/-
  EvmAsm.Evm64.DivMod.LimbSpec.PerLimb

  Per-limb basic helpers: zero path, denorm body, epilogue copy.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Zero path: b = 0, push 0. 5 instructions.
-- ============================================================================

abbrev divK_zeroPath_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_zeroPath

/-- Zero path: advance sp by 32, store four zeros at the output location.
    Used when b = 0 (both DIV and MOD return 0). -/
theorem divK_zeroPath_spec (sp : Word) (base : Word)
    (m32 m40 m48 m56 : Word)
    (hvalid : ValidMemRange sp 8) :
    let cr := divK_zeroPath_code base
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) **
       ((sp + 32) ↦ₘ m32) ** ((sp + 40) ↦ₘ m40) **
       ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))
      ((.x12 ↦ᵣ (sp + 32)) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  have I0 := addi_spec_gen_same .x12 sp 32 base (by nofun)
  have I1 := sd_x0_spec_gen .x12 (sp + 32) m32 0 (base + 4) (by validMem)
  have I2 := sd_x0_spec_gen .x12 (sp + 32) m40 8 (base + 8) (by validMem)
  have I3 := sd_x0_spec_gen .x12 (sp + 32) m48 16 (base + 12) (by validMem)
  have I4 := sd_x0_spec_gen .x12 (sp + 32) m56 24 (base + 16) (by validMem)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Denorm: De-normalize remainder. Per-limb specs for the shift body.
-- Same structure as NormB but SRL/SLL swapped (right-shift with merge from above).
-- ============================================================================

def divK_denorm_merge_prog (curr_off next_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 curr_off, .LD .x7 .x12 next_off, .SRL .x5 .x5 .x6,
   .SLL .x7 .x7 .x2, .OR .x5 .x5 .x7, .SD .x12 .x5 curr_off]

abbrev divK_denorm_merge_code (curr_off next_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_denorm_merge_prog curr_off next_off)

/-- Denorm merge limb (6 instructions): LD curr, LD next, SRL, SLL, OR, SD.
    Computes result = (curr >>> shift) ||| (next <<< anti_shift) and stores to curr_off.
    x6 = shift, x2 = anti_shift. -/
theorem divK_denorm_merge_spec (curr_off next_off : BitVec 12)
    (sp curr next v5 v7 shift anti_shift : Word) (base : Word)
    (hvalid_curr : isValidDwordAccess (sp + signExtend12 curr_off) = true)
    (hvalid_next : isValidDwordAccess (sp + signExtend12 next_off) = true) :
    let shifted_curr := curr >>> (shift.toNat % 64)
    let shifted_next := next <<< (anti_shift.toNat % 64)
    let result := shifted_curr ||| shifted_next
    let cr := divK_denorm_merge_code curr_off next_off base
    cpsTriple base (base + 24) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 curr_off) ↦ₘ curr) **
       ((sp + signExtend12 next_off) ↦ₘ next))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ shifted_next) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 curr_off) ↦ₘ result) **
       ((sp + signExtend12 next_off) ↦ₘ next)) := by
  intro shifted_curr shifted_next result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 curr curr_off base (by nofun) hvalid_curr
  have I1 := ld_spec_gen .x7 .x12 sp v7 next next_off (base + 4) (by nofun) hvalid_next
  have I2 := srl_spec_gen_rd_eq_rs1 .x5 .x6 curr shift (base + 8) (by nofun)
  have I3 := sll_spec_gen_rd_eq_rs1 .x7 .x2 next anti_shift (base + 12) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x7 shifted_curr shifted_next (base + 16) (by nofun)
  have I5 := sd_spec_gen .x12 .x5 sp result curr curr_off (base + 20) hvalid_curr
  runBlock I0 I1 I2 I3 I4 I5

def divK_denorm_last_prog (off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 off, .SRL .x5 .x5 .x6, .SD .x12 .x5 off]

abbrev divK_denorm_last_code (off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_denorm_last_prog off)

/-- Denorm last limb (3 instructions): LD, SRL, SD.
    Computes result = val >>> shift and stores to off. -/
theorem divK_denorm_last_spec (off : BitVec 12)
    (sp val v5 shift : Word) (base : Word)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let result := val >>> (shift.toNat % 64)
    let cr := divK_denorm_last_code off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ val))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ result)) := by
  intro result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 val off base (by nofun) hvalid
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 val shift (base + 4) (by nofun)
  have I2 := sd_spec_gen .x12 .x5 sp result val off (base + 8) hvalid
  runBlock I0 I1 I2

-- ============================================================================
-- Epilogue: Copy q[0..3] or u[0..3] to output. 10 instructions each.
-- Split into load phase (4 LD) + store phase (ADDI + 4 SD) + JAL.
-- ============================================================================

def divK_epilogue_load_prog (off0 off1 off2 off3 : BitVec 12) : List Instr :=
  [.LD .x5 .x12 off0, .LD .x6 .x12 off1, .LD .x7 .x12 off2, .LD .x10 .x12 off3]

abbrev divK_epilogue_load_code (off0 off1 off2 off3 : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_epilogue_load_prog off0 off1 off2 off3)

/-- Epilogue load phase: load 4 values from scratch space. 4 instructions.
    Loads q[0..3] (for DIV) or u[0..3] (for MOD) into x5, x6, x7, x10. -/
theorem divK_epilogue_load_spec (off0 off1 off2 off3 : BitVec 12)
    (sp r0 r1 r2 r3 v5 v6 v7 v10 : Word) (base : Word)
    (hv0 : isValidDwordAccess (sp + signExtend12 off0) = true)
    (hv1 : isValidDwordAccess (sp + signExtend12 off1) = true)
    (hv2 : isValidDwordAccess (sp + signExtend12 off2) = true)
    (hv3 : isValidDwordAccess (sp + signExtend12 off3) = true) :
    let cr := divK_epilogue_load_code off0 off1 off2 off3 base
    cpsTriple base (base + 16) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 off0) ↦ₘ r0) ** ((sp + signExtend12 off1) ↦ₘ r1) **
       ((sp + signExtend12 off2) ↦ₘ r2) ** ((sp + signExtend12 off3) ↦ₘ r3))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) ** (.x10 ↦ᵣ r3) **
       ((sp + signExtend12 off0) ↦ₘ r0) ** ((sp + signExtend12 off1) ↦ₘ r1) **
       ((sp + signExtend12 off2) ↦ₘ r2) ** ((sp + signExtend12 off3) ↦ₘ r3)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 r0 off0 base (by nofun) hv0
  have I1 := ld_spec_gen .x6 .x12 sp v6 r1 off1 (base + 4) (by nofun) hv1
  have I2 := ld_spec_gen .x7 .x12 sp v7 r2 off2 (base + 8) (by nofun) hv2
  have I3 := ld_spec_gen .x10 .x12 sp v10 r3 off3 (base + 12) (by nofun) hv3
  runBlock I0 I1 I2 I3

def divK_epilogue_store_prog (jal_off : BitVec 21) : List Instr :=
  [.ADDI .x12 .x12 32, .SD .x12 .x5 0, .SD .x12 .x6 8,
   .SD .x12 .x7 16, .SD .x12 .x10 24, .JAL .x0 jal_off]

abbrev divK_epilogue_store_code (jal_off : BitVec 21) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_epilogue_store_prog jal_off)

/-- Epilogue store phase: ADDI sp+32, store 4 values, JAL to exit. 6 instructions. -/
theorem divK_epilogue_store_spec (sp : Word) (base : Word)
    (r0 r1 r2 r3 m0 m8 m16 m24 : Word) (jal_off : BitVec 21)
    (hvalid : ValidMemRange sp 8) :
    let cr := divK_epilogue_store_code jal_off base
    cpsTriple base (base + 20 + signExtend21 jal_off) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) ** (.x10 ↦ᵣ r3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (
       (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) ** (.x10 ↦ᵣ r3) **
       ((sp + 32) ↦ₘ r0) ** ((sp + 40) ↦ₘ r1) **
       ((sp + 48) ↦ₘ r2) ** ((sp + 56) ↦ₘ r3)) := by
  have I0 := addi_spec_gen_same .x12 sp 32 base (by nofun)
  have I1 := sd_spec_gen .x12 .x5 (sp + 32) r0 m0 0 (base + 4) (by validMem)
  have I2 := sd_spec_gen .x12 .x6 (sp + 32) r1 m8 8 (base + 8) (by validMem)
  have I3 := sd_spec_gen .x12 .x7 (sp + 32) r2 m16 16 (base + 12) (by validMem)
  have I4 := sd_spec_gen .x12 .x10 (sp + 32) r3 m24 24 (base + 16) (by validMem)
  have I5 := jal_x0_spec_gen jal_off (base + 20)
  runBlock I0 I1 I2 I3 I4 I5

end EvmAsm.Evm64
