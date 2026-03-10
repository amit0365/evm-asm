/-
  EvmAsm.Evm64.DivModSpec

  CPS specifications for the 256-bit EVM DIV and MOD programs (Knuth Algorithm D).
  Bottom-up decomposition starting from the simplest phases.
-/

import EvmAsm.Evm64.DivMod
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Zero path: b = 0, push 0. 5 instructions.
-- ============================================================================

/-- Zero path: advance sp by 32, store four zeros at the output location.
    Used when b = 0 (both DIV and MOD return 0). -/
theorem divK_zeroPath_spec (sp : Addr) (base : Addr)
    (m32 m40 m48 m56 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code :=
      (base ↦ᵢ .ADDI .x12 .x12 32) **
      ((base + 4) ↦ᵢ .SD .x12 .x0 0) **
      ((base + 8) ↦ᵢ .SD .x12 .x0 8) **
      ((base + 12) ↦ᵢ .SD .x12 .x0 16) **
      ((base + 16) ↦ᵢ .SD .x12 .x0 24)
    cpsTriple base (base + 20)
      (code **
       (.x12 ↦ᵣ sp) **
       ((sp + 32) ↦ₘ m32) ** ((sp + 40) ↦ₘ m40) **
       ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))
      (code **
       (.x12 ↦ᵣ (sp + 32)) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  have I0 := addi_spec_gen_same .x12 sp 32 base (by nofun)
  have I1 := sd_x0_spec_gen .x12 (sp + 32) m32 0 (base + 4) (by validMem)
  have I2 := sd_x0_spec_gen .x12 (sp + 32) m40 8 (base + 8) (by validMem)
  have I3 := sd_x0_spec_gen .x12 (sp + 32) m48 16 (base + 12) (by validMem)
  have I4 := sd_x0_spec_gen .x12 (sp + 32) m56 24 (base + 16) (by validMem)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Phase A body: OR-reduce b[0..3]. 7 instructions (straight-line).
-- Pre/post include BEQ instruction and x0 for branch composition.
-- ============================================================================

/-- Phase A body: load and OR-reduce the 4 limbs of b.
    Produces x5 = b0 ||| b1 ||| b2 ||| b3.
    The BEQ instruction at base+28 and x0 are preserved for branch composition. -/
theorem divK_phaseA_body_spec (sp : Addr) (base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code :=
      (base ↦ᵢ .LD .x5 .x12 32) **
      ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
      ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
      ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
      ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 28) ↦ᵢ .BEQ .x5 .x0 1016)
    cpsTriple base (base + 28)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 b0 32 base (by nofun) (by validMem)
  have I1 := ld_spec_gen .x10 .x12 sp v10 b1 40 (base + 4) (by nofun) (by validMem)
  have I2 := or_spec_gen_rd_eq_rs1 .x5 .x10 b0 b1 (base + 8) (by nofun) (by nofun)
  have I3 := ld_spec_gen .x10 .x12 sp b1 b2 48 (base + 12) (by nofun) (by validMem)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x10 (b0 ||| b1) b2 (base + 16) (by nofun) (by nofun)
  have I5 := ld_spec_gen .x10 .x12 sp b2 b3 56 (base + 20) (by nofun) (by validMem)
  have I6 := or_spec_gen_rd_eq_rs1 .x5 .x10 (b0 ||| b1 ||| b2) b3 (base + 24) (by nofun) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5 I6

-- ============================================================================
-- Phase A: full cpsBranch (body + BEQ)
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- Phase A: OR-reduce b then BEQ to zero path. -/
theorem divK_phaseA_spec (sp : Addr) (base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hvalid : ValidMemRange sp 8) :
    let bor := b0 ||| b1 ||| b2 ||| b3
    let code :=
      (base ↦ᵢ .LD .x5 .x12 32) **
      ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
      ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
      ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
      ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 28) ↦ᵢ .BEQ .x5 .x0 1016)
    let post :=
      code **
      (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ bor) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
      ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)
    cpsBranch base
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      -- Taken: bor = 0
      ((base + 28) + signExtend13 1016) post
      -- Not taken: bor ≠ 0
      (base + 32) post := by
  intro bor; intro code; intro post
  -- 1. Body: 7 straight-line instructions
  have hbody := divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid
  -- 2. BEQ: branch at base + 28, drop pure facts from postconditions
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 bor (0 : Word) (base + 28)
  have ha1 : (base + 28 : Addr) + 4 = base + 32 := by bv_omega
  have hbeq : cpsBranch (base + 28)
      (((base + 28) ↦ᵢ .BEQ .x5 .x0 1016) ** (.x5 ↦ᵣ bor) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 28) + signExtend13 1016)
        (((base + 28) ↦ᵢ .BEQ .x5 .x0 1016) ** (.x5 ↦ᵣ bor) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 32)
        (((base + 28) ↦ᵢ .BEQ .x5 .x0 1016) ** (.x5 ↦ᵣ bor) ** (.x0 ↦ᵣ (0 : Word))) := by
    rw [ha1] at hbeq_raw
    exact cpsBranch_consequence (base + 28) _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      hbeq_raw
  -- 3. Frame BEQ with body code, x12, x10, and memory
  have hbeq_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .LD .x5 .x12 32) **
     ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
     ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
     ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
     ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- 4. Compose body → branch with permutation
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- 5. Final permutation of postconditions
  exact cpsBranch_consequence _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

-- ============================================================================
-- Phase B init: zero out q[0..3] and u[5..7], load b[1] and b[2].
-- 9 straight-line instructions.
-- ============================================================================

/-- Phase B init part 1: zero scratch q[0..3] and u[5..7]. 7 instructions. -/
theorem divK_phaseB_init1_spec (sp : Addr) (base : Addr)
    (q0 q1 q2 q3 u5 u6 u7 : Word)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true) :
    let code :=
      (base ↦ᵢ .SD .x12 .x0 4088) **
      ((base + 4) ↦ᵢ .SD .x12 .x0 4080) **
      ((base + 8) ↦ᵢ .SD .x12 .x0 4072) **
      ((base + 12) ↦ᵢ .SD .x12 .x0 4064) **
      ((base + 16) ↦ᵢ .SD .x12 .x0 4016) **
      ((base + 20) ↦ᵢ .SD .x12 .x0 4008) **
      ((base + 24) ↦ᵢ .SD .x12 .x0 4000)
    cpsTriple base (base + 28)
      (code **
       (.x12 ↦ᵣ sp) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7))
      (code **
       (.x12 ↦ᵣ sp) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word))) := by
  have I0 := sd_x0_spec_gen .x12 sp q0 4088 base hv_q0
  have I1 := sd_x0_spec_gen .x12 sp q1 4080 (base + 4) hv_q1
  have I2 := sd_x0_spec_gen .x12 sp q2 4072 (base + 8) hv_q2
  have I3 := sd_x0_spec_gen .x12 sp q3 4064 (base + 12) hv_q3
  have I4 := sd_x0_spec_gen .x12 sp u5 4016 (base + 16) hv_u5
  have I5 := sd_x0_spec_gen .x12 sp u6 4008 (base + 20) hv_u6
  have I6 := sd_x0_spec_gen .x12 sp u7 4000 (base + 24) hv_u7
  runBlock I0 I1 I2 I3 I4 I5 I6

/-- Phase B init part 2: load b[1] and b[2]. 2 instructions. -/
theorem divK_phaseB_init2_spec (sp : Addr) (base : Addr)
    (b1 b2 : Word) (v6 v7 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code :=
      (base ↦ᵢ .LD .x6 .x12 40) **
      ((base + 4) ↦ᵢ .LD .x7 .x12 48)
    cpsTriple base (base + 8)
      (code **
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2))
      (code **
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2)) := by
  have I0 := ld_spec_gen .x6 .x12 sp v6 b1 40 base (by nofun) (by validMem)
  have I1 := ld_spec_gen .x7 .x12 sp v7 b2 48 (base + 4) (by nofun) (by validMem)
  runBlock I0 I1

-- ============================================================================
-- Phase C4: Copy a → u[0..4] unshifted (shift = 0). 9 instructions.
-- ============================================================================

/-- Copy a[0..3] to u[0..3] and set u[4] = 0 (no shift needed). -/
theorem divK_copyAU_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 u0 u1 u2 u3 u4 : Word) (v5 : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true) :
    let code :=
      (base ↦ᵢ .LD .x5 .x12 0) **
      ((base + 4) ↦ᵢ .SD .x12 .x5 4056) **
      ((base + 8) ↦ᵢ .LD .x5 .x12 8) **
      ((base + 12) ↦ᵢ .SD .x12 .x5 4048) **
      ((base + 16) ↦ᵢ .LD .x5 .x12 16) **
      ((base + 20) ↦ᵢ .SD .x12 .x5 4040) **
      ((base + 24) ↦ᵢ .LD .x5 .x12 24) **
      ((base + 28) ↦ᵢ .SD .x12 .x5 4032) **
      ((base + 32) ↦ᵢ .SD .x12 .x0 4024)
    cpsTriple base (base + 36)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
       ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word))) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 a0 0 base (by nofun) (by validMem)
  have I1 := sd_spec_gen .x12 .x5 sp a0 u0 4056 (base + 4) hv_u0
  have I2 := ld_spec_gen .x5 .x12 sp a0 a1 8 (base + 8) (by nofun) (by validMem)
  have I3 := sd_spec_gen .x12 .x5 sp a1 u1 4048 (base + 12) hv_u1
  have I4 := ld_spec_gen .x5 .x12 sp a1 a2 16 (base + 16) (by nofun) (by validMem)
  have I5 := sd_spec_gen .x12 .x5 sp a2 u2 4040 (base + 20) hv_u2
  have I6 := ld_spec_gen .x5 .x12 sp a2 a3 24 (base + 24) (by nofun) (by validMem)
  have I7 := sd_spec_gen .x12 .x5 sp a3 u3 4032 (base + 28) hv_u3
  have I8 := sd_x0_spec_gen .x12 sp u4 4024 (base + 32) hv_u4
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8

end EvmAsm.Rv64
