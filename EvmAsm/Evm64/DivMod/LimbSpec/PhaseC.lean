/-
  EvmAsm.Evm64.DivMod.LimbSpec.PhaseC

  Phase C: CopyAU, NormB, NormA, Phase C2, LoopSetup, CLZ (all stages).
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
-- Phase C4: Copy a → u[0..4] unshifted (shift = 0). 9 instructions.
-- ============================================================================

abbrev divK_copyAU_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_copyAU

/-- Copy a[0..3] to u[0..3] and set u[4] = 0 (no shift needed). -/
theorem divK_copyAU_spec (sp : Word) (base : Word)
    (a0 a1 a2 a3 u0 u1 u2 u3 u4 : Word) (v5 : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true) :
    let cr := divK_copyAU_code base
    cpsTriple base (base + 36) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4))
      (
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

-- ============================================================================
-- NormB: Normalize b in-place (shift > 0). 21 instructions.
-- Per-limb decomposition: 3 merge limbs (6 instr each) + 1 last limb (3 instr).
-- ============================================================================

def divK_normB_merge_prog (high_off low_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 high_off, .LD .x7 .x12 low_off, .SLL .x5 .x5 .x6,
   .SRL .x7 .x7 .x2, .OR .x5 .x5 .x7, .SD .x12 .x5 high_off]

abbrev divK_normB_merge_code (high_off low_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normB_merge_prog high_off low_off)

/-- NormB merge limb (6 instructions): LD high, LD low, SLL, SRL, OR, SD.
    Computes result = (high <<< shift) ||| (low >>> anti_shift) and stores to high_off.
    x6 = shift, x2 = anti_shift (= 64 - shift as unsigned). -/
theorem divK_normB_merge_spec (high_off low_off : BitVec 12)
    (sp high low v5 v7 shift anti_shift : Word) (base : Word)
    (hvalid_high : isValidDwordAccess (sp + signExtend12 high_off) = true)
    (hvalid_low : isValidDwordAccess (sp + signExtend12 low_off) = true) :
    let shifted_high := high <<< (shift.toNat % 64)
    let shifted_low := low >>> (anti_shift.toNat % 64)
    let result := shifted_high ||| shifted_low
    let cr := divK_normB_merge_code high_off low_off base
    cpsTriple base (base + 24) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 high_off) ↦ₘ high) **
       ((sp + signExtend12 low_off) ↦ₘ low))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ shifted_low) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 high_off) ↦ₘ result) **
       ((sp + signExtend12 low_off) ↦ₘ low)) := by
  intro shifted_high shifted_low result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 high high_off base (by nofun) hvalid_high
  have I1 := ld_spec_gen .x7 .x12 sp v7 low low_off (base + 4) (by nofun) hvalid_low
  have I2 := sll_spec_gen_rd_eq_rs1 .x5 .x6 high shift (base + 8) (by nofun)
  have I3 := srl_spec_gen_rd_eq_rs1 .x7 .x2 low anti_shift (base + 12) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x7 shifted_high shifted_low (base + 16) (by nofun)
  have I5 := sd_spec_gen .x12 .x5 sp result high high_off (base + 20) hvalid_high
  runBlock I0 I1 I2 I3 I4 I5

def divK_normB_last_prog (off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 off, .SLL .x5 .x5 .x6, .SD .x12 .x5 off]

abbrev divK_normB_last_code (off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normB_last_prog off)

/-- NormB last limb (3 instructions): LD, SLL, SD.
    Computes result = val <<< shift and stores to off. -/
theorem divK_normB_last_spec (off : BitVec 12)
    (sp val v5 shift : Word) (base : Word)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let result := val <<< (shift.toNat % 64)
    let cr := divK_normB_last_code off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ val))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ result)) := by
  intro result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 val off base (by nofun) hvalid
  have I1 := sll_spec_gen_rd_eq_rs1 .x5 .x6 val shift (base + 4) (by nofun)
  have I2 := sd_spec_gen .x12 .x5 sp result val off (base + 8) hvalid
  runBlock I0 I1 I2

-- ============================================================================
-- NormA: Normalize a → u[0..4] (shift > 0). 20 instructions (excl. JAL).
-- Per-limb decomposition: top (3 instr) + 3 merge (5 instr each) + last (2 instr).
-- ============================================================================

def divK_normA_top_prog (src_off dst_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 src_off, .SRL .x7 .x5 .x2, .SD .x12 .x7 dst_off]

abbrev divK_normA_top_code (src_off dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_top_prog src_off dst_off)

/-- NormA top: LD a[3], SRL to x7, SD u[4]. 3 instructions.
    Computes u[4] = a[3] >>> anti_shift (overflow bits from top limb). -/
theorem divK_normA_top_spec (src_off dst_off : BitVec 12)
    (sp val v5 v7 anti_shift dst_old : Word) (base : Word)
    (hvalid_src : isValidDwordAccess (sp + signExtend12 src_off) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let result := val >>> (anti_shift.toNat % 64)
    let cr := divK_normA_top_code src_off dst_off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 src_off) ↦ₘ val) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ val) ** (.x7 ↦ᵣ result) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 src_off) ↦ₘ val) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 val src_off base (by nofun) hvalid_src
  have I1 := srl_spec_gen .x7 .x5 .x2 v7 val anti_shift (base + 4) (by nofun)
  have I2 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 8) hvalid_dst
  runBlock I0 I1 I2

def divK_normA_mergeA_prog (next_off dst_off : BitVec 12) : List Instr :=
  [.LD .x7 .x12 next_off, .SLL .x5 .x5 .x6, .SRL .x10 .x7 .x2,
   .OR .x5 .x5 .x10, .SD .x12 .x5 dst_off]

abbrev divK_normA_mergeA_code (next_off dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_mergeA_prog next_off dst_off)

/-- NormA merge type A (5 instructions): x5 holds current limb.
    LD next into x7, SLL x5 by shift, SRL x10 from x7 by anti_shift, OR into x5, SD.
    Used for u[3] and u[1] computation. -/
theorem divK_normA_mergeA_spec (next_off dst_off : BitVec 12)
    (sp current next v7 v10 shift anti_shift dst_old : Word) (base : Word)
    (hvalid_next : isValidDwordAccess (sp + signExtend12 next_off) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let shifted_curr := current <<< (shift.toNat % 64)
    let shifted_next := next >>> (anti_shift.toNat % 64)
    let result := shifted_curr ||| shifted_next
    let cr := divK_normA_mergeA_code next_off dst_off base
    cpsTriple base (base + 20) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ current) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ next) ** (.x10 ↦ᵣ shifted_next) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro shifted_curr shifted_next result cr
  have I0 := ld_spec_gen .x7 .x12 sp v7 next next_off base (by nofun) hvalid_next
  have I1 := sll_spec_gen_rd_eq_rs1 .x5 .x6 current shift (base + 4) (by nofun)
  have I2 := srl_spec_gen .x10 .x7 .x2 v10 next anti_shift (base + 8) (by nofun)
  have I3 := or_spec_gen_rd_eq_rs1 .x5 .x10 shifted_curr shifted_next (base + 12) (by nofun)
  have I4 := sd_spec_gen .x12 .x5 sp result dst_old dst_off (base + 16) hvalid_dst
  runBlock I0 I1 I2 I3 I4

def divK_normA_mergeB_prog (next_off dst_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 next_off, .SLL .x7 .x7 .x6, .SRL .x10 .x5 .x2,
   .OR .x7 .x7 .x10, .SD .x12 .x7 dst_off]

abbrev divK_normA_mergeB_code (next_off dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_mergeB_prog next_off dst_off)

/-- NormA merge type B (5 instructions): x7 holds current limb.
    LD next into x5, SLL x7 by shift, SRL x10 from x5 by anti_shift, OR into x7, SD.
    Used for u[2] computation. -/
theorem divK_normA_mergeB_spec (next_off dst_off : BitVec 12)
    (sp current next v5 v10 shift anti_shift dst_old : Word) (base : Word)
    (hvalid_next : isValidDwordAccess (sp + signExtend12 next_off) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let shifted_curr := current <<< (shift.toNat % 64)
    let shifted_next := next >>> (anti_shift.toNat % 64)
    let result := shifted_curr ||| shifted_next
    let cr := divK_normA_mergeB_code next_off dst_off base
    cpsTriple base (base + 20) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ current) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ next) ** (.x7 ↦ᵣ result) ** (.x10 ↦ᵣ shifted_next) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro shifted_curr shifted_next result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 next next_off base (by nofun) hvalid_next
  have I1 := sll_spec_gen_rd_eq_rs1 .x7 .x6 current shift (base + 4) (by nofun)
  have I2 := srl_spec_gen .x10 .x5 .x2 v10 next anti_shift (base + 8) (by nofun)
  have I3 := or_spec_gen_rd_eq_rs1 .x7 .x10 shifted_curr shifted_next (base + 12) (by nofun)
  have I4 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 16) hvalid_dst
  runBlock I0 I1 I2 I3 I4

def divK_normA_last_prog (dst_off : BitVec 12) : List Instr :=
  [.SLL .x7 .x7 .x6, .SD .x12 .x7 dst_off]

abbrev divK_normA_last_code (dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_last_prog dst_off)

/-- NormA last limb (2 instructions): SLL x7 by shift, SD to dst_off.
    Computes u[0] = a[0] <<< shift. -/
theorem divK_normA_last_spec (dst_off : BitVec 12)
    (sp val shift dst_old : Word) (base : Word)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let result := val <<< (shift.toNat % 64)
    let cr := divK_normA_last_code dst_off base
    cpsTriple base (base + 8) cr
      (
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ val) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro result cr
  have I0 := sll_spec_gen_rd_eq_rs1 .x7 .x6 val shift base (by nofun)
  have I1 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 4) hvalid_dst
  runBlock I0 I1

-- ============================================================================
-- Phase C2 body: store shift, compute anti_shift. 3 instructions.
-- ============================================================================

abbrev divK_phaseC2_code (shift0_off : BitVec 13) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseC2 shift0_off)

/-- Phase C2 body: SD shift to scratch, ADDI x2 = 0, SUB x2 = -shift.
    Preserves x6 and x0 for the subsequent BEQ.
    The postcondition uses `signExtend12 (0 : BitVec 12) - shift` (= 0 - shift)
    to match the syntactic form produced by addi_x0_spec_gen + sub_spec_gen. -/
theorem divK_phaseC2_body_spec (sp shift v2 shift_mem : Word)
    (shift0_off : BitVec 13) (base : Word)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true) :
    let cr := divK_phaseC2_code shift0_off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  intro cr
  have I0 := sd_spec_gen .x12 .x6 sp shift shift_mem 3992 base hv_shift
  have I1 := addi_x0_spec_gen .x2 v2 0 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x2 .x6
    (signExtend12 (0 : BitVec 12)) shift (base + 8) (by nofun)
  runBlock I0 I1 I2

-- ============================================================================
-- Phase C2 full: body + BEQ (shift = 0 branch). cpsBranch.
-- ============================================================================

set_option maxRecDepth 1024 in
/-- Phase C2: store shift, compute anti_shift, BEQ if shift=0.
    Taken: shift = 0, skip normalization.
    Not taken: shift ≠ 0, proceed to normalize.
    anti_shift = signExtend12 0 - shift (= 0 - shift = negation of shift amount). -/
theorem divK_phaseC2_spec (sp shift v2 shift_mem : Word)
    (shift0_off : BitVec 13) (base : Word)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true) :
    let cr := divK_phaseC2_code shift0_off base
    let post :=
      (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) **
      (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + signExtend12 3992) ↦ₘ shift)
    cpsBranch base cr
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      -- Taken: shift = 0
      ((base + 12) + signExtend13 shift0_off) post
      -- Not taken: shift ≠ 0
      (base + 16) post := by
  intro cr post
  have hbody := divK_phaseC2_body_spec sp shift v2 shift_mem shift0_off base hv_shift
  have hbeq_raw := beq_spec_gen .x6 .x0 shift0_off shift (0 : Word) (base + 12)
  have ha1 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  rw [ha1] at hbeq_raw
  have hbeq : cpsBranch (base + 12) _
      ((.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 12) + signExtend13 shift0_off)
        ((.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 16)
        ((.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      hbeq_raw
  have hbeq_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hbeq_ext := cpsBranch_extend_code (cr' := cr) (fun a i h => by
    simp only [CodeReq.singleton] at h
    split at h
    · next heq =>
      rw [beq_iff_eq] at heq; subst heq
      simp only [Option.some.injEq] at h; subst h
      show divK_phaseC2_code shift0_off base (base + 12) = _
      have hlen : (divK_phaseC2 shift0_off).length = 4 := by
        unfold divK_phaseC2 SD ADDI single seq; rfl
      exact CodeReq.ofProg_lookup base (divK_phaseC2 shift0_off) 3
        (by omega) (by omega)
    · simp at h) hbeq_framed
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_ext
  exact cpsBranch_consequence _ _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed
-- ============================================================================
-- Loop setup: LD n, compute m = 4 - n, BLT to skip loop.
-- 4 instructions: LD, ADDI, SUB, BLT. cpsBranch.
-- ============================================================================

abbrev divK_loopSetup_code (blt_off : BitVec 13) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_loopSetup blt_off)

/-- Loop setup body: load n, compute m = 4 - n. 3 straight-line instructions.
    Uses signExtend12 4 directly to match addi_x0_spec_gen + sub_spec_gen output. -/
theorem divK_loopSetup_body_spec (sp n v1 v5 : Word)
    (blt_off : BitVec 13) (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true) :
    let cr := divK_loopSetup_code blt_off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
       (.x1 ↦ᵣ (signExtend12 (4 : BitVec 12) - n)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n)) := by
  intro cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 n 3984 base (by nofun) hv_n
  have I1 := addi_x0_spec_gen .x1 v1 4 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x1 .x5
    (signExtend12 (4 : BitVec 12)) n (base + 8) (by nofun)
  runBlock I0 I1 I2

/-- Loop setup: load n, compute m = 4-n, BLT if m < 0 (skip loop).
    Taken: m < 0 (n > 4, impossible in practice but handled).
    Not taken: m >= 0, proceed to loop. -/
theorem divK_loopSetup_spec (sp n v1 v5 : Word)
    (blt_off : BitVec 13) (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true) :
    let m := signExtend12 (4 : BitVec 12) - n
    let cr := divK_loopSetup_code blt_off base
    let post :=
      (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + signExtend12 3984) ↦ₘ n)
    cpsBranch base cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      -- Taken: m < 0 (signed)
      ((base + 12) + signExtend13 blt_off) post
      -- Not taken: m >= 0
      (base + 16) post := by
  intro m cr post
  have hbody := divK_loopSetup_body_spec sp n v1 v5 blt_off base hv_n
  have hblt_raw := blt_spec_gen .x1 .x0 blt_off m (0 : Word) (base + 12)
  have ha1 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  rw [ha1] at hblt_raw
  have hblt : cpsBranch (base + 12) _
      ((.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 12) + signExtend13 blt_off)
        ((.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 16)
        ((.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      hblt_raw
  have hblt_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
     ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblt
  have hblt_ext := cpsBranch_extend_code (cr' := cr) (fun a i h => by
    simp only [CodeReq.singleton] at h
    split at h
    · next heq =>
      rw [beq_iff_eq] at heq; subst heq
      simp only [Option.some.injEq] at h; subst h
      show divK_loopSetup_code blt_off base (base + 12) = _
      have hlen : (divK_loopSetup blt_off).length = 4 := by
        unfold divK_loopSetup LD ADDI single seq; rfl
      exact CodeReq.ofProg_lookup base (divK_loopSetup blt_off) 3
        (by omega) (by omega)
    · simp at h) hblt_framed
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hblt_ext
  exact cpsBranch_consequence _ _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed
-- ============================================================================
-- CLZ init: ADDI x6 x0 0. 1 instruction.
-- ============================================================================

/-- CLZ init: set x6 = 0 (count register). -/
theorem divK_clz_init_spec (v6 : Word) (base : Word) :
    let cr := CodeReq.singleton base (.ADDI .x6 .x0 0)
    cpsTriple base (base + 4) cr
      ((.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ signExtend12 (0 : BitVec 12)) **
       (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  have I0 := addi_x0_spec_gen .x6 v6 0 base (by nofun)
  runBlock I0
-- ============================================================================
-- CLZ per-stage specs: SRLI x7 x5 K + BNE x7 x0 12 + SLLI x5 x5 M + ADDI x6 x6 M.
-- Two specs per stage: taken (shifted ≠ 0) and not-taken (shifted = 0).
-- Uses cpsBranch_elim_taken/ntaken to extract deterministic paths.
-- K : BitVec 6 (SRLI shamt), M_s : BitVec 6 (SLLI shamt), M_a : BitVec 12 (ADDI imm).
-- ============================================================================

def divK_clz_stage_prog (K M_s : BitVec 6) (M_a : BitVec 12) : List Instr :=
  [.SRLI .x7 .x5 K, .BNE .x7 .x0 12, .SLLI .x5 .x5 M_s, .ADDI .x6 .x6 M_a]

abbrev divK_clz_stage_code (K M_s : BitVec 6) (M_a : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_clz_stage_prog K M_s M_a)

/-- CLZ stage, taken branch: val >>> K ≠ 0, skip SLLI+ADDI.
    x5 = val (unchanged), x6 = count (unchanged), x7 = val >>> K. -/
theorem divK_clz_stage_taken_spec (K M_s : BitVec 6) (M_a : BitVec 12) (val count v7 : Word)
    (base : Word)
    (hne : val >>> K.toNat ≠ 0) :
    let cr := divK_clz_stage_code K M_s M_a base
    cpsTriple base (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) **
              (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  -- 1. SRLI body
  have I0 := srli_spec_gen .x7 .x5 v7 val K base (by nofun)
  -- 2. BNE at base+4: taken → base+16
  have hbne_raw := bne_spec_gen .x7 .x0 (12 : BitVec 13) (val >>> K.toNat) (0 : Word) (base + 4)
  have hsig : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  -- 3. Frame BNE with x5, x6
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  -- 4. Extend to full cr
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 16)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_stage_code K M_s M_a base (base + 4) = _
        simp only [divK_clz_stage_code, divK_clz_stage_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  -- 5. SRLI body
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  -- 6. Compose SRLI → BNE
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  -- 7. Eliminate not-taken path (contradicts hne)
  have taken := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
    exact hne ((sepConj_pure_right _ _ _).1 h_x0p).2)
  -- 8. Strip pure fact from taken postcondition, then permute
  -- taken postcondition: ((x7 ** x0 ** pure) ** (x5 ** x6))
  -- target postcondition: (x5 ** x6 ** x7 ** x0)
  -- Need intermediate: first strip pure, then xperm
  -- Use direct definition to avoid lambda wrapping
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := taken R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp') hp hpq⟩⟩
/-- CLZ stage, not-taken branch: val >>> K = 0, execute SLLI+ADDI.
    x5 = val <<< M, x6 = count + signExtend12 M, x7 = 0. -/
theorem divK_clz_stage_ntaken_spec (K M_s : BitVec 6) (M_a : BitVec 12) (val count v7 : Word)
    (base : Word)
    (heq : val >>> K.toNat = 0) :
    let cr := divK_clz_stage_code K M_s M_a base
    cpsTriple base (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (val <<< M_s.toNat)) ** (.x6 ↦ᵣ (count + signExtend12 M_a)) **
              (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  -- 1. SRLI body
  have I0 := srli_spec_gen .x7 .x5 v7 val K base (by nofun)
  -- 2. BNE at base+4
  have hbne_raw := bne_spec_gen .x7 .x0 (12 : BitVec 13) (val >>> K.toNat) (0 : Word) (base + 4)
  have hsig : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  -- 3. Frame BNE with x5, x6
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  -- 4. Extend BNE to full cr
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 16)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_stage_code K M_s M_a base (base + 4) = _
        simp only [divK_clz_stage_code, divK_clz_stage_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  -- 5. SRLI body
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  -- 6. Compose SRLI → BNE
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  -- 7. Eliminate taken path (contradicts heq)
  have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
    exact ((sepConj_pure_right _ _ _).1 h_x0p).2 (by rw [heq]))
  -- 8. SLLI + ADDI from base+8 to base+16
  have I1 := slli_spec_gen_same .x5 val M_s (base + 8) (by nofun)
  have I2 := addi_spec_gen_same .x6 count M_a (base + 12) (by nofun)
  have hslli_addi : cpsTriple (base + 8) (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
      ((.x5 ↦ᵣ (val <<< M_s.toNat)) ** (.x6 ↦ᵣ (count + signExtend12 M_a))) := by
    runBlock I1 I2
  have hframed := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hslli_addi
  -- 9. Strip pure from ntaken, compose with SLLI+ADDI
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp')
    ntaken hframed
  -- 10. Final permutation + rewrite x7 = 0
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => hp)
    (fun h hp => by rw [heq] at hp; xperm_hyp hp)
    full
-- ============================================================================
-- CLZ last stage (stage 5): SRLI x7 x5 63 + BNE(8) + ADDI x6 x6 1
-- 3 instructions. BNE offset = 8 (not 12), no SLLI.
-- ============================================================================

def divK_clz_last_prog : List Instr :=
  [.SRLI .x7 .x5 63, .BNE .x7 .x0 8, .ADDI .x6 .x6 1]

abbrev divK_clz_last_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_clz_last_prog

/-- CLZ last stage, taken: val >>> 63 ≠ 0 (MSB is 1), skip ADDI.
    x5 unchanged, x6 unchanged, x7 = val >>> 63. -/
theorem divK_clz_last_taken_spec (val count v7 : Word) (base : Word)
    (hne : val >>> 63 ≠ 0) :
    let cr := divK_clz_last_code base
    cpsTriple base (base + 12) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) **
              (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  have I0 := srli_spec_gen .x7 .x5 v7 val 63 base (by nofun)
  have h63 : (63 : BitVec 6).toNat = 63 := by decide
  simp only [h63] at I0
  have hbne_raw := bne_spec_gen .x7 .x0 (8 : BitVec 13) (val >>> 63) (0 : Word) (base + 4)
  have hsig : signExtend13 (8 : BitVec 13) = (8 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (8 : BitVec 13) = base + 12 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 12)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_last_code base (base + 4) = _
        simp only [divK_clz_last_code, divK_clz_last_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  have taken := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
    exact hne ((sepConj_pure_right _ _ _).1 h_x0p).2)
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := taken R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp') hp hpq⟩⟩
/-- CLZ last stage, ntaken: val >>> 63 = 0, execute ADDI.
    x5 unchanged, x6 = count + 1, x7 = 0. -/
theorem divK_clz_last_ntaken_spec (val count v7 : Word) (base : Word)
    (heq : val >>> 63 = 0) :
    let cr := divK_clz_last_code base
    cpsTriple base (base + 12) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ (count + signExtend12 (1 : BitVec 12))) **
              (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  have I0 := srli_spec_gen .x7 .x5 v7 val 63 base (by nofun)
  have h63 : (63 : BitVec 6).toNat = 63 := by decide
  simp only [h63] at I0
  have hbne_raw := bne_spec_gen .x7 .x0 (8 : BitVec 13) (val >>> 63) (0 : Word) (base + 4)
  have hsig : signExtend13 (8 : BitVec 13) = (8 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (8 : BitVec 13) = base + 12 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 12)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_last_code base (base + 4) = _
        simp only [divK_clz_last_code, divK_clz_last_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  -- Eliminate taken path (contradicts heq)
  have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
    exact ((sepConj_pure_right _ _ _).1 h_x0p).2 (by rw [heq]))
  -- ADDI from base+8 to base+12
  have I2 := addi_spec_gen_same .x6 count 1 (base + 8) (by nofun)
  have haddi : cpsTriple (base + 8) (base + 12) cr
      (.x6 ↦ᵣ count)
      (.x6 ↦ᵣ (count + signExtend12 (1 : BitVec 12))) := by
    runBlock I2
  have hframed := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) haddi
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp')
    ntaken hframed
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => hp)
    (fun h hp => by rw [heq] at hp; xperm_hyp hp)
    full

end EvmAsm.Evm64
