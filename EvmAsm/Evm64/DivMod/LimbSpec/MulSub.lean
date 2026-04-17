/-
  EvmAsm.Evm64.DivMod.LimbSpec.MulSub

  Mul-sub building blocks (partA/partB), sub-carry, setup, save-j, and the composed mulsub_limb spec.
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
-- Mul-sub limb: 11 instructions, core of the loop body.
-- q_hat * v[i] + carry_in, subtract from u[j+i].
-- ============================================================================

/-- Mul-sub limb Part A: LD v[i], MUL, MULHU, ADD, SLTU, ADD.
    6 instructions. Produces full_sub (x7) and partial_carry (x10). -/
theorem divK_mulsub_partA_spec (sp q_hat carry_in v5_old v7_old v_i : Word)
    (v_off : BitVec 12) (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 v_off) = true) :
    let prod_lo := q_hat * v_i
    let prod_hi := rv64_mulhu q_hat v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let partial_carry := borrow_add + prod_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.MULHU .x5 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x7 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x10 .x7 .x10))
       (CodeReq.singleton (base + 20) (.ADD .x10 .x10 .x5))))))
    cpsTriple base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ partial_carry) **
       (.x5 ↦ᵣ prod_hi) ** (.x7 ↦ᵣ full_sub) **
       ((sp + signExtend12 v_off) ↦ₘ v_i)) := by
  intro prod_lo prod_hi full_sub borrow_add partial_carry cr
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun) hv
  have I1 := mul_spec_gen .x7 .x11 .x5 v7_old q_hat v_i (base + 4) (by nofun)
  have I2 := mulhu_spec_gen_rd_eq_rs2 .x5 .x11 q_hat v_i (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x7 .x10 prod_lo carry_in (base + 12) (by nofun)
  have I4 := sltu_spec_gen_rd_eq_rs2 .x10 .x7 full_sub carry_in (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1 .x10 .x5 borrow_add prod_hi (base + 20) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5

/-- Mul-sub limb Part B: LD u[j+i], SLTU, SUB, ADD, SD.
    5 instructions. Produces carry_out (x10) and stores u_new. -/
theorem divK_mulsub_partB_spec (u_base partial_carry prod_hi full_sub v2_old u_i : Word)
    (u_off : BitVec 12) (base : Word)
    (hv : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    let u_new := u_i - full_sub
    let carry_out := partial_carry + borrow_sub
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x5 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x10 .x10 .x5))
       (CodeReq.singleton (base + 16) (.SD .x6 .x2 u_off)))))
    cpsTriple base (base + 20) cr
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ partial_carry) **
       (.x5 ↦ᵣ prod_hi) ** (.x7 ↦ᵣ full_sub) ** (.x2 ↦ᵣ v2_old) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ borrow_sub) ** (.x7 ↦ᵣ full_sub) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro borrow_sub u_new carry_out cr
  have I0 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off base (by nofun) hv
  have I1 := sltu_spec_gen .x5 .x2 .x7 prod_hi u_i full_sub (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x2 .x7 u_i full_sub (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x10 .x5 partial_carry borrow_sub (base + 12) (by nofun)
  have I4 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 16) hv
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Subtract carry from u[j+4]: 4 instructions after mul-sub limbs.
-- ============================================================================

/-- Subtract carry from u[j+4].
    4 instructions: LD, SLTU, SUB, SD. Produces borrow (x7). -/
theorem divK_sub_carry_spec (u_base carry_in v5_old v7_old u_top : Word)
    (u_off : BitVec 12) (base : Word)
    (hv : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let borrow := if BitVec.ult u_top carry_in then (1 : Word) else 0
    let u_new := u_top - carry_in
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x7 .x5 .x10))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x5 .x5 .x10))
       (CodeReq.singleton (base + 12) (.SD .x6 .x5 u_off))))
    cpsTriple base (base + 16) cr
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       ((u_base + signExtend12 u_off) ↦ₘ u_top))
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ u_new) ** (.x7 ↦ᵣ borrow) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro borrow u_new cr
  have I0 := ld_spec_gen .x5 .x6 u_base v5_old u_top u_off base (by nofun) hv
  have I1 := sltu_spec_gen .x7 .x5 .x10 v7_old u_top carry_in (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x5 .x10 u_top carry_in (base + 8) (by nofun)
  have I3 := sd_spec_gen .x6 .x5 u_base u_new u_top u_off (base + 12) hv
  runBlock I0 I1 I2 I3

-- ============================================================================
-- Mul-sub setup: restore j, compute u_base = &u[j], init carry = 0.
-- 5 instructions: LD + SLLI + ADDI + SUB + ADDI.
-- ============================================================================

/-- Mul-sub setup: restore j from scratch, compute u_base, zero carry. -/
theorem divK_mulsub_setup_spec (sp q_hat j v1_old v5_old v6_old v10_old : Word)
    (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 3976) = true) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let sp_m40 := sp + signExtend12 4056
    let u_base := sp_m40 - j_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3976))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x6 .x12 4056))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x6 .x6 .x5))
       (CodeReq.singleton (base + 16) (.ADDI .x10 .x0 0)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x1 ↦ᵣ v1_old) ** (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x10 ↦ᵣ v10_old) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ j_x8) ** (.x6 ↦ᵣ u_base) **
       (.x10 ↦ᵣ signExtend12 0) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j)) := by
  intro j_x8 sp_m40 u_base cr
  have I0 := ld_spec_gen .x1 .x12 sp v1_old j 3976 base (by nofun) hv
  have I1 := slli_spec_gen .x5 .x1 v5_old j 3 (base + 4) (by nofun)
  have I2 := addi_spec_gen .x6 .x12 v6_old sp 4056 (base + 8) (by nofun)
  have I3 := sub_spec_gen_rd_eq_rs1 .x6 .x5 sp_m40 j_x8 (base + 12) (by nofun)
  have I4 := addi_x0_spec_gen .x10 v10_old 0 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Save j: 1 instruction SD.
-- ============================================================================

/-- Save j to scratch memory. -/
theorem divK_save_j_spec (sp j j_old : Word) (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 3976) = true) :
    let cr := CodeReq.singleton base (.SD .x12 .x1 3976)
    cpsTriple base (base + 4) cr
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) ** (sp + signExtend12 3976 ↦ₘ j_old))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) ** (sp + signExtend12 3976 ↦ₘ j)) := by
  intro cr
  have I0 := sd_spec_gen .x12 .x1 sp j j_old 3976 base hv
  runBlock I0

-- ============================================================================
-- Composed per-limb specs: mulsub_limb, addback_limb.
-- These compose partA+partB into single per-limb operations.
-- ============================================================================

set_option maxRecDepth 2048 in
/-- Mul-sub full limb: partA (6 instrs) + partB (5 instrs) = 11 instructions.
    Input: q_hat (x11), carry_in (x10), v[i] and u[j+i] in memory.
    Output: carry_out (x10), u_new stored. -/
theorem divK_mulsub_limb_spec
    (sp u_base q_hat carry_in v5_old v7_old v2_old v_i u_i : Word)
    (v_off u_off : BitVec 12) (base : Word)
    (hv_v : isValidDwordAccess (sp + signExtend12 v_off) = true)
    (hv_u : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let prod_lo := q_hat * v_i
    let prod_hi := rv64_mulhu q_hat v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let partial_carry := borrow_add + prod_hi
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    let u_new := u_i - full_sub
    let carry_out := partial_carry + borrow_sub
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.MULHU .x5 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x7 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x10 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADD .x10 .x10 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SLTU .x5 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SUB .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 36) (.ADD .x10 .x10 .x5))
       (CodeReq.singleton (base + 40) (.SD .x6 .x2 u_off)))))))))))
    cpsTriple base (base + 44) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_in) **
       (.x6 ↦ᵣ u_base) ** (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_out) **
       (.x6 ↦ᵣ u_base) ** (.x5 ↦ᵣ borrow_sub) ** (.x7 ↦ᵣ full_sub) **
       (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro prod_lo prod_hi full_sub borrow_add partial_carry borrow_sub u_new carry_out cr
  -- Instructions from partA (6 instrs at base)
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun) hv_v
  have I1 := mul_spec_gen .x7 .x11 .x5 v7_old q_hat v_i (base + 4) (by nofun)
  have I2 := mulhu_spec_gen_rd_eq_rs2 .x5 .x11 q_hat v_i (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x7 .x10 prod_lo carry_in (base + 12) (by nofun)
  have I4 := sltu_spec_gen_rd_eq_rs2 .x10 .x7 full_sub carry_in (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1 .x10 .x5 borrow_add prod_hi (base + 20) (by nofun)
  -- Instructions from partB (5 instrs at base+24)
  have I6 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 24) (by nofun) hv_u
  have I7 := sltu_spec_gen .x5 .x2 .x7 prod_hi u_i full_sub (base + 28) (by nofun)
  have I8 := sub_spec_gen_rd_eq_rs1 .x2 .x7 u_i full_sub (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1 .x10 .x5 partial_carry borrow_sub (base + 36) (by nofun)
  have I10 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 40) hv_u
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10

end EvmAsm.Evm64
