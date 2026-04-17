/-
  EvmAsm.Evm64.DivMod.LimbSpec.Addback

  Add-back correction building blocks (partA/partB, finalization, carry init, correction branch) and the composed addback_limb spec.
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
-- Add-back correction limb: 8 instructions per limb.
-- u[j+i] += v[i] + carry_in, with carry propagation.
-- ============================================================================

/-- Add-back Part A: LD v[i], LD u[j+i], ADD carry, SLTU carry1, ADD v[i].
    5 instructions. Produces sum (x2) and carry1 (x7). -/
theorem divK_addback_partA_spec (sp u_base carry_in v5_old v2_old v_i u_i : Word)
    (v_off : BitVec 12) (u_off : BitVec 12) (base : Word)
    (hv_v : isValidDwordAccess (sp + signExtend12 v_off) = true)
    (hv_u : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let u_plus_carry := u_i + carry_in
    let carry1 := if BitVec.ult u_plus_carry carry_in then (1 : Word) else 0
    let u_new := u_plus_carry + v_i
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x7 .x2 .x7))
       (CodeReq.singleton (base + 16) (.ADD .x2 .x2 .x5)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry1) **
       (.x5 ↦ᵣ v_i) ** (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i)) := by
  intro u_plus_carry carry1 u_new cr
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun) hv_v
  have I1 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 4) (by nofun) hv_u
  have I2 := add_spec_gen_rd_eq_rs1 .x2 .x7 u_i carry_in (base + 8) (by nofun)
  have I3 := sltu_spec_gen_rd_eq_rs2 .x7 .x2 u_plus_carry carry_in (base + 12) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x2 .x5 u_plus_carry v_i (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

/-- Add-back Part B: SLTU carry2, OR carry_out, SD u_new.
    3 instructions. Produces carry_out (x7) and stores u_new. -/
theorem divK_addback_partB_spec (u_base carry1 v_i u_new u_i : Word)
    (u_off : BitVec 12) (base : Word)
    (hv_u : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let carry2 := if BitVec.ult u_new v_i then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLTU .x5 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 4) (.OR .x7 .x7 .x5))
       (CodeReq.singleton (base + 8) (.SD .x6 .x2 u_off)))
    cpsTriple base (base + 12) cr
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry1) **
       (.x5 ↦ᵣ v_i) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ carry2) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro carry2 carry_out cr
  have I0 := sltu_spec_gen_rd_eq_rs2 .x5 .x2 u_new v_i base (by nofun)
  have I1 := or_spec_gen_rd_eq_rs1 .x7 .x5 carry1 carry2 (base + 4) (by nofun)
  have I2 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 8) hv_u
  runBlock I0 I1 I2

-- ============================================================================
-- Add-back finalization: u[j+4] += carry, q_hat--.
-- 4 instructions: LD + ADD + SD + ADDI.
-- ============================================================================

/-- Add-back finalization after limb corrections. -/
theorem divK_addback_final_spec (u_base carry q_hat v5_old u_top : Word)
    (u_off : BitVec 12) (base : Word)
    (hv : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let u_new := u_top + carry
    let q_hat' := q_hat + signExtend12 4095
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x5 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x6 .x5 u_off))
       (CodeReq.singleton (base + 12) (.ADDI .x11 .x11 4095))))
    cpsTriple base (base + 16) cr
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (u_base + signExtend12 u_off ↦ₘ u_top))
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry) ** (.x11 ↦ᵣ q_hat') **
       (.x5 ↦ᵣ u_new) ** (u_base + signExtend12 u_off ↦ₘ u_new)) := by
  intro u_new q_hat' cr
  have I0 := ld_spec_gen .x5 .x6 u_base v5_old u_top u_off base (by nofun) hv
  have I1 := add_spec_gen_rd_eq_rs1 .x5 .x7 u_top carry (base + 4) (by nofun)
  have I2 := sd_spec_gen .x6 .x5 u_base u_new u_top u_off (base + 8) hv
  have I3 := addi_spec_gen_same .x11 q_hat 4095 (base + 12) (by nofun)
  runBlock I0 I1 I2 I3

-- ============================================================================
-- Addback carry init: ADDI x7 x0 0 (set carry = 0).
-- ============================================================================

/-- Initialize add-back carry to 0. -/
theorem divK_addback_init_spec (v7_old : Word) (base : Word) :
    let cr := CodeReq.singleton base (.ADDI .x7 .x0 0)
    cpsTriple base (base + 4) cr
      ((.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ 0))
      ((.x7 ↦ᵣ signExtend12 0) ** (.x0 ↦ᵣ 0)) := by
  intro cr
  have I0 := addi_x0_spec_gen .x7 v7_old 0 base (by nofun)
  runBlock I0

-- ============================================================================
-- Addback condition: BEQ x7 x0 (skip correction if no borrow).
-- ============================================================================

/-- Correction condition: branch if borrow (x7) is zero. -/
theorem divK_correction_branch_spec (borrow : Word) (skip_off : BitVec 13) (base : Word) :
    let cr := CodeReq.singleton base (.BEQ .x7 .x0 skip_off)
    cpsBranch base cr
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0))
      (base + signExtend13 skip_off)
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0))
      (base + 4)
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0)) := by
  intro cr
  have hbeq := beq_spec_gen .x7 .x0 skip_off borrow 0 base
  exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
    (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
    hbeq
set_option maxRecDepth 2048 in
/-- Add-back full limb: partA (5 instrs) + partB (3 instrs) = 8 instructions.
    Input: carry_in (x7), v[i] and u[j+i] in memory.
    Output: carry_out (x7), u_new stored. -/
theorem divK_addback_limb_spec
    (sp u_base carry_in v5_old v2_old v_i u_i : Word)
    (v_off u_off : BitVec 12) (base : Word)
    (hv_v : isValidDwordAccess (sp + signExtend12 v_off) = true)
    (hv_u : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let u_plus_carry := u_i + carry_in
    let carry1 := if BitVec.ult u_plus_carry carry_in then (1 : Word) else 0
    let u_new := u_plus_carry + v_i
    let carry2 := if BitVec.ult u_new v_i then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x7 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.ADD .x2 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SLTU .x5 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x7 .x7 .x5))
       (CodeReq.singleton (base + 28) (.SD .x6 .x2 u_off))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ carry2) ** (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro u_plus_carry carry1 u_new carry2 carry_out cr
  -- Instructions from partA (5 instrs at base)
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun) hv_v
  have I1 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 4) (by nofun) hv_u
  have I2 := add_spec_gen_rd_eq_rs1 .x2 .x7 u_i carry_in (base + 8) (by nofun)
  have I3 := sltu_spec_gen_rd_eq_rs2 .x7 .x2 u_plus_carry carry_in (base + 12) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x2 .x5 u_plus_carry v_i (base + 16) (by nofun)
  -- Instructions from partB (3 instrs at base+20)
  have I5 := sltu_spec_gen_rd_eq_rs2 .x5 .x2 u_new v_i (base + 20) (by nofun)
  have I6 := or_spec_gen_rd_eq_rs1 .x7 .x5 carry1 carry2 (base + 24) (by nofun)
  have I7 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 28) hv_u
  runBlock I0 I1 I2 I3 I4 I5 I6 I7

end EvmAsm.Evm64
