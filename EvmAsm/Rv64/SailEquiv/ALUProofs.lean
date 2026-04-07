/-
  EvmAsm.Rv64.SailEquiv.ALUProofs

  Per-instruction equivalence theorems for ALU register-register instructions.
  First proof: ADD.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

set_option maxHeartbeats 1600000

-- ============================================================================
-- Register inequality facts (pre-proved via native_decide to avoid 179-constructor enumeration)
-- ============================================================================

private theorem reg_ne_x1_x2 : (Register.x1 == Register.x2) = false := by native_decide
private theorem reg_ne_x1_x5 : (Register.x1 == Register.x5) = false := by native_decide
private theorem reg_ne_x1_x6 : (Register.x1 == Register.x6) = false := by native_decide
private theorem reg_ne_x1_x7 : (Register.x1 == Register.x7) = false := by native_decide
private theorem reg_ne_x1_x10 : (Register.x1 == Register.x10) = false := by native_decide
private theorem reg_ne_x1_x11 : (Register.x1 == Register.x11) = false := by native_decide
private theorem reg_ne_x1_x12 : (Register.x1 == Register.x12) = false := by native_decide
private theorem reg_ne_x2_x1 : (Register.x2 == Register.x1) = false := by native_decide
private theorem reg_ne_x2_x5 : (Register.x2 == Register.x5) = false := by native_decide
private theorem reg_ne_x2_x6 : (Register.x2 == Register.x6) = false := by native_decide
private theorem reg_ne_x2_x7 : (Register.x2 == Register.x7) = false := by native_decide
private theorem reg_ne_x2_x10 : (Register.x2 == Register.x10) = false := by native_decide
private theorem reg_ne_x2_x11 : (Register.x2 == Register.x11) = false := by native_decide
private theorem reg_ne_x2_x12 : (Register.x2 == Register.x12) = false := by native_decide
private theorem reg_ne_x5_x1 : (Register.x5 == Register.x1) = false := by native_decide
private theorem reg_ne_x5_x2 : (Register.x5 == Register.x2) = false := by native_decide
private theorem reg_ne_x5_x6 : (Register.x5 == Register.x6) = false := by native_decide
private theorem reg_ne_x5_x7 : (Register.x5 == Register.x7) = false := by native_decide
private theorem reg_ne_x5_x10 : (Register.x5 == Register.x10) = false := by native_decide
private theorem reg_ne_x5_x11 : (Register.x5 == Register.x11) = false := by native_decide
private theorem reg_ne_x5_x12 : (Register.x5 == Register.x12) = false := by native_decide
private theorem reg_ne_x6_x1 : (Register.x6 == Register.x1) = false := by native_decide
private theorem reg_ne_x6_x2 : (Register.x6 == Register.x2) = false := by native_decide
private theorem reg_ne_x6_x5 : (Register.x6 == Register.x5) = false := by native_decide
private theorem reg_ne_x6_x7 : (Register.x6 == Register.x7) = false := by native_decide
private theorem reg_ne_x6_x10 : (Register.x6 == Register.x10) = false := by native_decide
private theorem reg_ne_x6_x11 : (Register.x6 == Register.x11) = false := by native_decide
private theorem reg_ne_x6_x12 : (Register.x6 == Register.x12) = false := by native_decide
private theorem reg_ne_x7_x1 : (Register.x7 == Register.x1) = false := by native_decide
private theorem reg_ne_x7_x2 : (Register.x7 == Register.x2) = false := by native_decide
private theorem reg_ne_x7_x5 : (Register.x7 == Register.x5) = false := by native_decide
private theorem reg_ne_x7_x6 : (Register.x7 == Register.x6) = false := by native_decide
private theorem reg_ne_x7_x10 : (Register.x7 == Register.x10) = false := by native_decide
private theorem reg_ne_x7_x11 : (Register.x7 == Register.x11) = false := by native_decide
private theorem reg_ne_x7_x12 : (Register.x7 == Register.x12) = false := by native_decide
private theorem reg_ne_x10_x1 : (Register.x10 == Register.x1) = false := by native_decide
private theorem reg_ne_x10_x2 : (Register.x10 == Register.x2) = false := by native_decide
private theorem reg_ne_x10_x5 : (Register.x10 == Register.x5) = false := by native_decide
private theorem reg_ne_x10_x6 : (Register.x10 == Register.x6) = false := by native_decide
private theorem reg_ne_x10_x7 : (Register.x10 == Register.x7) = false := by native_decide
private theorem reg_ne_x10_x11 : (Register.x10 == Register.x11) = false := by native_decide
private theorem reg_ne_x10_x12 : (Register.x10 == Register.x12) = false := by native_decide
private theorem reg_ne_x11_x1 : (Register.x11 == Register.x1) = false := by native_decide
private theorem reg_ne_x11_x2 : (Register.x11 == Register.x2) = false := by native_decide
private theorem reg_ne_x11_x5 : (Register.x11 == Register.x5) = false := by native_decide
private theorem reg_ne_x11_x6 : (Register.x11 == Register.x6) = false := by native_decide
private theorem reg_ne_x11_x7 : (Register.x11 == Register.x7) = false := by native_decide
private theorem reg_ne_x11_x10 : (Register.x11 == Register.x10) = false := by native_decide
private theorem reg_ne_x11_x12 : (Register.x11 == Register.x12) = false := by native_decide
private theorem reg_ne_x12_x1 : (Register.x12 == Register.x1) = false := by native_decide
private theorem reg_ne_x12_x2 : (Register.x12 == Register.x2) = false := by native_decide
private theorem reg_ne_x12_x5 : (Register.x12 == Register.x5) = false := by native_decide
private theorem reg_ne_x12_x6 : (Register.x12 == Register.x6) = false := by native_decide
private theorem reg_ne_x12_x7 : (Register.x12 == Register.x7) = false := by native_decide
private theorem reg_ne_x12_x10 : (Register.x12 == Register.x10) = false := by native_decide
private theorem reg_ne_x12_x11 : (Register.x12 == Register.x11) = false := by native_decide

-- ============================================================================
-- Bridge lemma 2: sailRegVal after wX_bits
-- ============================================================================

/-- After wX_bits writes value v to register rd in the SAIL state,
    sailRegVal of the resulting state agrees with Rv64's setReg. -/
theorem sailRegVal_after_wX_bits (s_sail : SailState) (s_rv : MachineState)
    (hrel : StateRel s_rv s_sail) (rd : Reg) (v : BitVec 64) :
    ∀ r : Reg, sailRegVal
      (match rd with
        | .x0 => s_sail
        | .x1 => { s_sail with regs := s_sail.regs.insert Register.x1 v }
        | .x2 => { s_sail with regs := s_sail.regs.insert Register.x2 v }
        | .x5 => { s_sail with regs := s_sail.regs.insert Register.x5 v }
        | .x6 => { s_sail with regs := s_sail.regs.insert Register.x6 v }
        | .x7 => { s_sail with regs := s_sail.regs.insert Register.x7 v }
        | .x10 => { s_sail with regs := s_sail.regs.insert Register.x10 v }
        | .x11 => { s_sail with regs := s_sail.regs.insert Register.x11 v }
        | .x12 => { s_sail with regs := s_sail.regs.insert Register.x12 v }) r =
      some ((s_rv.setReg rd v).getReg r) := by
  intro r
  set_option maxHeartbeats 800000 in
  cases rd <;> cases r <;>
    simp only [sailRegVal, MachineState.setReg, MachineState.getReg,
      Std.ExtDHashMap.get?_insert_self, Std.ExtDHashMap.get?_insert,
      beq_self_eq_true, ite_true, ite_false, decide_true, decide_false,
      reg_ne_x1_x2, reg_ne_x1_x5, reg_ne_x1_x6, reg_ne_x1_x7,
      reg_ne_x1_x10, reg_ne_x1_x11, reg_ne_x1_x12,
      reg_ne_x2_x1, reg_ne_x2_x5, reg_ne_x2_x6, reg_ne_x2_x7,
      reg_ne_x2_x10, reg_ne_x2_x11, reg_ne_x2_x12,
      reg_ne_x5_x1, reg_ne_x5_x2, reg_ne_x5_x6, reg_ne_x5_x7,
      reg_ne_x5_x10, reg_ne_x5_x11, reg_ne_x5_x12,
      reg_ne_x6_x1, reg_ne_x6_x2, reg_ne_x6_x5, reg_ne_x6_x7,
      reg_ne_x6_x10, reg_ne_x6_x11, reg_ne_x6_x12,
      reg_ne_x7_x1, reg_ne_x7_x2, reg_ne_x7_x5, reg_ne_x7_x6,
      reg_ne_x7_x10, reg_ne_x7_x11, reg_ne_x7_x12,
      reg_ne_x10_x1, reg_ne_x10_x2, reg_ne_x10_x5, reg_ne_x10_x6,
      reg_ne_x10_x7, reg_ne_x10_x11, reg_ne_x10_x12,
      reg_ne_x11_x1, reg_ne_x11_x2, reg_ne_x11_x5, reg_ne_x11_x6,
      reg_ne_x11_x7, reg_ne_x11_x10, reg_ne_x11_x12,
      reg_ne_x12_x1, reg_ne_x12_x2, reg_ne_x12_x5, reg_ne_x12_x6,
      reg_ne_x12_x7, reg_ne_x12_x10, reg_ne_x12_x11,
      dite_true, dite_false] <;>
    -- All remaining goals follow from hrel.reg_agree for a specific register
    all_goals (first | rfl | (
      have ha := hrel.reg_agree
      first
        | (have := ha .x1; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x2; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x5; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x6; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x7; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x10; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x11; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x12; simp [sailRegVal, MachineState.getReg] at this; exact this)))

-- ============================================================================
-- ADD
-- ============================================================================

/-- ADD rd rs1 rs2: the SAIL execute_RTYPE for rop.ADD produces a state
    that agrees with Rv64's execInstrBr on registers and memory. -/
theorem add_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.ADD) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      (∀ r : Reg, sailRegVal s_sail' r =
        some ((execInstrBr s_rv (.ADD rd rs1 rs2)).getReg r)) ∧
      s_sail'.mem = s_sail.mem := by
  -- Step 1: Unfold execute_RTYPE, apply bridge lemma for rX_bits (keep regToRegidx opaque)
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  -- Step 2: Case-split on rd, unfold regToRegidx, apply concrete wX_bits lemma
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  -- Step 3: Witness state and prove register agreement + memory preservation.
  -- sailRegVal_after_wX_bits needs the concrete rd, which is now known after cases.
  -- For each concrete rd, witness the state and apply bridge lemma 2
  all_goals first
    | exact ⟨_, rfl, sailRegVal_after_wX_bits s_sail s_rv hrel .x0 _, rfl⟩
    | exact ⟨_, rfl, sailRegVal_after_wX_bits s_sail s_rv hrel .x1 _, rfl⟩
    | exact ⟨_, rfl, sailRegVal_after_wX_bits s_sail s_rv hrel .x2 _, rfl⟩
    | exact ⟨_, rfl, sailRegVal_after_wX_bits s_sail s_rv hrel .x5 _, rfl⟩
    | exact ⟨_, rfl, sailRegVal_after_wX_bits s_sail s_rv hrel .x6 _, rfl⟩
    | exact ⟨_, rfl, sailRegVal_after_wX_bits s_sail s_rv hrel .x7 _, rfl⟩
    | exact ⟨_, rfl, sailRegVal_after_wX_bits s_sail s_rv hrel .x10 _, rfl⟩
    | exact ⟨_, rfl, sailRegVal_after_wX_bits s_sail s_rv hrel .x11 _, rfl⟩
    | exact ⟨_, rfl, sailRegVal_after_wX_bits s_sail s_rv hrel .x12 _, rfl⟩

end EvmAsm.Rv64.SailEquiv
