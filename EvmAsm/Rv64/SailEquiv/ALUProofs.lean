/-
  EvmAsm.Rv64.SailEquiv.ALUProofs

  Per-instruction equivalence theorems for RTYPE and UTYPE instructions.

  ## Bidirectionality

  Each theorem has the form:
    Given StateRel s_rv s_sail,
    ∃ s_sail', runSail (execute_*) s_sail = some (RETIRE_SUCCESS, s_sail')
              ∧ StateRel (execInstrBr s_rv instr) s_sail'

  This is **bidirectional** for total instructions:

  - **Safety (Rv64 → SAIL):** The SAIL spec can execute and produces a matching
    state. Every Rv64 behavior is a valid SAIL behavior.

  - **Liveness (SAIL → Rv64):** The `some` witness proves SAIL succeeds. Since
    `execInstrBr` is total (pure function, always returns), the Rv64 model also
    "succeeds." `StateRel` ensures they agree. The Rv64 model doesn't get stuck
    on any instruction that SAIL accepts.

  Both directions hold because `execInstrBr` is total and `runSail` is
  deterministic for these instructions (no `choose`, no external state).
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
-- Register inequality facts (pre-proved via native_decide)
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
-- Bridge: reg_agree after a register insert (9x9 case split)
-- ============================================================================

theorem reg_agree_after_insert (s_sail : SailState) (s_rv : MachineState)
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
-- ADD, SUB, AND, OR, XOR
-- ============================================================================

-- The proof pattern: unfold execute_RTYPE, bridge rX_bits reads, case-split rd
-- for wX_bits, witness state, build StateRel (reg_agree from bridge + mem_agree trivial).

theorem add_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.ADD) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.ADD rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  -- Each goal after `cases rd`: witness state, build StateRel with concrete rd
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem sub_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SUB) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SUB rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem and_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.AND) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.AND rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem or_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.OR) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.OR rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem xor_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.XOR) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.XOR rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

-- ============================================================================
-- Comparison helper equivalences
-- ============================================================================

/-- SAIL's signed comparison value matches Rv64's SLT result. -/
theorem slt_value_equiv (a b : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_s a b)) =
    if BitVec.slt a b then (1 : BitVec 64) else 0 := by
  unfold zopz0zI_s bool_to_bit bool_bit_forwards zero_extend Sail.BitVec.zeroExtend
  cases h : (a.toInt <b b.toInt) <;> simp [h, BitVec.slt] <;> native_decide

/-- SAIL's unsigned comparison value matches Rv64's SLTU result. -/
theorem sltu_value_equiv (a b : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u a b)) =
    if BitVec.ult a b then (1 : BitVec 64) else 0 := by
  unfold zopz0zI_u bool_to_bit bool_bit_forwards zero_extend Sail.BitVec.zeroExtend BitVec.toNatInt
  cases h : (↑a.toNat <b ↑b.toNat) <;> simp [h, BitVec.ult] <;> native_decide

-- ============================================================================
-- SLT, SLTU
-- ============================================================================

theorem slt_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SLT) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SLT rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    slt_value_equiv]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem sltu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SLTU) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SLTU rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    sltu_value_equiv]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

-- ============================================================================
-- SLL, SRL, SRA (register shifts)
--
-- SAIL uses: shift_bits_left/right v (extractLsb rs2 5 0)
-- Rv64 uses: v <<< (rs2.toNat % 64) / v >>> ... / sshiftRight v ...
-- After simp, shift_bits_left = <<<, extractLsb reduces to % 64.
-- SRA additionally needs Int.toNat_emod for shift_bits_right_arith.
-- ============================================================================

theorem sll_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SLL) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SLL rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    shift_bits_left, Sail.BitVec.extractLsb]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem srl_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SRL) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SRL rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    shift_bits_right, Sail.BitVec.extractLsb]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem sra_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SRA) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SRA rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    shift_bits_right_arith, Sail.BitVec.extractLsb, BitVec.toNatInt, Int.toNat_emod]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

-- ============================================================================
-- LUI helper + proof
-- ============================================================================

/-- SAIL's sign_extend(imm ++ 0x000) equals Rv64's (imm.zeroExtend 32 <<< 12).signExtend 64. -/
theorem lui_equiv (imm : BitVec 20) :
    sign_extend (m := 64) (imm ++ (0 : BitVec 12)) =
    (imm.zeroExtend 32 <<< 12).signExtend 64 := by
  simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide

theorem lui_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd : Reg) (imm : BitVec 20) :
    ∃ s_sail',
      runSail (execute_UTYPE imm (regToRegidx rd) uop.LUI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.LUI rd imm)) s_sail' := by
  unfold execute_UTYPE
  simp only [runSail_bind, runSail_pure, lui_equiv]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, ← lui_equiv] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, ← lui_equiv] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, ← lui_equiv] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, ← lui_equiv] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, ← lui_equiv] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, ← lui_equiv] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, ← lui_equiv] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, ← lui_equiv] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, ← lui_equiv] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

-- ============================================================================
-- ADDIW helper + proof
-- ============================================================================

/-- SAIL's sign_extend(extractLsb (rs1 + sign_extend imm) 31 0) equals
    Rv64's ((rs1.truncate 32 + (signExtend12 imm).truncate 32) : BitVec 32).signExtend 64. -/
theorem addiw_equiv (rs1 : BitVec 64) (imm : BitVec 12) :
    (Sail.BitVec.signExtend (Sail.BitVec.extractLsb (rs1 + sign_extend (m := 64) imm) 31 0) 64 : BitVec 64) =
    ((rs1.truncate 32 + (imm.signExtend 64).truncate 32 : BitVec 32).signExtend 64 : BitVec 64) := by
  simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb]; bv_decide

theorem addiw_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (imm : BitVec 12) :
    ∃ s_sail',
      runSail (execute_ADDIW imm (regToRegidx rs1) (regToRegidx rd)) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.ADDIW rd rs1 imm)) s_sail' := by
  unfold execute_ADDIW
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    addiw_equiv]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12, ← addiw_equiv] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12, ← addiw_equiv] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12, ← addiw_equiv] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12, ← addiw_equiv] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12, ← addiw_equiv] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12, ← addiw_equiv] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12, ← addiw_equiv] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12, ← addiw_equiv] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12, ← addiw_equiv] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

end EvmAsm.Rv64.SailEquiv
