/-
  EvmAsm.Rv64.SailEquiv.ShiftProofs

  Per-instruction equivalence theorems for immediate shift instructions:
  SLLI, SRLI, SRAI.

  These use execute_SHIFTIOP which takes a 6-bit shamt, extracts bits [5:0]
  (identity for BitVec 6), then applies the shift operation.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.ALUProofs
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

set_option maxHeartbeats 1600000

theorem slli_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (shamt : BitVec 6) :
    ∃ s_sail',
      runSail (execute_SHIFTIOP shamt (regToRegidx rs1) (regToRegidx rd) sop.SLLI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SLLI rd rs1 shamt)) s_sail' := by
  sorry

theorem srli_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (shamt : BitVec 6) :
    ∃ s_sail',
      runSail (execute_SHIFTIOP shamt (regToRegidx rs1) (regToRegidx rd) sop.SRLI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SRLI rd rs1 shamt)) s_sail' := by
  sorry

theorem srai_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (shamt : BitVec 6) :
    ∃ s_sail',
      runSail (execute_SHIFTIOP shamt (regToRegidx rs1) (regToRegidx rd) sop.SRAI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SRAI rd rs1 shamt)) s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
