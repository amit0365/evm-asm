/-
  EvmAsm.Evm64.DivMod.LimbSpec

  Backward-compatible re-export: the per-limb CPS specifications for the
  256-bit EVM DIV/MOD programs (Knuth Algorithm D) now live under
  `EvmAsm/Evm64/DivMod/LimbSpec/` as focused sub-files:

  - PerLimb : zero path, denorm per-limb, epilogue copy
  - PhaseA  : Phase A body + BEQ cpsBranch to zero path
  - PhaseB  : Phase B init, tail, cascade step
  - PhaseC  : CopyAU, NormB, NormA, Phase C2, LoopSetup, CLZ
  - MulSub  : mul-sub partA/partB, sub-carry, setup, save-j, composed mulsub_limb
  - Addback : add-back partA/partB, finalization, carry init, correction branch,
              composed addback_limb
  - Branch  : store q[j] (+ composed), loop control, trial quotient (u, vtop,
              MAX, composed)
  - Div128  : div128 subroutine (Phase 1, Step 1, Step 2, End phase)

  Downstream modules may continue to `import EvmAsm.Evm64.DivMod.LimbSpec`
  or import individual sub-files directly to avoid pulling unrelated
  compilation.
-/

import EvmAsm.Evm64.DivMod.LimbSpec.PerLimb
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseA
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseB
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseC
import EvmAsm.Evm64.DivMod.LimbSpec.MulSub
import EvmAsm.Evm64.DivMod.LimbSpec.Addback
import EvmAsm.Evm64.DivMod.LimbSpec.Branch
import EvmAsm.Evm64.DivMod.LimbSpec.Div128
