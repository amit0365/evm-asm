/-
  EvmAsm.Evm64.DivMod.LoopDefs

  Backward-compatible re-export: the Knuth Algorithm D loop body
  computation and postcondition definitions now live under
  `EvmAsm/Evm64/DivMod/LoopDefs/`:

  - Iter   : iteration computation functions (mulsubN4, addbackN4,
             addbackN4_carry, div128 quotient helpers, per-n iter{Max,Call,
             Bool-unified}, double-addback iter variants) and their
             per-iteration unified postconditions.
  - Post   : loop-exit postcondition, mulsub-skip / addback body posts,
             per-n call-path postconditions (generic-j variants).
  - Bundle : multi-iteration precondition / postcondition bundles
             (two-, three-, four-iteration pre/posts; unified posts).

  Downstream modules may continue to `import EvmAsm.Evm64.DivMod.LoopDefs`
  or import individual sub-files directly.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.Iter
import EvmAsm.Evm64.DivMod.LoopDefs.Post
import EvmAsm.Evm64.DivMod.LoopDefs.Bundle
