## Goal

Create a stack-level spec for the MUL opcode using `evmWordIs`, completing the three-level proof hierarchy.

## Prerequisites

- None

## Context

The MUL opcode (63 instructions) has per-limb specs in `Evm64/Multiply/LimbSpec.lean` but lacks the topmost `evm_mul_stack_spec` that operates on `evmWordIs` assertions. Resolves #55.

## Approach

1. Create `Evm64/Multiply/Spec.lean`
2. Compose column specs (col0-col3 + epilogue) into full program spec
3. Lift to `evmWordIs` using bridge lemma `EvmWord.mul_correct` (may need to add to `EvmWordArith.lean`)
4. Final spec: `evm_mul_stack_spec` pops two `evmWordIs` words, pushes `a * b`
5. Follow `Add/Spec.lean` pattern

## Acceptance Criteria

- [ ] `evm_mul_stack_spec` proved with `evmWordIs` (0 sorry)
- [ ] Bridge lemma `EvmWord.mul_correct` connecting limb-level multiply to `EvmWord` multiplication
- [ ] `lake build` succeeds

## Milestone
B: Complete EVM Opcode Coverage

