# Plan: `EvmWord.mul_correct` Bridge Lemma

## Context

The MUL opcode's per-limb spec (`evm_mul_spec` in `Multiply/LimbSpec.lean`) is complete. It outputs 4 result limbs via schoolbook multiplication organized by columns. What's missing is the bridge lemma proving these 4 limbs equal `(a * b).getLimb i`, and then the stack-level spec `evm_mul_stack_spec` in `Multiply/Spec.lean` (currently a copy of ADD spec).

## Approach: Two-phase proof

### Phase 1 — Nat-level schoolbook identity (new file: `EvmWordArith/MulCorrect.lean`)

**Goal:** Prove at the Nat level that the column-organized carry chain produces `(a.toNat * b.toNat) % 2^256`.

**Strategy:** 
- Mirror the exact `let` bindings from `evm_mul_spec` but at the Nat level (using `toNat`, `div`, `mod`)
- Convert each BitVec carry (`if ult x y then 1 else 0`) → Nat carry (`(x + y) / 2^64`)
- Convert each `rv64_mulhu a b` → `(a * b) / 2^64`, each `a * b` → `(a * b) % 2^64`
- Use `mul_full_product` to decompose each partial product
- Show the 4 result values satisfy `val256 r0 r1 r2 r3 = (val256 a0 a1 a2 a3 * val256 b0 b1 b2 b3) % 2^256`

**Key helper lemmas needed:**
1. `carry_toNat` (exists in Arithmetic.lean) — reuse for accumulation carries
2. Per-column Nat telescoping — each column's accumulation is correct
3. Final composition — columns combine to give full product mod 2^256

**Proof sketch:** Expand `val256 a * val256 b`, collect terms by result-limb position (mod W^4). The 10 relevant cross-products are:
- Limb 0: `a0*b0`
- Limb 1: `a0*b1 + a1*b0 + carry_from_limb0`
- Limb 2: `a0*b2 + a1*b1 + a2*b0 + carry_from_limb1`
- Limb 3: `a0*b3 + a1*b2 + a2*b1 + a3*b0 + carry_from_limb2`

Terms where `i+j >= 4` vanish mod 2^256. Use `ring` for algebraic normalization, `omega` for carry bounds.

### Phase 2 — BitVec lifting (in `MulCorrect.lean`)

**Goal:** `mul_correct` theorem:
```lean
theorem mul_correct (a b : EvmWord) :
    (a * b).getLimb 0 = <expr0> ∧
    (a * b).getLimb 1 = <expr1> ∧
    (a * b).getLimb 2 = <expr2> ∧
    (a * b).getLimb 3 = <expr3>
```
where `<exprN>` matches exactly what `evm_mul_spec` stores at `sp + 32 + 8*N`.

**Strategy (follows ADD pattern from Arithmetic.lean):**
1. `(a * b).toNat = (a.toNat * b.toNat) % 2^256` — from `BitVec.toNat_mul`
2. Decompose `a.toNat`, `b.toNat` via `toNat_eq_limb_sum`
3. Set `P = a.toNat * b.toNat`, then `(a*b).getLimb i = P % 2^256 / 2^(64*i) % 2^64`
4. Factor P at each limb boundary using `ring`
5. Use div/mod identities + carry equations from Phase 1 to match spec expressions
6. `BitVec.eq_of_toNat_eq` to lift to BitVec

### Phase 3 — Rewrite `Multiply/Spec.lean`

Replace the ADD-copied code with:
1. `evm_mul_code` definition (reference the code from LimbSpec)
2. `evm_mul_stack_spec` theorem that:
   - Calls `evm_mul_spec` for the raw limb result
   - Calls `mul_correct` to rewrite limbs as `(a * b).getLimb i`
   - Uses `cpsTriple_consequence` to lift precondition/postcondition (same pattern as ADD's stack spec)
   - Result: `evmWordIs (sp + 32) (a * b)` in postcondition

## Files to modify/create

| File | Action |
|------|--------|
| `EvmWordArith/MulCorrect.lean` | **Create** — Phase 1 + Phase 2 |
| `Multiply/Spec.lean` | **Rewrite** — Phase 3 |
| `EvmWordArith/Arithmetic.lean` | Possibly add `mul_correct` here instead if small enough |

## Risk areas

1. **Heartbeat budget:** The schoolbook chain has ~10 carries × 10 partial products. The ADD proof uses 800k heartbeats for 4 carries. MUL may need 2-4M heartbeats or must be split into sub-lemmas.
2. **nlinarith vs omega:** The product expansion involves multiplications of Nat variables (not just additions). `omega` can't handle these; `nlinarith` or `ring` + manual factoring needed.
3. **Carry chain complexity:** Each carry depends on previous carries. May need to track accumulators incrementally rather than all at once.

## Verification

- `lake build` succeeds with 0 sorry
- All three acceptance criteria from MUL_PLAN.md met
