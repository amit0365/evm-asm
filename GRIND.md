# GRIND.md — simp/grind set conventions

This document is the single source of truth for how this repo organizes `grind`-based and `simp`-based proof automation. Read it before writing a new closing tactic, before adding a new `@[simp]`/`@[grind =]` lemma that other proofs will share, and before opening a follow-up issue to consolidate repetitive proof patterns.

`CLAUDE.md` and `AGENTS.md` link here from their proof-conventions sections — do not duplicate this content elsewhere.

---

## 1. Why we are doing this

A large class of proofs in this repo close goals that mix concrete bitvector evaluations (e.g., `signExtend12 4056 = 18446744073709551576`), small shift/`.toNat` reductions, and bitvector arithmetic. Historically these were closed by inline chains:

```lean
simp only [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
           show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
           show (3 : BitVec 6).toNat = 3 from by decide,
           show (1 : Word) <<< 3 = (8 : Word) from by decide,
           ...]
bv_omega
```

That style has three problems:

1. **Per-proof maintenance.** Every theorem repeats the same `show … from by decide` block. Adding a new concrete offset means editing every downstream proof.
2. **Cascade fragility.** When the assembly program shifts by one instruction, address literals change and dozens of inline chains have to be manually re-derived.
3. **Reviewer cost.** Identical 6–10-line chains drown signal in noise.

The fix is to register the atomic facts once in a named set, expose a single tactic that closes the class of goals, and migrate consumers to `by <tactic_name>`. New atomic facts are then a one-line `@[set_name, grind =]` declaration that every consumer picks up automatically.

`grind` is the right primary engine for these goals because it composes simp + congruence + cutsat in one step and is *resilient to vocabulary growth* — adding a fact to the set does not require revisiting any consumer. `grind` is kernel-checkable and therefore compatible with this repo's ban on `native_decide` / `bv_decide`.

## 2. Canonical example: `divmod_addr` (issue #263, PR #304)

The reference implementation lives at `EvmAsm/Evm64/DivMod/AddrNorm.lean` (+ `AddrNormAttr.lean`). It closes DivMod address-arithmetic equalities of the shape
`(sp + signExtend12 N₁ ± k <<< 3) ± signExtend12 N₂ = sp + signExtend12 N₃`.

```lean
-- GOOD: one-line, atomic facts in the shared `divmod_addr` set
theorem u_j1_0_eq_j0_4088 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

-- BAD: inline show-from-by-decide chain (per-proof maintenance burden)
theorem u_j1_0_eq_j0_4088' (sp : Word) : … := by
  simp only [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, …]
  bv_omega
```

When inventing a new grindset, copy the structure of `AddrNorm.lean` / `AddrNormAttr.lean` rather than reinventing it.

## 3. Pattern: registering a new grind/simp set

A grindset has at most three moving parts. Pick the layout that matches what you need.

### Layout A — Grind-only (simplest)

Use this if your tactic only needs `grind` to close goals — no consumer ever calls `simp only [my_set]` directly.

```lean
namespace MyDomain

@[grind =] theorem foo_eval_0 : foo 0 = bar := by decide
@[grind =] theorem foo_eval_1 : foo 1 = baz := by decide
-- ...

/-- Close a MyDomain equality. -/
macro "my_domain" : tactic => `(tactic| grind)

end MyDomain
```

### Layout B — Grind + named simp set (preferred when you also want `simp only [my_set]`)

Lean 4 forbids using an attribute in the same file in which it is declared. So a named simp attribute requires two files:

- `MyDomainAttr.lean`:
    ```lean
    import Mathlib.Tactic.Attr.Register

    /-- Simp set for MyDomain. -/
    register_simp_attr my_domain
    ```
- `MyDomain.lean`:
    ```lean
    import MyDomainAttr

    namespace MyDomain

    @[my_domain, grind =] theorem foo_eval_0 : foo 0 = bar := by decide
    -- ...

    /-- Close a MyDomain equality. Grind first (fastest, most resilient);
        simp+bv_omega fallback covers shapes grind can't fully reduce. -/
    macro "my_domain" : tactic =>
      `(tactic| first
        | grind
        | (simp only [my_domain]; bv_omega))

    end MyDomain
    ```

### Layout choice

- If consumers will only ever call `by my_domain` (the macro), prefer **Layout A**.
- If consumers may also want `simp only [my_domain]` for partial reductions or composition, use **Layout B**. The split file cost is small.
- The `divmod_addr` set uses **Layout B** because `simp only [divmod_addr]` may eventually be useful in larger composition proofs that don't want to invoke grind.

## 4. Rules of thumb

These are the durable lessons. Follow them unless you have a documented reason to deviate, and update this document if the deviation is general enough to be a new rule.

### Registration

- **Dual-register atomic facts** as `@[my_attr, grind =]`. Both `simp only [my_attr]` users and `grind` users see the same vocabulary, and the set stays in sync trivially.
- **Put atomic facts in a sub-namespace** (e.g., `EvmAsm.Evm64.DivMod.AddrNorm`) so file-private shadows in consumer files don't collide. `@[grind =]` and `@[my_attr]` are namespace-agnostic, so the macro keeps working without any `open`.
- **Tactic macros are syntactically global.** A `macro "my_domain" : tactic => …` declaration is reachable from any file that imports yours — no `open` needed.
- **Keep the set complete on first landing.** If a new concrete literal turns up later, add it as a one-line `@[my_attr, grind =]` fact in the set's file. Do **not** scatter inline `show … from by decide` lemmas in proof bodies as a workaround.

### Tactic macro

- **Grind-first, simp-second.** When grind and `simp only [...]; bv_omega` close the goal at comparable speed (within ~1.5×), put `grind` as the first branch of the `first` block and the simp+omega path as fallback. This matches the maintainability priority — see §5 for the empirical justification.
- **Fallback closer matches the goal class.** For arithmetic goals use `bv_omega`; for pure rewrite goals use `rfl`; for decidable propositions use `decide`. Don't reflexively reach for `bv_omega`.
- **Don't add a third branch unless you have evidence it's needed.** A `first | grind | simp+omega` pair is enough for the `divmod_addr` workload.

### Don'ts

- **Don't `grind` separation-logic permutations.** That is `xperm`'s job. Grind's congruence reasoning interacts badly with the 30+ atom assertions common in this repo and will time out.
- **Don't `grind` through `@[irreducible] def`s.** Grind respects irreducibility, so it cannot see through e.g. `loopBodyPostN4`. Use `delta` first or use a different mechanism.
- **Don't register broad `@[simp]` on signExtend / shift evaluations.** They are too aggressive for the global default simp set and will derail unrelated proofs. Always scope them under a named attribute (`@[divmod_addr]`, etc.) and let the macro pull them in via `simp only [name]` or `grind`.
- **Don't replace already-one-liner proofs.** If a proof is already `by decide` or `by rfl`, leave it alone. The grindset rollout is for collapsing *repetitive multi-line chains*, not for stylistic uniformity.
- **Don't replace specialized tactics** like `xperm`, `runBlock`, `seqFrame`, `liftSpec`, `pcFree`. They are tuned for their workloads and grind would be either slower, less precise, or both.

### Performance

- **Benchmark before bulk migration.** Before migrating a heavy file, run `lake build <module>` before and after. Reject the migration if it slows the module by more than ~10%.
- **Cap atomic-fact files at ~50 entries.** If a set grows beyond, split by sub-domain (e.g., `divmod_addr_se12`, `divmod_addr_shift`).
- **Watch grind's `@[grind =]` global index.** Many cheap facts are fine; complex unfolding rules in `@[grind =]` slow every `grind` call repo-wide. If a fact is heavy or domain-specific, prefer adding it to the *named simp set only* and reaching it via `grind [my_attr]` rather than the global `@[grind =]` index. We don't have a measured threshold yet — flag in PR review if a new set adds >100 global grind facts at once.

## 5. Empirical evidence (Lean v4.30.0-rc1)

The decision to default to `grind` over `simp only [...]; bv_omega` is grounded in this experiment, run during PR #304 on three representative DivMod address lemmas (`u_j1_0_eq_j0_4088`, `n3_ub1_off4088`, `n3_ub1_off4080`):

| Approach | Result | Time |
|---|---|---|
| `by grind` (bare, no hints) | **FAIL** — needs hints | — |
| `by grind [signExtend12]` (unfold hint) | pass | ~23ms |
| `by grind` with atomic facts as `@[grind =]` | pass | ~23ms |
| `simp only [inline]; bv_omega` (the original style) | pass | ~23ms |

**Conclusion:** grind and simp+omega are performance-equivalent on this workload. The maintainability win — adding a new offset is one line of `@[divmod_addr, grind =]` instead of a per-proof edit — is what tips the choice toward grind. Re-run a similar small experiment whenever you propose a new set; do not assume the conclusion generalizes blindly.

## 6. When to open a new grindset (vs. extend an existing one)

- **Extend an existing set** if the new fact is semantically the same domain (e.g., a new `signExtend12` offset → add to `divmod_addr` or, for non-DivMod usage, to the future `rv64_addr` set).
- **Open a new set** if the goal class is genuinely different — e.g., byte-extract algebra, register-operation rewrites, RLP encoding lemmas. Each new set should:
  - Solve a class of goals that recurs in ≥3 unrelated files (otherwise the inline lemma is fine).
  - Have ≤50 atomic facts at first landing.
  - Come with a tactic macro and one migrated file as proof-of-value, per §3.

When in doubt, write a short throwaway test demonstrating the duplication is real, link it in the issue, and propose the new set.

## 7. Sets currently in the repo

| Set | File | Status | Issue / PR |
|---|---|---|---|
| `divmod_addr` | `EvmAsm/Evm64/DivMod/AddrNorm.lean` (+ `AddrNormAttr.lean`) | landed (infrastructure + 1 file migrated) | #263 / #304 |

Add new rows here as sets land. Each row should link the issue and the introducing PR.

## 8. Roadmap

The phased rollout plan for spreading this methodology repo-wide is tracked in PLAN.md under the "Grindset Rollout" section (or a separate `GRINDSET_ROLLOUT.md` if extracted). Pending phases at time of writing:

1. **Bulk DivMod address migration** (~108 lemmas across 11 files) — extends `divmod_addr`.
2. **`rv64_addr`** — generalize `bv_addr` (currently `simp only [BitVec.add_assoc]; rfl`) to a richer set covering `signExtend13`/`signExtend21` evaluations and register-offset arithmetic.
3. **`byte_alg`** — `extractByte`/`replaceByte` algebra in `EvmAsm/Rv64/ByteOps.lean` and `EvmAsm/Evm64/Byte/`.
4. **`reg_ops`** — `getReg`/`setReg`/`getPC`/`setPC` equations in `Rv64/Basic.lean`. Lowest risk because the lemmas are already `@[simp]`; this phase only augments with `@[grind =]`.
5. **`bv_eval`** — concrete BitVec/Word arithmetic. Highest scope-blowup risk; gate on demand evidence from earlier phases.
6. **Retrospective & policy hardening** — measure proof-line reduction, decide whether to keep per-domain macros or unify into a single `evm_grind`.

Each phase = one issue + one PR (or a small series of ≤3-file PRs). When a phase lands, add a row to §7 and update its status here.

## 9. Maintenance & contribution

- **Update §7** when a new set lands.
- **Update §8** when a phase moves between pending → in-progress → landed, or when phases are added/removed.
- **Update §4 ("Rules of thumb")** when a new lesson generalizes from a single PR to a repo-wide convention.
- **Do not duplicate this content** in CLAUDE.md, AGENTS.md, or PR descriptions. Link here instead.
- **PR conventions for new sets:** name the file `<DomainName>Set.lean` or `<DomainName>Norm.lean` (consistent with `AddrNorm.lean`); place the attr-decl file alongside as `<DomainName>SetAttr.lean` if Layout B is used; provide one migrated file in the same PR as proof-of-value; document in §7.

## 10. References

- Lean 4 grind tactic: <https://leanprover.github.io/theorem_proving_in_lean4/> (search for grind), and `Init.Grind` in the Lean source for the `@[grind =]` / `@[grind ←]` / `@[grind →]` annotations.
- Mathlib `register_simp_attr`: `Mathlib/Tactic/Attr/Register.lean` — the canonical example of declaring named simp attributes.
- This repo's `bv_addr` precedent: `EvmAsm/Rv64/Tactics/SeqFrame.lean` — the original tiny-tactic-wrapper pattern (`simp only [BitVec.add_assoc]; rfl`) that the grindset methodology generalizes.
