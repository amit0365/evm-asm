/-
  EvmAsm.Evm64.DivMod.LoopDefs.Post

  Postcondition definitions for the loop body: loop-exit postcondition
  (loopExitPost + per-n abbrevs), mulsub-skip / addback body posts
  (loopBodySkipPost / loopBodyAddbackPost + abbrevs, mulsubN4_c3),
  and per-n call-path postconditions (n=3/n=2/n=1 generic-j variants).
-/

import EvmAsm.Evm64.DivMod.LoopDefs.Iter

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Loop exit postcondition for n
-- Common assertion shape for both cpsBranch exits (taken/ntaken).
-- Parameterized by the final output values (un0_f..un3_f, u4_f, q_f, c3).
-- ============================================================================

/-- Loop exit postcondition for n. Both taken (loop-back) and ntaken (exit)
    paths produce this same assertion shape, differing only in the output values.
    Encapsulates u_base/j'/q_addr address computation + 21-atom assertion chain. -/
@[irreducible]
def loopExitPost (n : Word) (sp j q_f c3 un0_f un1_f un2_f un3_f u4_f
    v0 v1 v2 v3 : Word) : Assertion :=
  let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let j' := j + signExtend12 4095
  let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
  (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
  (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
  (.x2 ↦ᵣ un3_f) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_f) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_f) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_f) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_f) **
  ((u_base + signExtend12 4064) ↦ₘ u4_f) **
  (q_addr ↦ₘ q_f)

theorem loopExitPost_unfold (n: Word) (sp j q_f c3 un0_f un1_f un2_f un3_f u4_f
    v0 v1 v2 v3 : Word) :
    loopExitPost n sp j q_f c3 un0_f un1_f un2_f un3_f u4_f v0 v1 v2 v3 =
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let j' := j + signExtend12 4095
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
    (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
    (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
    (.x2 ↦ᵣ un3_f) ** (.x0 ↦ᵣ (0 : Word)) **
    (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
    ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_f) **
    ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_f) **
    ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_f) **
    ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_f) **
    ((u_base + signExtend12 4064) ↦ₘ u4_f) **
    (q_addr ↦ₘ q_f) := by
  delta loopExitPost; rfl

/-- Loop exit postcondition abbreviations for n -/
abbrev loopExitPostN1 := loopExitPost (1 : Word)
abbrev loopExitPostN2 := loopExitPost (2 : Word)
abbrev loopExitPostN3 := loopExitPost (3 : Word)
abbrev loopExitPostN4 := loopExitPost (4 : Word)

-- ============================================================================
-- Composed postcondition: mulsub skip (borrow = 0) for n=4
-- Encapsulates the full mulsub computation + exit postcondition.
-- ============================================================================
/-- Full mulsub-skip postcondition for n loop body. -/
@[irreducible]
def loopBodySkipPost (n : Word) (sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  loopExitPost n sp j q_hat ms.2.2.2.2 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) v0 v1 v2 v3

/-- Full mulsub-addback postcondition for n loop body. -/
@[irreducible]
def loopBodyAddbackPost (n : Word) (sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
  let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
  let u4_new := u_top - c3
  let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
  loopExitPost n sp j (q_hat + signExtend12 4095) c3 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3

/-- Backward-compatible abbreviations for loopBodySkipPost and loopBodyAddbackPost. -/
abbrev loopBodyN1SkipPost := loopBodySkipPost (1 : Word)
abbrev loopBodyN1AddbackPost := loopBodyAddbackPost (1 : Word)
abbrev loopBodyN2SkipPost := loopBodySkipPost (2 : Word)
abbrev loopBodyN2AddbackPost := loopBodyAddbackPost (2 : Word)
abbrev loopBodyN3SkipPost := loopBodySkipPost (3 : Word)
abbrev loopBodyN3AddbackPost := loopBodyAddbackPost (3 : Word)
abbrev loopBodyN4SkipPost := loopBodySkipPost (4 : Word)
abbrev loopBodyN4AddbackPost := loopBodyAddbackPost (4 : Word)


/-- The mulsub carry c3 for n=4, used in borrow conditions. -/
def mulsubN4_c3 (q_hat v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Word :=
  (mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2

-- ============================================================================
-- Call path postconditions for n=3 (includes div128 scratch cells)
-- ============================================================================

/-- Call+skip postcondition for n=3 loop body at j=0.
    Bundles div128Quot computation + loopBodyN3SkipPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallSkipPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u3 u2 v2
  loopBodyN3SkipPost sp (0 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Call+addback postcondition for n=3 loop body at j=0.
    Bundles div128Quot computation + loopBodyN3AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallAddbackPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u3 u2 v2
  loopBodyN3AddbackPost sp (0 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Borrow condition for n=3 call+skip: mulsub doesn't overflow. -/
def isSkipBorrowN3Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u3 u2 v2
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)

/-- Borrow condition for n=3 call+addback: mulsub overflows. -/
def isAddbackBorrowN3Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u3 u2 v2
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word)

-- ============================================================================
-- Generic j versions of call path postconditions (for multi-iteration loops)
-- ============================================================================

/-- Call+skip postcondition for n=3 loop body, generic j.
    Bundles div128Quot computation + loopBodyN3SkipPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallSkipPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u3 u2 v2
  loopBodyN3SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Call+addback postcondition for n=3 loop body, generic j.
    Bundles div128Quot computation + loopBodyN3AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallAddbackPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u3 u2 v2
  loopBodyN3AddbackPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

-- ============================================================================
-- Generic j versions of n=1 call path postconditions
-- ============================================================================

/-- Call+skip postcondition for n=1 loop body, generic j.
    Bundles div128Quot computation + loopBodyN1SkipPost + scratch cells.
    For n=1: div128 uses u_hi=u1, u_lo=u0, v_top=v0. -/
@[irreducible]
def loopBodyN1CallSkipPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u1 u0 v0
  loopBodyN1SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u0)

/-- Call+addback postcondition for n=1 loop body, generic j.
    Bundles div128Quot computation + loopBodyN1AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN1CallAddbackPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u1 u0 v0
  loopBodyN1AddbackPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u0)

-- ============================================================================
-- Generic j versions of n=2 call path postconditions
-- ============================================================================

/-- Call+skip postcondition for n=2 loop body, generic j.
    Bundles div128Quot computation + loopBodyN2SkipPost + scratch cells.
    For n=2: div128 uses u_hi=u2, u_lo=u1, v_top=v1. -/
@[irreducible]
def loopBodyN2CallSkipPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u2 u1 v1
  loopBodyN2SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u1)

/-- Call+addback postcondition for n=2 loop body, generic j.
    Bundles div128Quot computation + loopBodyN2AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN2CallAddbackPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u2 u1 v1
  loopBodyN2AddbackPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u1)

end EvmAsm.Evm64
