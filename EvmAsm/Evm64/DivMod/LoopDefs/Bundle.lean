/-
  EvmAsm.Evm64.DivMod.LoopDefs.Bundle

  Multi-iteration precondition / postcondition bundles: two-iteration
  (n=3, n=2, n=1), three-iteration (n=2, n=1), and four-iteration (n=1)
  loop pre/post, including scratch-cell variants, legacy max+skip posts,
  and the Bool-parameterized unified postconditions.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.Post

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Two-iteration loop precondition for n=3
-- ============================================================================

/-- Precondition for the n=3 two-iteration loop (base+448 → base+904).
    Bundles registers, v-cells, u-cells at j=1 base, and extra j=0 cells. -/
@[irreducible]
def loopN3Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word) : Assertion :=
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_1 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_1 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_1 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_1 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_1 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig) **
  (q_addr_0 ↦ₘ q0_old)

-- ============================================================================
-- Two-iteration loop postconditions for n=3 (max path, unified)
-- ============================================================================

/-- Postcondition for the full n=3 two-iteration loop (both iterations max path).
    Uses iterN3Max for each iteration to handle all skip/addback combinations. -/
@[irreducible]
def loopN3MaxPost (sp v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word) : Assertion :=
  let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

-- ============================================================================
-- Two-iteration loop precondition/postcondition for n=3 (call path)
-- ============================================================================

/-- Precondition for the n=3 two-iteration loop with scratch cells.
    Used when at least one iteration takes the call (div128) path. -/
@[irreducible]
def loopN3PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN3Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

/-- Postcondition for the full n=3 two-iteration loop (both iterations call path).
    Uses iterN3Call for each iteration. Scratch cells have j=0's values. -/
@[irreducible]
def loopN3CallCallPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word) : Assertion :=
  let r1 := iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Call sp base (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

/-- Postcondition for n=3 two-iteration loop (j=1 max, j=0 call).
    Scratch cells have j=0's call values. -/
@[irreducible]
def loopN3MaxCallPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word) : Assertion :=
  let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Call sp base (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

/-- Postcondition for n=3 two-iteration loop (j=1 call, j=0 max).
    Scratch cells have j=1's call values (unchanged by j=0 max path). -/
@[irreducible]
def loopN3CallMaxPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word) : Assertion :=
  let r1 := iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

-- ============================================================================
-- Legacy two-iteration postconditions (max+skip × max+skip specific case)
-- ============================================================================

/-- Postcondition for the full n=3 two-iteration loop (max+skip at both j=1 and j=0).
    Includes the j=0 exit postcondition plus j=1's carried frame atoms (u4_new, q[1]). -/
@[irreducible]
def loopN3MaxSkipSkipPost (sp v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word) : Assertion :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopBodyN3SkipPost sp (0 : Word) q_hat v0 v1 v2 v3
    u0_orig ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ (u_top - ms.2.2.2.2)) **
  (q_addr_1 ↦ₘ q_hat)

/-- j=0 BLTU condition for n=3 max path after j=1 max+skip: u3_j0 ≥ v2. -/
def isMaxBltuN3After_j1_skip (v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Prop :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  ¬BitVec.ult ms.2.2.1 v2

/-- j=0 borrow=0 condition for n=3 max path after j=1 max+skip. -/
def isSkipBorrowN3After_j1_skip (v0 v1 v2 v3 u0 u1 u2 u3 u0_orig : Word) : Prop :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  (if BitVec.ult ms.2.2.2.1
      (mulsubN4_c3 q_hat v0 v1 v2 v3 u0_orig ms.1 ms.2.1 ms.2.2.1)
    then (1 : Word) else 0) = (0 : Word)

-- ============================================================================
-- Unified two-iteration loop postcondition for n=3
-- ============================================================================

/-- Unified postcondition for the n=3 two-iteration loop.
    `bltu_1` is the BLTU outcome at j=1, `bltu_0` at j=0.
    Delegates to existing per-path postconditions via match.
    For max×max, scratch cells pass through unchanged (carried as parameters).
    For other combinations, scratch cells are overwritten by div128 (params unused). -/
@[irreducible]
def loopN3UnifiedPost (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  match bltu_1, bltu_0 with
  | false, false =>
    loopN3MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig **
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | true,  true  => loopN3CallCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig
  | false, true  => loopN3MaxCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig
  | true,  false => loopN3CallMaxPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig

-- ============================================================================
-- Three-iteration loop precondition/postcondition for n=2
-- Issue #262: Bool-parameterized composition for 3 iterations (j=2,1,0)
-- ============================================================================

/-- Precondition for the n=2 three-iteration loop (j starts at 2).
    Includes j=2's iteration precondition plus pre-existing atoms
    for j=1 (u0_orig_1, q1_old) and j=0 (u0_orig_0, q0_old). -/
@[irreducible]
def loopN2Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0
    q2_old q1_old q0_old : Word) : Assertion :=
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_2 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_2 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_2 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_2 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_2 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_2 ↦ₘ q2_old) **
  ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) **
  (q_addr_0 ↦ₘ q0_old)

/-- Precondition for n=2 three-iteration loop with scratch cells.
    Used when at least one iteration may take the call (div128) path. -/
@[irreducible]
def loopN2PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0
    q2_old q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN2Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0 q2_old q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

-- ============================================================================
-- Two-iteration (j=1, j=0) precondition/postcondition for n=2
-- Mirrors loopN3Pre/loopN3UnifiedPost but with n=2 values
-- ============================================================================

/-- Precondition for n=2 two-iteration loop (j=1, j=0).
    Same structure as loopN3Pre but with n_mem = 2. -/
@[irreducible]
def loopN2Iter10Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word) : Assertion :=
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_1 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_1 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_1 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_1 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_1 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig) **
  (q_addr_0 ↦ₘ q0_old)

/-- Precondition for n=2 two-iteration loop with scratch cells. -/
@[irreducible]
def loopN2Iter10PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN2Iter10Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

/-- Unified postcondition for n=2 two-iteration loop (j=1, j=0).
    Same structure as loopN3UnifiedPost but without j=2 carried atoms.
    Scratch handling: call path includes scratch, max path carries passthrough params. -/
@[irreducible]
def loopN2Iter10Post (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig
     ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  let r1 := iterN2 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=0 iteration postcondition (includes scratch if bltu_0 = true)
  loopIterPostN2 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  -- Carried atoms from j=1
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  -- Scratch cells
  match bltu_1, bltu_0 with
  | false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, true  => empAssertion
  | true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u1)
  | true,  true  => empAssertion

/-- Unified postcondition for the n=2 three-iteration loop.
    Parameterized by `(bltu_2 bltu_1 bltu_0 : Bool)` covering all 8 path combinations.

    Structure:
    - j=0 iteration postcondition (includes scratch when bltu_0 = true)
    - Carried atoms from j=1 (u4, q) and j=2 (u4, q)
    - Scratch cells: depend on which iteration was the last call path
      - All max (F,F,F): passthrough original scratch params
      - bltu_0=true: scratch handled inside loopIterPostN2Call (empAssertion here)
      - Last call was j=1 (bltu_1=T, bltu_0=F): scratch from j=1's div128
      - Last call was j=2 (bltu_2=T, others F): scratch from j=2's div128 -/
@[irreducible]
def loopN2UnifiedPost (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_1 u0_orig_0
     ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  -- Compute iteration results
  let r2 := iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let r1 := iterN2 bltu_1 v0 v1 v2 v3 u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  -- Address bases for carried atoms
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=0 iteration postcondition (includes scratch if bltu_0 = true)
  loopIterPostN2 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0_orig_0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  -- Carried atoms from j=1 and j=2
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  ((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1) **
  -- Scratch cells
  match bltu_2, bltu_1, bltu_0 with
  | false, false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, false, true  => empAssertion
  | false, true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r2.2.1)
  | false, true,  true  => empAssertion
  | true,  false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u1)
  | true,  false, true  => empAssertion
  | true,  true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r2.2.1)
  | true,  true,  true  => empAssertion

-- ============================================================================
-- Four-iteration loop precondition/postcondition for n=1
-- Issue #262: Bool-parameterized composition for 4 iterations (j=3,2,1,0)
-- ============================================================================

/-- Precondition for the n=1 four-iteration loop (j starts at 3).
    Includes j=3's iteration precondition plus pre-existing atoms
    for j=2 (u0_orig_2, q2_old), j=1 (u0_orig_1, q1_old), and j=0 (u0_orig_0, q0_old). -/
@[irreducible]
def loopN1Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_2 u0_orig_1 u0_orig_0
    q3_old q2_old q1_old q0_old : Word) : Assertion :=
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (3 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_3 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_3 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_3 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_3 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_3 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_3 ↦ₘ q3_old) **
  ((u_base_2 + signExtend12 0) ↦ₘ u0_orig_2) **
  (q_addr_2 ↦ₘ q2_old) **
  ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) **
  (q_addr_0 ↦ₘ q0_old)

/-- Precondition for n=1 four-iteration loop with scratch cells.
    Used when at least one iteration may take the call (div128) path. -/
@[irreducible]
def loopN1PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_2 u0_orig_1 u0_orig_0
    q3_old q2_old q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN1Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_2 u0_orig_1 u0_orig_0 q3_old q2_old q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

-- ============================================================================
-- Two-iteration (j=1, j=0) precondition/postcondition for n=1
-- ============================================================================

/-- Precondition for n=1 two-iteration loop (j=1, j=0).
    Same structure as loopN2Iter10Pre but with n_mem = 1. -/
@[irreducible]
def loopN1Iter10Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word) : Assertion :=
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_1 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_1 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_1 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_1 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_1 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig) **
  (q_addr_0 ↦ₘ q0_old)

/-- Precondition for n=1 two-iteration loop with scratch cells. -/
@[irreducible]
def loopN1Iter10PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN1Iter10Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

/-- Unified postcondition for n=1 two-iteration loop (j=1, j=0).
    Same structure as loopN2Iter10Post but with n=1 per-iteration functions.
    Scratch handling: call path includes scratch, max path carries passthrough params.
    For n=1: div128 scratch uses v0/div128DLo v0/div128Un0 u0. -/
@[irreducible]
def loopN1Iter10Post (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig
     ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  let r1 := iterN1 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=0 iteration postcondition (includes scratch if bltu_0 = true)
  loopIterPostN1 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  -- Carried atoms from j=1
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  -- Scratch cells
  match bltu_1, bltu_0 with
  | false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, true  => empAssertion
  | true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0)
  | true,  true  => empAssertion

-- ============================================================================
-- Three-iteration (j=2, j=1, j=0) precondition/postcondition for n=1
-- ============================================================================

/-- Precondition for n=1 three-iteration loop (j=2, j=1, j=0).
    Same structure as loopN2Pre but with n_mem = 1, starting at j=2. -/
@[irreducible]
def loopN1Iter210Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0
    q2_old q1_old q0_old : Word) : Assertion :=
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_2 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_2 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_2 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_2 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_2 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_2 ↦ₘ q2_old) **
  ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) **
  (q_addr_0 ↦ₘ q0_old)

/-- Precondition for n=1 three-iteration loop with scratch cells. -/
@[irreducible]
def loopN1Iter210PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0
    q2_old q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN1Iter210Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0 q2_old q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

/-- Unified postcondition for n=1 three-iteration loop (j=2, j=1, j=0).
    Parameterized by `(bltu_2 bltu_1 bltu_0 : Bool)` covering all 8 path combinations.
    For n=1: div128 scratch uses v0/div128DLo v0/div128Un0 u0 (u0 from the call iteration). -/
@[irreducible]
def loopN1Iter210Post (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_1 u0_orig_0
     ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  -- Compute iteration results
  let r2 := iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let r1 := iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  -- Address bases for carried atoms
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=0 iteration postcondition (includes scratch if bltu_0 = true)
  loopIterPostN1 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0_orig_0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  -- Carried atoms from j=1 and j=2
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  ((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1) **
  -- Scratch cells
  match bltu_2, bltu_1, bltu_0 with
  | false, false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, false, true  => empAssertion
  | false, true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | false, true,  true  => empAssertion
  | true,  false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0)
  | true,  false, true  => empAssertion
  | true,  true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | true,  true,  true  => empAssertion

/-- Unified postcondition for the n=1 four-iteration loop.
    Parameterized by `(bltu_3 bltu_2 bltu_1 bltu_0 : Bool)` covering all 16 path combinations.

    Structure:
    - j=0 iteration postcondition (includes scratch when bltu_0 = true)
    - Carried atoms from j=1 (u4, q), j=2 (u4, q), and j=3 (u4, q)
    - Scratch cells: depend on which iteration was the last call path
      - All max (F,F,F,F): passthrough original scratch params
      - bltu_0=true: scratch handled inside loopIterPostN1Call (empAssertion here)
      - Last call was j=1 (bltu_1=T, bltu_0=F): scratch from j=1's div128 (div128Un0 u0_orig_1)
      - Last call was j=2 (bltu_2=T, bltu_1=F, bltu_0=F): scratch from j=2's div128 (div128Un0 u0_orig_2)
      - Last call was j=3 (bltu_3=T, others F): scratch from j=3's div128 (div128Un0 u0) -/
@[irreducible]
def loopN1UnifiedPost (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_2 u0_orig_1 u0_orig_0
     ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  -- Compute iteration results
  let r3 := iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let r2 := iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
  let r1 := iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  -- Address bases for carried atoms
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=0 iteration postcondition (includes scratch if bltu_0 = true)
  loopIterPostN1 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0_orig_0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  -- Carried atoms from j=1, j=2, and j=3
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  ((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1) **
  ((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1) **
  -- Scratch cells: value depends on the last call-path iteration
  match bltu_3, bltu_2, bltu_1, bltu_0 with
  | false, false, false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, false, false, true  => empAssertion
  | false, false, true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | false, false, true,  true  => empAssertion
  | false, true,  false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_2)
  | false, true,  false, true  => empAssertion
  | false, true,  true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | false, true,  true,  true  => empAssertion
  | true,  false, false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0)
  | true,  false, false, true  => empAssertion
  | true,  false, true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | true,  false, true,  true  => empAssertion
  | true,  true,  false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_2)
  | true,  true,  false, true  => empAssertion
  | true,  true,  true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | true,  true,  true,  true  => empAssertion

end EvmAsm.Evm64
