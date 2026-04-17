/-
  EvmAsm.Evm64.DivMod.LoopDefs.Iter

  Iteration computation functions for the Knuth Algorithm D loop body:
  mulsubN4, addbackN4, addbackN4_carry, div128 quotient helpers, per-n
  iter{Max,Call} variants, Bool-parameterized unified iter definitions,
  and the double-addback iter variants. Each iter definition is paired
  with its per-iteration unified postcondition (loopIterPost*).
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Mulsub computation: u - q*v for 4 limbs
-- Returns (un0, un1, un2, un3, c3) where c3 is the final carry.
-- ============================================================================

/-- Mulsub: compute u - q*v for 4 limbs, returning (un0, un1, un2, un3, c3). -/
def mulsubN4 (q v0 v1 v2 v3 u0 u1 u2 u3 : Word) :
    Word × Word × Word × Word × Word :=
  let p0_lo := q * v0; let p0_hi := rv64_mulhu q v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q * v1; let p1_hi := rv64_mulhu q v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q * v2; let p2_hi := rv64_mulhu q v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q * v3; let p3_hi := rv64_mulhu q v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  (un0, un1, un2, un3, c3)

/-- Addback: compute u + v for 4 limbs (used after mulsub underflow).
    Returns (aun0, aun1, aun2, aun3, aun4). -/
def addbackN4 (un0 un1 un2 un3 u4_new v0 v1 v2 v3 : Word) :
    Word × Word × Word × Word × Word :=
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0
  let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0
  let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1
  let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1
  let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2
  let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2
  let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3
  let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4_new + aco3
  (aun0, aun1, aun2, aun3, aun4)

/-- Extract the 4-limb carry-out from addbackN4's intermediate computation.
    This is the carry out of the 4th limb (aco3), before the u4_new addition.
    Used by the double-addback check: if carry = 0, a second addback is needed. -/
def addbackN4_carry (un0 un1 un2 un3 v0 v1 v2 v3 : Word) : Word :=
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0
  let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0
  let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1
  let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1
  let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2
  let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2
  let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3
  let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  ac1_3 ||| ac2_3

-- ============================================================================
-- Unified per-iteration result for n=1 max path (BLTU not taken)
-- ============================================================================

/-- Per-iteration computation for n=1 when the trial quotient is max (BLTU not taken).
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
@[irreducible]
def iterN1Max (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=1 max-path loop iteration.
    Uses iterN1Max to compute the result values, covering both skip and addback. -/
@[irreducible]
def loopIterPostN1Max (sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let c3 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN1 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3

-- ============================================================================
-- div128 quotient computation (shared across all n-cases)
-- ============================================================================

/-- Trial quotient from the div128 subroutine: divides u_hi:u_lo by v_top. -/
def div128Quot (u_hi u_lo v_top : Word) : Word :=
  let d_hi := v_top >>> (32 : BitVec 6).toNat
  let d_lo := (v_top <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u_lo >>> (32 : BitVec 6).toNat
  let div_un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u_hi d_hi
  let rhat := u_hi - q1 * d_hi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + d_hi
  let q_dlo := q1c * d_lo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * d_lo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 d_hi
  let rhat2 := un21 - q0 * d_hi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
  let q0_dlo := q0c * d_lo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  (q1' <<< (32 : BitVec 6).toNat) ||| q0'

/-- Low 32 bits of v_top, stored to scratch during div128 call path. -/
def div128DLo (v_top : Word) : Word :=
  (v_top <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

/-- Low 32 bits of u_lo, stored to scratch during div128 call path. -/
def div128Un0 (u_lo : Word) : Word :=
  (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

-- ============================================================================
-- Unified per-iteration result for n=3 max path (BLTU not taken)
-- ============================================================================

/-- Per-iteration computation for n=3 when the trial quotient is max (BLTU not taken).
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
def iterN3Max (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=3 max-path loop iteration.
    Uses iterN3Max to compute the result values, covering both skip and addback. -/
@[irreducible]
def loopIterPostN3Max (sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let c3 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN3 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3

-- ============================================================================
-- Unified per-iteration result for n=1 call path (BLTU taken)
-- ============================================================================

/-- Per-iteration computation for n=1 when the trial quotient comes from div128 (BLTU taken).
    For n=1: div128 uses u_hi=u1, u_lo=u0, v_top=v0.
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
@[irreducible]
def iterN1Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat := div128Quot u1 u0 v0
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=1 call-path loop iteration.
    Uses iterN1Call for the result values, plus div128 scratch cells.
    For n=1: scratch uses v0/div128DLo v0/div128Un0 u0. -/
@[irreducible]
def loopIterPostN1Call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let q_hat := div128Quot u1 u0 v0
  let c3 := (mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN1 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u0)

/-- Borrow condition for n=1 call+skip: mulsub doesn't overflow. -/
def isSkipBorrowN1Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u1 u0 v0
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)

/-- Borrow condition for n=1 call+addback: mulsub overflows. -/
def isAddbackBorrowN1Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u1 u0 v0
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word)

-- ============================================================================
-- Unified (Bool-parameterized) per-iteration for n=1
-- ============================================================================

/-- Unified per-iteration computation for n=1.
    `bltu = true` means BLTU taken (call path, trial quotient from div128).
    `bltu = false` means BLTU not taken (max path, trial quotient = 0xFFF).
    For n=1: div128 uses u_hi=u1, u_lo=u0, v_top=v0. -/
def iterN1 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  else iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[simp]
theorem iterN1_true (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN1 true v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN1]

@[simp]
theorem iterN1_false (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN1 false v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN1]

/-- Unified per-iteration postcondition for n=1.
    Same structure as loopIterPostN2 but delegates to loopIterPostN1Call/Max. -/
@[irreducible]
def loopIterPostN1 (bltu : Bool) (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  match bltu with
  | true => loopIterPostN1Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top
  | false => loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion

@[simp] theorem loopIterPostN1_call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN1 true sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    loopIterPostN1Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  delta loopIterPostN1; rfl

@[simp] theorem loopIterPostN1_max (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN1 false sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    (loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion) := by
  delta loopIterPostN1; rfl

-- ============================================================================
-- Unified per-iteration result for n=3 call path (BLTU taken)
-- ============================================================================

/-- Per-iteration computation for n=3 when the trial quotient comes from div128 (BLTU taken).
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
def iterN3Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat := div128Quot u3 u2 v2
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=3 call-path loop iteration.
    Uses iterN3Call for the result values, plus div128 scratch cells. -/
@[irreducible]
def loopIterPostN3Call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let q_hat := div128Quot u3 u2 v2
  let c3 := (mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN3 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

-- ============================================================================
-- Unified per-iteration result for n=2 max path (BLTU not taken)
-- ============================================================================

/-- Per-iteration computation for n=2 when the trial quotient is max (BLTU not taken).
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
@[irreducible]
def iterN2Max (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=2 max-path loop iteration.
    Uses iterN2Max to compute the result values, covering both skip and addback. -/
@[irreducible]
def loopIterPostN2Max (sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let c3 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN2 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3

-- ============================================================================
-- Unified per-iteration result for n=2 call path (BLTU taken)
-- ============================================================================

/-- Per-iteration computation for n=2 when the trial quotient comes from div128 (BLTU taken).
    For n=2: div128 uses u_hi=u2, u_lo=u1, v_top=v1.
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
@[irreducible]
def iterN2Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat := div128Quot u2 u1 v1
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=2 call-path loop iteration.
    Uses iterN2Call for the result values, plus div128 scratch cells. -/
@[irreducible]
def loopIterPostN2Call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let q_hat := div128Quot u2 u1 v1
  let c3 := (mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN2 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u1)

/-- Borrow condition for n=2 call+skip: mulsub doesn't overflow. -/
def isSkipBorrowN2Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u2 u1 v1
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)

/-- Borrow condition for n=2 call+addback: mulsub overflows. -/
def isAddbackBorrowN2Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u2 u1 v1
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word)

-- ============================================================================
-- Unified (Bool-parameterized) per-iteration computation for n=3
-- Issue #262: Unify max/call branch paths via Bool parameter
-- ============================================================================

/-- Unified per-iteration computation for n=3.
    `bltu = true` means BLTU taken (call path, trial quotient from div128).
    `bltu = false` means BLTU not taken (max path, trial quotient = 0xFFF).
    Internally handles both skip and addback via iterN3Call/iterN3Max. -/
def iterN3 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  else iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[simp]
theorem iterN3_true (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN3 true v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN3]

@[simp]
theorem iterN3_false (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN3 false v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN3]

/-- Unified per-iteration postcondition for n=3.
    Delegates to loopIterPostN3Call (call path) or loopIterPostN3Max (max path).
    When `bltu = true` (call path), includes div128 scratch cells.
    When `bltu = false` (max path), appends empAssertion (stripped by sepConj_emp_right'). -/
@[irreducible]
def loopIterPostN3 (bltu : Bool) (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  match bltu with
  | true => loopIterPostN3Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top
  | false => loopIterPostN3Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion

@[simp] theorem loopIterPostN3_call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN3 true sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    loopIterPostN3Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  delta loopIterPostN3; rfl

@[simp] theorem loopIterPostN3_max (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN3 false sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    (loopIterPostN3Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion) := by
  delta loopIterPostN3; rfl

-- ============================================================================
-- Unified (Bool-parameterized) per-iteration computation for n=2
-- Issue #262: Same pattern as n=3 but div128 uses u2/u1/v1
-- ============================================================================

/-- Unified per-iteration computation for n=2.
    `bltu = true` means BLTU taken (call path, trial quotient from div128).
    `bltu = false` means BLTU not taken (max path, trial quotient = 0xFFF).
    For n=2: div128 uses u_hi=u2, u_lo=u1, v_top=v1. -/
def iterN2 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  else iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[simp]
theorem iterN2_true (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN2 true v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN2]

@[simp]
theorem iterN2_false (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN2 false v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN2]

/-- Unified per-iteration postcondition for n=2.
    Same structure as loopIterPostN3 but delegates to loopIterPostN2Call/Max. -/
@[irreducible]
def loopIterPostN2 (bltu : Bool) (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  match bltu with
  | true => loopIterPostN2Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top
  | false => loopIterPostN2Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion

@[simp] theorem loopIterPostN2_call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN2 true sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    loopIterPostN2Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  delta loopIterPostN2; rfl

@[simp] theorem loopIterPostN2_max (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN2 false sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    (loopIterPostN2Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion) := by
  delta loopIterPostN2; rfl

-- ============================================================================
-- Double-addback iter variants (models the FIXED algorithm)
--
-- These define the correct semantics with double addback: after the first
-- addback, check addbackN4_carry; if carry = 0 (overestimate was 2),
-- perform a second addback and decrement q by 2 instead of 1.
--
-- The original iterN*Max/iterN*Call definitions (above) model the CURRENT
-- assembly which only does single addback. These _da variants model the
-- FIXED assembly with the backward-branch double addback check.
-- ============================================================================

/-- Helper: single iteration with double addback, parameterized by q_hat.
    Used by all iter*_da variants. -/
def iterWithDoubleAddback (q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    if carry = 0 then
      let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
      (q_hat + signExtend12 4095 + signExtend12 4095,
       ab'.1, ab'.2.1, ab'.2.2.1, ab'.2.2.2.1, ab'.2.2.2.2)
    else
      (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

@[irreducible]
def iterN1Max_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[irreducible]
def iterN1Call_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[irreducible]
def iterN2Max_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[irreducible]
def iterN2Call_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[irreducible]
def iterN3Max_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[irreducible]
def iterN3Call_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 u_top

end EvmAsm.Evm64
