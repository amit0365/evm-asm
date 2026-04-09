/-
  EvmAsm.Evm64.EvmWordArith.DivMulSubCarry

  Strict carry bound for the multiply-subtract operation: the per-limb
  carry from mulsub is always strictly less than 2^64 (fits in a Word).

  This is the critical bridge between register-level carry propagation
  (Word addition) and Nat-level carry equations. Without this, the Word
  carry could wrap around, breaking the chain.

  Key results:
  - mulsub_limb_carry_strict_lt: per-limb carry < 2^64 (unconditional)
  - mulsub_limb_word_carry_eq: Word carry = Nat carry (corollary)
  - mulsub_limb_nat_word_eq: per-limb equation using Word carry directly
  - mulsub_register_4limb_val256: 4-limb register ops → val256 equation
-/

import EvmAsm.Evm64.EvmWordArith.DivMulSubLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Strict carry bound: carry < 2^64 (always)
-- ============================================================================

/-- Helper: when MULHU = 2^64 - 2 (maximum), the low product is at most 1.
    From (2^64-1)² = (2^64-2)·2^64 + 1, so MUL result ≤ 1. -/
private theorem prod_lo_le_one_of_mulhu_max {q v_i : Word}
    (h : (rv64_mulhu q v_i).toNat = 2^64 - 2) :
    (q * v_i).toNat ≤ 1 := by
  have hprod := partial_product_decompose q v_i
  have hmax : q.toNat * v_i.toNat ≤ (2^64 - 1) * (2^64 - 1) :=
    Nat.mul_le_mul (by omega : q.toNat ≤ 2^64 - 1) (by omega : v_i.toNat ≤ 2^64 - 1)
  -- q * v_i = (2^64 - 2) * 2^64 + (q * v_i).toNat
  -- q * v_i ≤ (2^64 - 1)^2 = (2^64 - 2) * 2^64 + 1
  -- Therefore (q * v_i).toNat ≤ 1
  have : (2 : Nat) ^ 64 - 1 = 18446744073709551615 := by norm_num
  have : (2 : Nat) ^ 64 - 2 = 18446744073709551614 := by norm_num
  have : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  nlinarith

/-- The per-limb mulsub carry is strictly less than 2^64.

    The carry is `borrow_add + prod_hi + borrow_sub` where:
    - borrow_add ∈ {0, 1} (from prod_lo + carry_in overflow)
    - prod_hi ≤ 2^64 - 2 (from MULHU bound)
    - borrow_sub ∈ {0, 1} (from u_i < full_sub underflow)

    When prod_hi ≤ 2^64 - 3: carry ≤ 1 + (2^64 - 3) + 1 = 2^64 - 1 < 2^64.
    When prod_hi = 2^64 - 2: prod_lo ≤ 1, and borrow_add = 1 forces
    full_sub.toNat = 0 (modular wrap leaves 0), making borrow_sub = 0. -/
theorem mulsub_limb_carry_strict_lt (q v_i u_i carry_in : Word) :
    let prod_lo := q * v_i
    let prod_hi := rv64_mulhu q v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    borrow_add.toNat + prod_hi.toNat + borrow_sub.toNat < 2^64 := by
  intro prod_lo prod_hi full_sub borrow_add borrow_sub
  have h_ph := mulhu_toNat_le q v_i
  -- Work with Nat-level values: ba_n, bs_n ∈ {0, 1}
  set ba_n := if full_sub.toNat < carry_in.toNat then 1 else 0 with h_ba_def
  set bs_n := if u_i.toNat < full_sub.toNat then 1 else 0 with h_bs_def
  -- Convert borrow_add/borrow_sub toNat to ba_n/bs_n
  have h_ba : borrow_add.toNat = ba_n := by
    show (if BitVec.ult full_sub carry_in then (1 : Word) else 0).toNat = ba_n
    simp only [h_ba_def]; by_cases h : full_sub.toNat < carry_in.toNat <;> simp [BitVec.ult, h]
  have h_bs : borrow_sub.toNat = bs_n := by
    show (if BitVec.ult u_i full_sub then (1 : Word) else 0).toNat = bs_n
    simp only [h_bs_def]; by_cases h : u_i.toNat < full_sub.toNat <;> simp [BitVec.ult, h]
  rw [h_ba, h_bs]
  -- Bridge let-defs so omega can connect them
  have h_ph_bridge : prod_hi.toNat = (rv64_mulhu q v_i).toNat := rfl
  -- Now goal is: ba_n + prod_hi.toNat + bs_n < 2^64
  have h_ba_01 : ba_n ≤ 1 := by simp only [h_ba_def]; split <;> omega
  have h_bs_01 : bs_n ≤ 1 := by simp only [h_bs_def]; split <;> omega
  -- Easy case: prod_hi ≤ 2^64 - 3
  by_cases h_ph_max : (rv64_mulhu q v_i).toNat ≤ 2^64 - 3
  · -- ba_n ≤ 1, bs_n ≤ 1, ph ≤ 2^64 - 3 → sum ≤ 2^64 - 1
    omega
  -- Hard case: prod_hi = 2^64 - 2
  push Not at h_ph_max
  have h_ph_eq : (rv64_mulhu q v_i).toNat = 2^64 - 2 := by omega
  have h_plo : (q * v_i).toNat ≤ 1 := prod_lo_le_one_of_mulhu_max h_ph_eq
  -- Suffices: ba_n + bs_n ≤ 1
  suffices ba_n + bs_n ≤ 1 by omega
  have h_fs_val : full_sub.toNat = ((q * v_i).toNat + carry_in.toNat) % 2^64 :=
    BitVec.toNat_add (q * v_i) carry_in
  have h_ci := carry_in.isLt
  -- Case: ba_n = 0 → immediate
  by_cases h_ba_0 : ba_n = 0
  · omega
  -- Case: ba_n = 1 → overflow → full_sub = 0 → bs_n = 0
  have h_ba_1 : ba_n = 1 := by omega
  -- ba_n = 1 means full_sub.toNat < carry_in.toNat
  have h_ov : full_sub.toNat < carry_in.toNat := by
    simp only [h_ba_def] at h_ba_1; split at h_ba_1 <;> [assumption; omega]
  -- overflow: (q * v_i).toNat + carry_in.toNat ≥ 2^64
  have h_overflow : (q * v_i).toNat + carry_in.toNat ≥ 2^64 := by
    by_contra h_no; push Not at h_no
    rw [h_fs_val, Nat.mod_eq_of_lt h_no] at h_ov; omega
  -- (q * v_i).toNat = 1 and carry_in = 2^64 - 1
  have h_plo_1 : (q * v_i).toNat = 1 := by omega
  -- full_sub = 0
  have h_fs_0 : full_sub.toNat = 0 := by rw [h_fs_val]; omega
  -- bs_n = 0 (nothing is < 0)
  have : bs_n = 0 := by
    simp only [h_bs_def, show ¬(u_i.toNat < full_sub.toNat) from by omega, ite_false]
  omega

-- ============================================================================
-- Word carry = Nat carry (unconditional corollary)
-- ============================================================================

/-- The Word-level carry `(borrow_add + prod_hi) + borrow_sub` equals the
    Nat sum `borrow_add.toNat + prod_hi.toNat + borrow_sub.toNat`.

    This follows from `mulsub_limb_carry_strict_lt` (carry < 2^64 means
    the Word additions don't overflow) and `mulsub_carry_word_eq`. -/
theorem mulsub_limb_word_carry_eq (q v_i u_i carry_in : Word) :
    let prod_lo := q * v_i
    let prod_hi := rv64_mulhu q v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    ((borrow_add + prod_hi) + borrow_sub).toNat =
      borrow_add.toNat + prod_hi.toNat + borrow_sub.toNat := by
  intro prod_lo prod_hi full_sub borrow_add borrow_sub
  exact mulsub_carry_word_eq borrow_add prod_hi borrow_sub
    (mulsub_limb_carry_strict_lt q v_i u_i carry_in)

-- ============================================================================
-- Per-limb equation using Word carry directly
-- ============================================================================

/-- Per-limb mulsub Nat equation using the Word carry_out directly.
    Combines `mulsub_limb_nat_eq` and `mulsub_limb_word_carry_eq` so the
    carry_out can be passed directly as carry_in to the next limb. -/
theorem mulsub_limb_nat_word_eq (q v_i u_i carry_in : Word) :
    let prod_lo := q * v_i
    let prod_hi := rv64_mulhu q v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let u_new := u_i - full_sub
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    let carry_out := (borrow_add + prod_hi) + borrow_sub
    u_i.toNat + carry_out.toNat * 2^64 =
      u_new.toNat + q.toNat * v_i.toNat + carry_in.toNat := by
  intro prod_lo prod_hi full_sub borrow_add u_new borrow_sub carry_out
  rw [show carry_out = (borrow_add + prod_hi) + borrow_sub from rfl,
      mulsub_limb_word_carry_eq q v_i u_i carry_in]
  exact mulsub_limb_nat_eq q v_i u_i carry_in

-- ============================================================================
-- 4-limb composition: register ops → val256 equation
-- ============================================================================

/-- 4-limb mulsub from register operations → val256 Euclidean equation.

    This connects the exact register-level computation from `divK_mulsub_full_spec`
    to the mathematical Euclidean equation. The let-bindings match those in the
    mulsub loop body: for each limb i, compute prod_lo/hi, full_sub, borrows,
    updated u_new, and carry_out.

    The initial carry is 0 (first limb). Each subsequent limb uses the
    Word carry from the previous limb. -/
theorem mulsub_register_4limb_val256 (q v0 v1 v2 v3 u0 u1 u2 u3 : Word) :
    -- Limb 0 (carry_in = 0)
    let fs0 := q * v0 + (0 : Word)
    let ba0 := if BitVec.ult fs0 (0 : Word) then (1 : Word) else 0
    let un0 := u0 - fs0
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let c0 := (ba0 + rv64_mulhu q v0) + bs0
    -- Limb 1 (carry_in = c0)
    let fs1 := q * v1 + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let un1 := u1 - fs1
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let c1 := (ba1 + rv64_mulhu q v1) + bs1
    -- Limb 2 (carry_in = c1)
    let fs2 := q * v2 + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let un2 := u2 - fs2
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let c2 := (ba2 + rv64_mulhu q v2) + bs2
    -- Limb 3 (carry_in = c2)
    let fs3 := q * v3 + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let un3 := u3 - fs3
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let c3 := (ba3 + rv64_mulhu q v3) + bs3
    -- Result
    val256 u0 u1 u2 u3 + c3.toNat * 2^256 =
      val256 un0 un1 un2 un3 + q.toNat * val256 v0 v1 v2 v3 := by
  intro fs0 ba0 un0 bs0 c0
        fs1 ba1 un1 bs1 c1
        fs2 ba2 un2 bs2 c2
        fs3 ba3 un3 bs3 c3
  -- Per-limb equations from mulsub_limb_nat_word_eq
  have h0 := mulsub_limb_nat_word_eq q v0 u0 (0 : Word)
  have h1 := mulsub_limb_nat_word_eq q v1 u1 c0
  have h2 := mulsub_limb_nat_word_eq q v2 u2 c1
  have h3 := mulsub_limb_nat_word_eq q v3 u3 c2
  -- Simplify h0: carry_in = 0, so (0 : Word).toNat = 0
  have h0' : u0.toNat + c0.toNat * 2^64 = un0.toNat + q.toNat * v0.toNat := by
    have := h0; simp only [show (0 : Word).toNat = 0 from rfl] at this; linarith
  -- Chain via mulsub_chain_nat
  exact mulsub_chain_nat q.toNat u0 u1 u2 u3 v0 v1 v2 v3 un0 un1 un2 un3
    c0.toNat c1.toNat c2.toNat c3.toNat h0' h1 h2 h3

end EvmWord

end EvmAsm.Evm64
