/-
  EvmAsm.Evm64.EvmWordArith.MulCorrect

  Bridge lemma: the column-organized schoolbook multiply from evm_mul_spec
  produces the correct limbs of (a * b : EvmWord).

  Column structure (NOT a linear carry chain like ADD):
    Col0: b[0] × {a[0],a[1],a[2],a[3]} → initializes r0, r1 partial, r2 partial, r3 partial
    Col1: b[1] × {a[0],a[1],a[2]}      → finalizes r1, updates r2, r3 partial
    Col2: b[2] × {a[0],a[1]}            → finalizes r2, updates r3
    Col3: b[3] × {a[0]}                 → finalizes r3

  Reference mapping (evm_mul_spec postcondition → result limbs):
    sp+32 ↦ c0_r0      → (a*b).getLimb 0
    sp+40 ↦ c1_r1      → (a*b).getLimb 1
    sp+48 ↦ c2_r2      → (a*b).getLimb 2
    sp+56 ↦ r3_final   → (a*b).getLimb 3

  Proof strategy: toNat decomposition + mul_full_product + carry_toNat + div/mod
-/

import EvmAsm.Evm64.EvmWordArith.MultiLimb
import EvmAsm.Evm64.EvmWordArith.Arithmetic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- MUL correctness: column-organized schoolbook multiply produces (a * b) limbs
-- ============================================================================

theorem mul_correct (a b : EvmWord):
    let a0 := a.getLimb 0; let a1 := a.getLimb 1; let a2 := a.getLimb 2; let a3 := a.getLimb 3;
    let b0 := b.getLimb 0; let b1 := b.getLimb 1; let b2 := b.getLimb 2; let b3 := b.getLimb 3;
    -- Col0 intermediates
    let c0_r0 := a0 * b0
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_hi_a2b0 := rv64_mulhu a2 b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c0_c2 := if BitVec.ult c0_r2 c0_lo_a2b0 then (1 : Word) else 0
    let c0_r3p := c0_hi_a2b0 + c0_c2 + a3 * b0
    -- Col1 intermediates
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_cr1 := if BitVec.ult c1_r2a c1_rc then (1 : Word) else 0
    let c1_lo2 := a1 * b1
    let c1_hi2 := rv64_mulhu a1 b1
    let c1_r2 := c1_r2a + c1_lo2
    let c1_cr2 := if BitVec.ult c1_r2 c1_lo2 then (1 : Word) else 0
    let c1_rc2 := c1_hi2 + c1_cr2
    let c1_r3p := c1_cr1 + c1_rc2 + a2 * b1 + c0_r3p
    -- Col2 intermediates
    let c2_lo := a0 * b2
    let c2_hi := rv64_mulhu a0 b2
    let c2_r2 := c1_r2 + c2_lo
    let c2_c := if BitVec.ult c2_r2 c2_lo then (1 : Word) else 0
    let c2_rc := c2_hi + c2_c + a1 * b2
    let c2_r3 := c1_r3p + c2_rc
    -- Col3
    let r3_final := c2_r3 + a0 * b3
    (a * b).getLimb 0 = c0_r0 ∧
    (a * b).getLimb 1 = c1_r1 ∧
    (a * b).getLimb 2 = c2_r2 ∧
    (a * b).getLimb 3 = r3_final := by
  intro a0 a1 a2 a3 b0 b1 b2 b3 c0_r0 c0_hi_a0b0 c0_lo_a1b0 c0_hi_a1b0 c0_r1 c0_c1 c0_lo_a2b0 c0_hi_a2b0 c0_r2 c0_c2 c0_r3p c1_lo c1_hi c1_r1 c1_c1 c1_rc c1_r2a c1_cr1 c1_lo2 c1_hi2 c1_r2 c1_cr2 c1_rc2 c1_r3p c2_lo c2_hi c2_r2 c2_c c2_rc c2_r3 r3_final

  have h_c0_r0 : c0_r0.toNat = (a0.toNat * b0.toNat) % 2^64 :=
      mul_toNat a0 b0
  have h_c0_hi_a0b0 : c0_hi_a0b0.toNat = (a0.toNat * b0.toNat) / 2^64 :=
        rv64_mulhu_toNat a0 b0
  have h_c0_lo_a1b0 : c0_lo_a1b0.toNat = (a1.toNat * b0.toNat) % 2^64 :=
        mul_toNat a1 b0
  have h_c0_hi_a1b0 : c0_hi_a1b0.toNat = (a1.toNat * b0.toNat) / 2^64 :=
      rv64_mulhu_toNat a1 b0
  have h_c0_r1 : c0_r1.toNat = (c0_hi_a0b0.toNat + c0_lo_a1b0.toNat) % 2^64 :=
      BitVec.toNat_add c0_hi_a0b0 c0_lo_a1b0
  have h_c0_c1 : c0_c1.toNat = (c0_hi_a0b0.toNat + c0_lo_a1b0.toNat) / 2^64 :=
      EvmWord.carry_toNat c0_hi_a0b0 c0_lo_a1b0
  have h_c0_lo_a2b0 : c0_lo_a2b0.toNat = (a2.toNat * b0.toNat) % 2^64 :=
      mul_toNat a2 b0
  have h_c0_hi_a2b0 : c0_hi_a2b0.toNat = (a2.toNat * b0.toNat) / 2^64 :=
      rv64_mulhu_toNat a2 b0
  have h_c0_r2 : c0_r2.toNat = ((c0_hi_a1b0 + c0_c1).toNat + c0_lo_a2b0.toNat) % 2^64 :=
      BitVec.toNat_add (c0_hi_a1b0 + c0_c1) c0_lo_a2b0
  have h_c0_r2_inner : (c0_hi_a1b0 + c0_c1).toNat = (c0_hi_a1b0.toNat + c0_c1.toNat) % 2^64 :=
      BitVec.toNat_add c0_hi_a1b0 c0_c1
  have h_c0_c2 : c0_c2.toNat = ((c0_hi_a1b0 + c0_c1).toNat + c0_lo_a2b0.toNat) / 2^64 :=
      EvmWord.carry_toNat (c0_hi_a1b0 + c0_c1) c0_lo_a2b0
  have h_c0_c2_inner : (c0_hi_a1b0 + c0_c1).toNat = (c0_hi_a1b0.toNat + c0_c1.toNat) % 2^64 :=
      BitVec.toNat_add c0_hi_a1b0 c0_c1
  have h_c0_r3p : c0_r3p.toNat = ((c0_hi_a2b0 + c0_c2).toNat + (a3 * b0).toNat) % 2^64 :=
      BitVec.toNat_add (c0_hi_a2b0 + c0_c2) (a3 * b0)
  have h_c0_r3p_inner : (c0_hi_a2b0 + c0_c2).toNat = (c0_hi_a2b0.toNat + c0_c2.toNat) % 2^64 :=
      BitVec.toNat_add c0_hi_a2b0 c0_c2
  have h_c1_lo : c1_lo.toNat = (a0.toNat * b1.toNat) % 2^64 :=
      mul_toNat a0 b1
  have h_c1_hi : c1_hi.toNat = (a0.toNat * b1.toNat) / 2^64 :=
      rv64_mulhu_toNat a0 b1
  have h_c1_r1 : c1_r1.toNat = (c0_r1.toNat + c1_lo.toNat) % 2^64 :=
      BitVec.toNat_add c0_r1 c1_lo
  have h_c1_c1 : c1_c1.toNat = (c0_r1.toNat + c1_lo.toNat) / 2^64 :=
      EvmWord.carry_toNat c0_r1 c1_lo
  have h_c1_rc : c1_rc.toNat = (c1_hi.toNat + c1_c1.toNat) % 2^64 :=
      BitVec.toNat_add c1_hi c1_c1
  have h_c1_r2a : c1_r2a.toNat = (c0_r2.toNat + c1_rc.toNat) % 2^64 :=
      BitVec.toNat_add c0_r2 c1_rc
  have h_c1_cr1 : c1_cr1.toNat = (c0_r2.toNat + c1_rc.toNat) / 2^64 :=
      EvmWord.carry_toNat c0_r2 c1_rc
  have h_c1_lo2 : c1_lo2.toNat = (a1.toNat * b1.toNat) % 2^64 :=
      mul_toNat a1 b1
  have h_c1_hi2 : c1_hi2.toNat = (a1.toNat * b1.toNat) / 2^64 :=
      rv64_mulhu_toNat a1 b1
  have h_c1_r2 : c1_r2.toNat = (c1_r2a.toNat + c1_lo2.toNat) % 2^64 :=
      BitVec.toNat_add c1_r2a c1_lo2
  have h_c1_cr2 : c1_cr2.toNat = (c1_r2a.toNat + c1_lo2.toNat) / 2^64 :=
      EvmWord.carry_toNat c1_r2a c1_lo2
  have h_c1_rc2 : c1_rc2.toNat = (c1_hi2.toNat + c1_cr2.toNat) % 2^64 :=
      BitVec.toNat_add c1_hi2 c1_cr2
  have h_c1_r3p : c1_r3p.toNat = ((c1_cr1 + c1_rc2 + a2 * b1).toNat + c0_r3p.toNat) % 2^64 :=
      BitVec.toNat_add (c1_cr1 + c1_rc2 + a2 * b1) c0_r3p
  have h_c2_lo : c2_lo.toNat = (a0.toNat * b2.toNat) % 2^64 :=
      mul_toNat a0 b2
  have h_c2_hi : c2_hi.toNat = (a0.toNat * b2.toNat) / 2^64 :=
      rv64_mulhu_toNat a0 b2
  have h_c2_r2 : c2_r2.toNat = (c1_r2.toNat + c2_lo.toNat) % 2^64 :=
      BitVec.toNat_add c1_r2 c2_lo
  have h_c2_c : c2_c.toNat = (c1_r2.toNat + c2_lo.toNat) / 2^64 :=
      EvmWord.carry_toNat c1_r2 c2_lo
  have h_c2_rc : c2_rc.toNat = ((c2_hi + c2_c).toNat + (a1 * b2).toNat) % 2^64 :=
      BitVec.toNat_add (c2_hi + c2_c) (a1 * b2)
  have h_c2_r3 : c2_r3.toNat = (c1_r3p.toNat + c2_rc.toNat) % 2^64 :=
      BitVec.toNat_add c1_r3p c2_rc
  have h_r3_final : r3_final.toNat = (c2_r3.toNat + (a0 * b3).toNat) % 2^64 :=
      BitVec.toNat_add c2_r3 (a0 * b3)

  have hP : (a * b).toNat = (a.toNat * b.toNat) % 2^256 := BitVec.toNat_mul a b
  -- Use toNat_eq_limb_sum but since a0 := a.getLimb 0 etc., types match
  have ha : a.toNat = a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192 :=
    toNat_eq_limb_sum a
  have hb : b.toNat = b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192 :=
    toNat_eq_limb_sum b
    -- Abbreviate the full product polynomial
  set P := (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192) *
    (b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192)
  have hPdecomp : (a * b).toNat = P % 2^256 := by rw [hP, ha, hb]


  -- limb bounds
  have ha0 := a0.isLt; have hb0 := b0.isLt
  have ha1 := a1.isLt; have hb1 := b1.isLt
  have ha2 := a2.isLt; have hb2 := b2.isLt
  have ha3 := a3.isLt; have hb3 := b3.isLt
   -- getLimb toNat for (a*b) at each index
  have key0 : ((a * b).getLimb 0).toNat = P % 2^256 % 2^64 := by
      simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hPdecomp]; norm_num
  have key1 : ((a * b).getLimb 1).toNat = P % 2^256 / 2^64 % 2^64 := by
      simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hPdecomp]; norm_num
  have key2 : ((a * b).getLimb 2).toNat = P % 2^256 / 2^128 % 2^64 := by
      simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hPdecomp]; norm_num
  have key3 : ((a * b).getLimb 3).toNat = P % 2^256 / 2^192 % 2^64 := by
      simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
        show (3 : Fin 4).val = 3 from rfl]; rw [hPdecomp]

  -- Factor P at each limb boundary using ring, then omega handles div/mod
  set W := (2 : Nat) ^ 64
  have hW : 0 < W := by positivity
  have h128 : (2:Nat)^128 = W * W := by norm_num [W]
  have h192 : (2:Nat)^192 = W * (W * W) := by norm_num [W]
  have h256 : (2:Nat)^256 = W * (W * (W * W)) := by norm_num [W]
  -- Factor P for division at each boundary
  have hP0 : P = (a0.toNat * b0.toNat) +
      ((a0.toNat * b1.toNat + a1.toNat * b0.toNat) +
       (a0.toNat * b2.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat) * W +
       (a0.toNat * b3.toNat + a1.toNat * b2.toNat + a2.toNat * b1.toNat + a3.toNat * b0.toNat) * (W * W) +
       ((a1.toNat * b3.toNat + a2.toNat * b2.toNat + a3.toNat * b1.toNat) +
        (a2.toNat * b3.toNat + a3.toNat * b2.toNat) * W +
        (a3.toNat * b3.toNat) * (W * W)) * (W * (W * W))) * W := by
      simp only [P, h128, h192]; ring
  have hP1 : P = (a0.toNat * b0.toNat) + (a0.toNat * b1.toNat + a1.toNat * b0.toNat) * W +
      ((a0.toNat * b2.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat) +
       (a0.toNat * b3.toNat + a1.toNat * b2.toNat + a2.toNat * b1.toNat + a3.toNat * b0.toNat) * W +
       ((a1.toNat * b3.toNat + a2.toNat * b2.toNat + a3.toNat * b1.toNat) +
        (a2.toNat * b3.toNat + a3.toNat * b2.toNat) * W +
        (a3.toNat * b3.toNat) * (W * W)) * (W * W)) * (W * W) := by
      simp only [P, h128, h192]; ring
  have hP2 : P = (a0.toNat * b0.toNat) + (a0.toNat * b1.toNat + a1.toNat * b0.toNat) * W +
      (a0.toNat * b2.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat) * (W * W) +
      ((a0.toNat * b3.toNat + a1.toNat * b2.toNat + a2.toNat * b1.toNat + a3.toNat * b0.toNat) +
       ((a1.toNat * b3.toNat + a2.toNat * b2.toNat + a3.toNat * b1.toNat) +
        (a2.toNat * b3.toNat + a3.toNat * b2.toNat) * W +
        (a3.toNat * b3.toNat) * (W * W)) * W) * (W * (W * W)) := by
      simp only [P, h128, h192]; ring

   -- Helpers: strip W-multiples from mod W
  have strip4 : ∀ p q r s W, 0 < W →
        (p + (q + r * W + s * (W * W))) % W = (p + q) % W := by
      intro p q r s W hW'
      rw [show p + (q + r * W + s * (W * W)) = (p + q) + (r + s * W) * W from by ring,
          Nat.add_mul_mod_self_right]
  have strip2 : ∀ (p q r W : Nat), (p + (q + r * W)) % W = (p + q) % W := by
      intro p q r W
      rw [show p + (q + r * W) = (p + q) + r * W from by ring, Nat.add_mul_mod_self_right]

  -- Limb 0: P % W^4 % W = (a0*b0) % W — MUL produces the low 64 bits directly
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [key0, h_c0_r0, h256, Nat.mod_mul_right_mod, hP0, Nat.add_mul_mod_self_right]

  -- Limb 1: P/W % W = c1_r1.toNat
  --   Key identity: (a0*b0/W + a0*b1 + a1*b0) mod W = c1_r1.toNat
  --   Proof sketch:
  --   1. Nat.mod_mul_right_div_self to get P / W % W^3 % W
  --   2. Factor P = a0*b0 + (a0*b1 + a1*b0 + ...)*W via hP0
  --   3. Nat.add_mul_div_right to divide out W
  --   4. Strip higher-order terms, leaving (a0*b0/W + a0*b1 + a1*b0) % W
  --   5. Decompose via mul_full_product: a0*b0 = hi*W + lo
  --   6. Match with c1_r1 carry chain via h_c0_r1, h_c1_r1
  constructor
  · sorry

  -- Limb 2: P/W² % W = c2_r2.toNat
  --   The W^2 coefficient of P is (a0*b2 + a1*b1 + a2*b0 + carries from limbs 0-1).
  --   Similar structure to limb 1 but with 2 levels of carry propagation.
  constructor
  · sorry

  -- Limb 3: P/W³ % W = r3_final.toNat
  --   The W^3 coefficient of P is (a0*b3 + a1*b2 + a2*b1 + a3*b0 + carries).
  --   Higher terms (i+j >= 4) vanish mod W^4.
  · sorry

end EvmWord

end EvmAsm.Evm64
