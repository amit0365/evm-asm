/-
  EvmAsm.Evm64.DivMod.Compose.FullPath

  Full path merging: compose PhaseAB → CLZ → PhaseC2 → NormB → NormA → LoopSetup
  into end-to-end specs for the b≠0 non-zero path.

  Start with the n=4 (b[3]≠0, shift≠0) case as the primary composition.
-/

import EvmAsm.Evm64.DivMod.Compose.PhaseAB
import EvmAsm.Evm64.DivMod.Compose.CLZ
import EvmAsm.Evm64.DivMod.Compose.Norm
import EvmAsm.Evm64.DivMod.Compose.NormA

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Phase AB(n=4) → CLZ composition: base → base+212
-- ============================================================================

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 4096 in
/-- PhaseAB(n=4) + CLZ: b≠0, b[3]≠0.
    base → base+212. After CLZ, x6 = shift count, x5 = shifted leading limb. -/
theorem evm_div_phaseAB_n4_clz_spec (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 n_mem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true) :
    cpsTriple base (base + 212) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b3).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b3).1) ** (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  -- Phase AB(n=4): base → base+116
  have hAB := evm_div_phaseAB_n4_spec sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 n_mem hbnz hb3nz hvalid hv_q0 hv_q1 hv_q2 hv_q3 hv_u5 hv_u6 hv_u7 hv_n
  -- CLZ: base+116 → base+212, needs x5=b3 (leading limb), x6=b1, x7=b2
  have hCLZ := divK_clz_spec b3 b1 b2 base
  -- Frame CLZ with x12, x10, and all memory atoms
  have hCLZf := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)))
    (by pcFree) hCLZ
  -- Compose AB → CLZ
  have hABCLZ := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hAB hCLZf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hABCLZ

-- ============================================================================
-- PhaseAB(n=4) → CLZ → PhaseC2(ntaken) → NormB: base → base+312
-- ============================================================================

set_option maxHeartbeats 25600000 in
set_option maxRecDepth 4096 in
/-- PhaseAB(n=4) + CLZ + PhaseC2(shift≠0) + NormB: full normalization path.
    base → base+312. b[0..3] normalized in-place. -/
theorem evm_div_n4_to_normB_spec (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 n_mem shift_mem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true) :
    let shift := (clzResult b3).1
    let anti_shift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    cpsTriple base (base + 312) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ (b0 >>> (anti_shift.toNat % 64))) **
       (.x2 ↦ᵣ anti_shift) **
       ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  intro shift anti_shift b3' b2' b1' b0'
  -- Step 1: PhaseAB(n=4) + CLZ (base → base+212)
  have hABCLZ := evm_div_phaseAB_n4_clz_spec sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 n_mem hbnz hb3nz hvalid hv_q0 hv_q1 hv_q2 hv_q3 hv_u5 hv_u6 hv_u7 hv_n
  -- Frame AB+CLZ with x2 and shift_mem (not touched by AB or CLZ)
  have hABCLZf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     ((sp + signExtend12 3992) ↦ₘ shift_mem))
    (by pcFree) hABCLZ
  -- Step 2: PhaseC2 ntaken (base+212 → base+228)
  -- shift = (clzResult b3).1, need shift ≠ 0
  have hC2 := divK_phaseC2_ntaken_spec sp shift ((clzResult b3).2 >>> (63 : Nat))
    shift_mem base hv_shift hshift_nz
  -- Frame C2 with x5, x10, and all other memory
  have hC2f := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ (clzResult b3).2) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)))
    (by pcFree) hC2
  -- Compose AB+CLZ → C2
  have hABC2 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hABCLZf hC2f
  -- Step 3: NormB (base+228 → base+312)
  have hNB := divK_normB_full_spec sp b0 b1 b2 b3
    (clzResult b3).2 ((clzResult b3).2 >>> (63 : Nat))
    shift anti_shift base hvalid
  intro_lets at hNB
  -- Frame NormB with x10, x0, and non-b[] memory
  have hNBf := cpsTriple_frame_left _ _ _ _ _
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNB
  -- Compose AB+CLZ+C2 → NormB
  have hFull := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hABC2 hNBf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Rv64
