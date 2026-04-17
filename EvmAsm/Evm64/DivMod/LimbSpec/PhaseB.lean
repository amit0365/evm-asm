/-
  EvmAsm.Evm64.DivMod.LimbSpec.PhaseB

  Phase B: init (zero q/u, load b[1..2]), tail (leading-limb load), cascade step.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Phase B init: zero out q[0..3] and u[5..7], load b[1] and b[2].
-- 9 straight-line instructions.
-- ============================================================================

abbrev divK_phaseB_init1_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseB.take 7)

/-- Phase B init part 1: zero scratch q[0..3] and u[5..7]. 7 instructions. -/
theorem divK_phaseB_init1_spec (sp : Word) (base : Word)
    (q0 q1 q2 q3 u5 u6 u7 : Word)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true) :
    let cr := divK_phaseB_init1_code base
    cpsTriple base (base + 28) cr
      (
       (.x12 ↦ᵣ sp) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7))
      (
       (.x12 ↦ᵣ sp) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word))) := by
  have I0 := sd_x0_spec_gen .x12 sp q0 4088 base hv_q0
  have I1 := sd_x0_spec_gen .x12 sp q1 4080 (base + 4) hv_q1
  have I2 := sd_x0_spec_gen .x12 sp q2 4072 (base + 8) hv_q2
  have I3 := sd_x0_spec_gen .x12 sp q3 4064 (base + 12) hv_q3
  have I4 := sd_x0_spec_gen .x12 sp u5 4016 (base + 16) hv_u5
  have I5 := sd_x0_spec_gen .x12 sp u6 4008 (base + 20) hv_u6
  have I6 := sd_x0_spec_gen .x12 sp u7 4000 (base + 24) hv_u7
  runBlock I0 I1 I2 I3 I4 I5 I6

abbrev divK_phaseB_init2_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseB.drop 7 |>.take 2)

/-- Phase B init part 2: load b[1] and b[2]. 2 instructions. -/
theorem divK_phaseB_init2_spec (sp : Word) (base : Word)
    (b1 b2 : Word) (v6 v7 : Word)
    (hvalid : ValidMemRange sp 8) :
    let cr := divK_phaseB_init2_code base
    cpsTriple base (base + 8) cr
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2))
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2)) := by
  have I0 := ld_spec_gen .x6 .x12 sp v6 b1 40 base (by nofun) (by validMem)
  have I1 := ld_spec_gen .x7 .x12 sp v7 b2 48 (base + 4) (by nofun) (by validMem)
  runBlock I0 I1

-- ============================================================================
-- Phase B tail: store n, compute address of b[n-1], load leading limb.
-- 5 instructions: SD, ADDI, SLLI, ADD, LD.
-- ============================================================================

abbrev divK_phaseB_tail_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseB.drop 16)

/-- Phase B tail: store n to scratch, compute sp + (n-1)*8, load b[n-1].
    x5 = n on entry. On exit, x5 = leading limb b[n-1]. -/
theorem divK_phaseB_tail_spec (sp n leading_limb n_mem : Word) (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_limb : isValidDwordAccess
      ((sp + ((n + signExtend12 4095) <<< (3 : BitVec 6).toNat)) + signExtend12 32) = true) :
    let nm1 := n + signExtend12 4095
    let nm1_x8 := nm1 <<< (3 : BitVec 6).toNat
    let addr_lead := sp + nm1_x8
    let cr := divK_phaseB_tail_code base
    cpsTriple base (base + 20) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
       ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((addr_lead + signExtend12 32) ↦ₘ leading_limb))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ leading_limb) **
       ((sp + signExtend12 3984) ↦ₘ n) **
       ((addr_lead + signExtend12 32) ↦ₘ leading_limb)) := by
  intro nm1 nm1_x8 addr_lead cr
  have I0 := sd_spec_gen .x12 .x5 sp n n_mem 3984 base hv_n
  have I1 := addi_spec_gen_same .x5 n 4095 (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x5 nm1 3 (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs2 .x5 .x12 sp nm1_x8 (base + 12) (by nofun)
  have I4 := ld_spec_gen_same .x5 addr_lead leading_limb 32 (base + 16) (by nofun) hv_limb
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Phase B cascade step: ADDI x5 n_val + BNE rx x0 offset. cpsBranch.
-- Used for each "if b[k]≠0 → n=k" step in the n-computation cascade.
-- ============================================================================

abbrev divK_phaseB_cascade_step_code (n_val : BitVec 12) (rx : Reg) (bne_off : BitVec 13)
    (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x5 .x0 n_val))
   (CodeReq.singleton (base + 4) (.BNE rx .x0 bne_off))

/-- Single cascade step: load n_val into x5, then BNE on rx vs x0.
    Taken: rx ≠ 0 (limb is nonzero), branch to target with x5 = n_val.
    Not taken: rx = 0, fall through with x5 = n_val. -/
theorem divK_phaseB_cascade_step_spec (n_val : BitVec 12) (rx : Reg) (check v5 : Word)
    (bne_off : BitVec 13) (base : Word) :
    let n := (0 : Word) + signExtend12 n_val
    let cr := divK_phaseB_cascade_step_code n_val rx bne_off base
    let post :=
      (.x5 ↦ᵣ n) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check)
    cpsBranch base cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check))
      -- Taken: check ≠ 0
      ((base + 4) + signExtend13 bne_off) post
      -- Not taken: check = 0
      (base + 8) post := by
  intro n cr post
  -- 1. ADDI body
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check))
      ((.x5 ↦ᵣ n) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check)) := by
    have I0 := addi_spec_gen .x5 .x0 v5 (0 : Word) n_val base (by nofun)
    runBlock I0
  -- 2. BNE at base + 4, drop pure facts
  have hbne_raw := bne_spec_gen rx .x0 bne_off check (0 : Word) (base + 4)
  have ha1 : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha1] at hbne_raw
  have hbne : cpsBranch (base + 4) _
      ((rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 4) + signExtend13 bne_off)
        ((rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 8)
        ((rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      hbne_raw
  -- 3. Frame BNE with x5
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    (.x5 ↦ᵣ n)
    (by pcFree) hbne
  -- 4. Extend to full cr
  have hbne_ext := cpsBranch_extend_code (cr' := cr) (fun a i h => by
    simp only [CodeReq.singleton] at h
    split at h
    · next heq =>
      rw [beq_iff_eq] at heq; subst heq
      simp only [Option.some.injEq] at h; subst h
      show divK_phaseB_cascade_step_code n_val rx bne_off base (base + 4) = _
      simp only [divK_phaseB_cascade_step_code, CodeReq.union, CodeReq.singleton]
      have h0 : ¬(base + 4 = base) := by bv_omega
      simp only [beq_iff_eq, h0, ↓reduceIte]
    · simp at h) hbne_framed
  -- 5. Compose
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  exact cpsBranch_consequence _ _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

end EvmAsm.Evm64
