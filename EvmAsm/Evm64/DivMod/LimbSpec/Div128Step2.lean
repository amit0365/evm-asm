/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2

  Full-step composition for instrs [30]-[46] of the `div128` subroutine —
  combining step-2-init (DIVU+MUL+SUB), clamp-q0 (SRLI+BEQ+ADDI+ADD),
  Phase 2b guard (SRLI+BNE — Knuth TAOCP §4.3.1 Step D3), and prodcheck2
  (LD+MUL+SLLI+LD+OR + BLTU+JAL + ADDI) into a single refined `q0`
  computation for the low 64 bits.

  Thirtieth chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the
  spec.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Clamp
import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Tail
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- div128 step 2 upto-guard: init + clamp_q0 composition for instrs [30]-[36].
    Output at base+28 with x5=q0c, x11=rhat2c, x1=hi ready for the Phase 2b
    guard to consume.

    Note: proof pattern matches the pre-guard (main-branch) step2_spec's first
    two sub-specs; this sub-lemma exists so the full `divK_div128_step2_spec`
    can compose it with the new `phase2b_guard_spec` + `prodcheck2_merged_spec`
    without re-stating the init/clamp code subsumption every time. -/
theorem divK_div128_step2_upto_guard_spec
    (sp un21 dHi v1Old v5Old v11Old dlo un0 : Word) (base : Word) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
       (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6)))))))
    cpsTriple base (base + 28) cr
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
       (.x1 ↦ᵣ hi) ** (.x11 ↦ᵣ rhat2c) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0 rhat2 hi q0c rhat2c cr
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
       (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))))))) := rfl
  have h1_raw := divK_div128_step2_init_spec un21 dHi v1Old v5Old v11Old base
  have h1 : cpsTriple base (base + 12) cr _ _ :=
    cpsTriple_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]; exact CodeReq.union_mono_tail (CodeReq.union_mono_tail
        (CodeReq.union_mono_left _ _)))
  have h1f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h1
  have h2_raw := divK_div128_clamp_q0_merged_spec q0 rhat2 dHi (q0 * dHi) (base + 12)
  have ha4 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  have ha8 : (base + 12 : Word) + 8 = base + 20 := by bv_addr
  have ha12 : (base + 12 : Word) + 12 = base + 24 := by bv_addr
  have ha16 : (base + 12 : Word) + 16 = base + 28 := by bv_addr
  simp only [ha4, ha8, ha12, ha16] at h2_raw
  have h2 : cpsTriple (base + 12) (base + 28) cr _ _ :=
    cpsTriple_extend_code (h := h2_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · simp at h)
  have h2f := cpsTriple_frameR
    ((.x7 ↦ᵣ un21) ** (.x12 ↦ᵣ sp) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h2
  have h12 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1f h2f
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    h12

/-- div128 step 2: trial division q0, clamp, Phase 2b guard, product check.
    Instrs [30]-[46] (17 instructions). Includes the Knuth TAOCP §4.3.1
    Step D3 guard (SRLI + BNE at instrs [37]-[38]) that skips the
    product check when `rhat2c >= 2^32`.

    Input: un21 in x7, dHi in x6, dlo/un0 in memory.
    Output: refined q0 in x5 (= `div128Quot_phase2b_q0' q0c rhat2c dlo un0`).

    **NOTE**: output's x7, x1, x11 values differ between guard-fires and
    guard-doesn't-fire paths:
    - Guard fires (rhat2c_hi ≠ 0): x7 = un21 (unchanged), x1 = rhat2c_hi,
      x11 = rhat2c.
    - Guard doesn't fire (rhat2c_hi = 0): x7 = q0Dlo, x1 = rhat2Un0,
      x11 = un0.

    The postcondition uses `rhat2c_hi = 0`-aware selectors to capture this. -/
theorem divK_div128_step2_spec
    (sp un21 dHi v1Old v5Old v11Old dlo un0 : Word) (base : Word) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
    let q0Dlo := q0c * dlo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let rhat2c_hi := rhat2c >>> (32 : BitVec 6).toNat
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
    -- Exit values for registers that differ between guard-fires/doesn't
    -- paths. On guard-fires: x7 keeps un21 (MUL not run), x1 keeps
    -- rhat2c_hi (loaded by SRLI), x11 keeps rhat2c (un0 not loaded).
    -- On guard-doesn't-fire: x7 holds q0Dlo, x1 holds rhat2Un0, x11 holds un0.
    let x7_exit := if rhat2c_hi = 0 then q0Dlo else un21
    let x1_exit := if rhat2c_hi = 0 then rhat2Un0 else rhat2c_hi
    let x11_exit := if rhat2c_hi = 0 then un0 else rhat2c
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SRLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 32) (.BNE .x1 .x0 36))
      (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 40) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 44) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 56) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 60) (.JAL .x0 8))
       (CodeReq.singleton (base + 64) (.ADDI .x5 .x5 4095)))))))))))))))))
    cpsTriple base (base + 68) cr
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x7 ↦ᵣ x7_exit) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
       (.x1 ↦ᵣ x1_exit) ** (.x11 ↦ᵣ x11_exit) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0 rhat2 hi q0c rhat2c q0Dlo rhat2Un0 rhat2c_hi q0' x7_exit x1_exit x11_exit cr
  -- TODO(#61 Phase 2b coordinated fix, iteration 2026-04-23):
  -- `divK_div128_step2_upto_guard_spec` above covers the base..base+28 section
  -- (cleanly replacing the old step2 pattern). Remaining composition:
  --   h1 = divK_div128_step2_upto_guard_spec (cpsTriple base..base+28) ✓ available
  --   h2 = phase2b_guard_spec at base+28 (cpsBranch → base+68 | base+36)
  --   h3 = prodcheck2_merged_spec at base+36 (cpsTriple base+36..base+68)
  --   compose h1+h2 via cpsTriple_seq_cpsBranch_perm_same_cr
  --   compose + h3 via cpsBranch_seq_cpsTriple_with_perm_same_cr
  --   merge via cpsBranch_merge_same_cr with cpsTriple_refl bridges
  -- Empirical finding: attempting the full composition in one elab step
  -- times out at maxHeartbeats (200000) at the first cpsTriple_seq_cpsBranch
  -- xperm_hyp call (too many atoms to permute). Next iteration needs to
  -- factor the composition into additional intermediate sub-lemmas to split
  -- the elaboration cost.
  sorry

end EvmAsm.Evm64
