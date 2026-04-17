/-
  EvmAsm.Evm64.DivMod.LimbSpec.Branch

  Branch / loop-control helpers: store q[j] (singleton + composed), loop-control j--/BGE, trial quotient loads (u, vtop, MAX, composed).
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
-- Store q[j]: 4 instructions.
-- ============================================================================

/-- Store q[j]: compute &q[j] = sp+4088 - j*8, store q_hat.
    First 3 instructions compute q_addr. Then SD stores. Split into 3+1. -/
theorem divK_store_qj_addr_spec (sp j v5_old v7_old : Word)
    (base : Word) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let sp_m8 := sp + signExtend12 4088
    let q_addr := sp_m8 - j_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x7 .x12 4088))
       (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5)))
    cpsTriple base (base + 12) cr
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr)) := by
  intro j_x8 sp_m8 q_addr cr
  have I0 := slli_spec_gen .x5 .x1 v5_old j 3 base (by nofun)
  have I1 := addi_spec_gen .x7 .x12 v7_old sp 4088 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 sp_m8 j_x8 (base + 8) (by nofun)
  runBlock I0 I1 I2

/-- Store q[j]: SD q_hat at q_addr. 1 instruction. -/
theorem divK_store_qj_write_spec (q_addr q_hat q_old : Word) (base : Word)
    (hv : isValidDwordAccess q_addr = true) :
    let cr := CodeReq.singleton base (.SD .x7 .x11 0)
    cpsTriple base (base + 4) cr
      ((.x7 ↦ᵣ q_addr) ** (.x11 ↦ᵣ q_hat) ** (q_addr ↦ₘ q_old))
      ((.x7 ↦ᵣ q_addr) ** (.x11 ↦ᵣ q_hat) ** (q_addr ↦ₘ q_hat)) := by
  intro cr
  have hse : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr : q_addr + signExtend12 (0 : BitVec 12) = q_addr := by rw [hse]; bv_omega
  have hv' : isValidDwordAccess (q_addr + signExtend12 0) = true := by rw [haddr]; exact hv
  have I0 := sd_spec_gen .x7 .x11 q_addr q_hat q_old 0 base hv'
  rw [haddr] at I0
  runBlock I0

-- ============================================================================
-- Loop control: j-- and BGE loop back.
-- 2 instructions: ADDI + BGE.
-- ============================================================================

set_option maxRecDepth 1024 in
/-- Loop control: decrement j and branch back if j >= 0. -/
theorem divK_loop_control_spec (j : Word) (loop_back_off : BitVec 13)
    (base : Word) :
    let j' := j + signExtend12 4095
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADDI .x1 .x1 4095))
       (CodeReq.singleton (base + 4) (.BGE .x1 .x0 loop_back_off))
    cpsBranch base cr
      ((.x1 ↦ᵣ j) ** (.x0 ↦ᵣ 0))
      (base + 4 + signExtend13 loop_back_off)
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      (base + 8)
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) := by
  intro j' cr
  -- 1. ADDI body
  have hbody : cpsTriple base (base + 4) cr
      ((.x1 ↦ᵣ j) ** (.x0 ↦ᵣ 0))
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) := by
    have I0 := addi_spec_gen_same .x1 j 4095 base (by nofun)
    runBlock I0
  -- 2. BGE, drop pure facts
  have hbge_raw := bge_spec_gen .x1 .x0 loop_back_off j' 0 (base + 4)
  have ha1 : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha1] at hbge_raw
  have hbge : cpsBranch (base + 4) _
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      ((base + 4) + signExtend13 loop_back_off)
        ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      (base + 8)
        ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) :=
    cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      hbge_raw
  -- 3. Extend BGE to full cr
  have hbge_ext : cpsBranch (base + 4) cr
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      ((base + 4) + signExtend13 loop_back_off) ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      (base + 8) ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) :=
    fun R hR s hcr hPR hpc =>
      hbge R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show CodeReq.union (CodeReq.singleton base (.ADDI .x1 .x1 4095))
          (CodeReq.singleton (base + 4) (.BGE .x1 .x0 loop_back_off)) (base + 4) = _
        simp only [CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  -- 4. Compose
  exact cpsTriple_seq_cpsBranch_same_cr _ _ _ _ _ _ _ _ _ hbody hbge_ext
-- ============================================================================
-- Trial quotient: load u[j+n], u[j+n-1].
-- 7 instructions: LD + ADD + SLLI + ADDI + SUB + LD + LD.
-- ============================================================================

/-- Load u_hi = u[j+n] and u_lo = u[j+n-1] for trial quotient estimation.
    u_addr = sp + signExtend12 4056 - (j + n) <<< 3.
    u_hi = mem[u_addr], u_lo = mem[u_addr + 8]. -/
theorem divK_trial_load_u_spec (sp j n v5_old v7_old u_hi u_lo : Word)
    (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true) :
    let jpn := j + n
    let jpn_x8 := jpn <<< (3 : BitVec 6).toNat
    let u0_base := sp + signExtend12 4056
    let u_addr := u0_base - jpn_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x7 .x1 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x7 .x7 3))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADDI .x5 .x12 4056))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x5 0))
       (CodeReq.singleton (base + 24) (.LD .x5 .x5 8)))))))
    cpsTriple base (base + 28) cr
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x7 ↦ᵣ u_hi) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo)) := by
  intro jpn jpn_x8 u0_base u_addr cr
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr0 : u_addr + signExtend12 (0 : BitVec 12) = u_addr := by rw [hse0]; bv_omega
  have hv_uhi' : isValidDwordAccess (u_addr + signExtend12 0) = true := by rw [haddr0]; exact hv_uhi
  have I0 := ld_spec_gen .x5 .x12 sp v5_old n 3984 base (by nofun) hv_n
  have I1 := add_spec_gen .x7 .x1 .x5 j n v7_old (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x7 jpn 3 (base + 8) (by nofun)
  have I3 := addi_spec_gen .x5 .x12 n sp 4056 (base + 12) (by nofun)
  have I4 := sub_spec_gen_rd_eq_rs1 .x5 .x7 u0_base jpn_x8 (base + 16) (by nofun)
  have I5 := ld_spec_gen .x7 .x5 u_addr jpn_x8 u_hi 0 (base + 20) (by nofun) hv_uhi'
  rw [haddr0] at I5
  have I6 := ld_spec_gen_same .x5 u_addr u_lo 8 (base + 24) (by nofun) hv_ulo
  runBlock I0 I1 I2 I3 I4 I5 I6

-- ============================================================================
-- Trial quotient: load v_top = b[n-1].
-- 5 instructions: LD + ADDI + SLLI + ADD + LD.
-- ============================================================================

/-- Load v_top = b[n-1] for trial quotient estimation.
    vtop_addr = sp + (n + signExtend12 4095) <<< 3.
    v_top = mem[vtop_addr + 32]. -/
theorem divK_trial_load_vtop_spec (sp n v6_old v10_old v_top : Word)
    (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true) :
    let nm1 := n + signExtend12 4095
    let nm1_x8 := nm1 <<< (3 : BitVec 6).toNat
    let vtop_base := sp + nm1_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x6 .x6 4095))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x6 .x6 3))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x6 .x12 .x6))
       (CodeReq.singleton (base + 16) (.LD .x10 .x6 32)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6_old) ** (.x10 ↦ᵣ v10_old) **
       (sp + signExtend12 3984 ↦ₘ n) ** (vtop_base + signExtend12 32 ↦ₘ v_top))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ vtop_base) ** (.x10 ↦ᵣ v_top) **
       (sp + signExtend12 3984 ↦ₘ n) ** (vtop_base + signExtend12 32 ↦ₘ v_top)) := by
  intro nm1 nm1_x8 vtop_base cr
  have I0 := ld_spec_gen .x6 .x12 sp v6_old n 3984 base (by nofun) hv_n
  have I1 := addi_spec_gen_same .x6 n 4095 (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x6 nm1 3 (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs2 .x6 .x12 sp nm1_x8 (base + 12) (by nofun)
  have I4 := ld_spec_gen .x10 .x6 vtop_base v10_old v_top 32 (base + 16) (by nofun) hv_vtop
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Trial quotient: MAX path (u_hi >= v_top).
-- 2 instructions: ADDI x11 x0 4095 + JAL x0 8.
-- ============================================================================

/-- Trial quotient MAX path: set q_hat = MAX64, jump over div128 call. -/
theorem divK_trial_max_spec (v11_old : Word) (base : Word) :
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADDI .x11 .x0 4095))
       (CodeReq.singleton (base + 4) (.JAL .x0 8))
    cpsTriple base (base + 12) cr
      ((.x11 ↦ᵣ v11_old) ** (.x0 ↦ᵣ 0))
      ((.x11 ↦ᵣ signExtend12 4095) ** (.x0 ↦ᵣ 0)) := by
  intro cr
  have hj : signExtend21 (8 : BitVec 21) = (8 : Word) := by decide
  have I0 := addi_x0_spec_gen .x11 v11_old 4095 base (by nofun)
  have I1 := jal_x0_spec_gen 8 (base + 4)
  rw [hj] at I1
  have ha : (base + 4 : Word) + 8 = base + 12 := by bv_addr
  rw [ha] at I1
  runBlock I0 I1

-- ============================================================================
-- Trial quotient load phase: load u[j+n], u[j+n-1], v_top = b[n-1].
-- trial_load_u [1]-[7] + trial_load_vtop [8]-[12] = 12 instructions.
-- ============================================================================

set_option maxRecDepth 2048 in
/-- Trial quotient load: fetch u_hi, u_lo, v_top from memory.
    Instrs [1]-[12] of loop body.
    Output: x7 = u_hi, x5 = u_lo, x10 = v_top, x6 = vtop_base. -/
theorem divK_trial_load_spec
    (sp j n v5_old v6_old v7_old v10_old u_hi u_lo v_top : Word)
    (base : Word)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true) :
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x7 .x1 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x7 .x7 3))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADDI .x5 .x12 4056))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x5 0))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x6 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 32) (.ADDI .x6 .x6 4095))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x6 .x6 3))
      (CodeReq.union (CodeReq.singleton (base + 40) (.ADD .x6 .x12 .x6))
       (CodeReq.singleton (base + 44) (.LD .x10 .x6 32))))))))))))
    cpsTriple base (base + 48) cr
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtop_base) **
       (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top)) := by
  intro u_addr vtop_base cr
  -- Instructions from trial_load_u (7 instrs at base)
  let jpn := j + n
  let jpn_x8 := jpn <<< (3 : BitVec 6).toNat
  let u0_base := sp + signExtend12 4056
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr0 : u_addr + signExtend12 (0 : BitVec 12) = u_addr := by rw [hse0]; bv_omega
  have hv_uhi' : isValidDwordAccess (u_addr + signExtend12 0) = true := by rw [haddr0]; exact hv_uhi
  have I0 := ld_spec_gen .x5 .x12 sp v5_old n 3984 base (by nofun) hv_n1
  have I1 := add_spec_gen .x7 .x1 .x5 j n v7_old (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x7 jpn 3 (base + 8) (by nofun)
  have I3 := addi_spec_gen .x5 .x12 n sp 4056 (base + 12) (by nofun)
  have I4 := sub_spec_gen_rd_eq_rs1 .x5 .x7 u0_base jpn_x8 (base + 16) (by nofun)
  have I5 := ld_spec_gen .x7 .x5 u_addr jpn_x8 u_hi 0 (base + 20) (by nofun) hv_uhi'
  rw [haddr0] at I5
  have I6 := ld_spec_gen_same .x5 u_addr u_lo 8 (base + 24) (by nofun) hv_ulo
  -- Instructions from trial_load_vtop (5 instrs at base+28)
  let nm1 := n + signExtend12 4095
  let nm1_x8 := nm1 <<< (3 : BitVec 6).toNat
  have I7 := ld_spec_gen .x6 .x12 sp v6_old n 3984 (base + 28) (by nofun) hv_n1
  have I8 := addi_spec_gen_same .x6 n 4095 (base + 32) (by nofun)
  have I9 := slli_spec_gen_same .x6 nm1 3 (base + 36) (by nofun)
  have I10 := add_spec_gen_rd_eq_rs2 .x6 .x12 sp nm1_x8 (base + 40) (by nofun)
  have I11 := ld_spec_gen .x10 .x6 vtop_base v10_old v_top 32 (base + 44) (by nofun) hv_vtop
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11
-- ============================================================================
-- Composed store q[j]: addr computation + SD = 4 instructions.
-- ============================================================================

set_option maxRecDepth 2048 in
/-- Store q[j]: compute address and store q_hat. 4 instructions.
    q_addr = sp + 4088 - j*8. -/
theorem divK_store_qj_spec (sp j q_hat v5_old v7_old q_old : Word)
    (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - j_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x7 .x12 4088))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
       (CodeReq.singleton (base + 12) (.SD .x7 .x11 0))))
    cpsTriple base (base + 16) cr
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (q_addr ↦ₘ q_old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr) **
       (q_addr ↦ₘ q_hat)) := by
  intro j_x8 q_addr cr
  -- Instructions from store_qj_addr (3 instrs at base)
  have I0 := slli_spec_gen .x5 .x1 v5_old j 3 base (by nofun)
  have I1 := addi_spec_gen .x7 .x12 v7_old sp 4088 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 (sp + signExtend12 4088) j_x8 (base + 8) (by nofun)
  -- SD instruction with signExtend12 normalization
  have hse : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr : q_addr + signExtend12 (0 : BitVec 12) = q_addr := by rw [hse]; bv_omega
  have hv' : isValidDwordAccess (q_addr + signExtend12 0) = true := by rw [haddr]; exact hv
  have I3 := sd_spec_gen .x7 .x11 q_addr q_hat q_old 0 (base + 12) hv'
  rw [haddr] at I3
  runBlock I0 I1 I2 I3

end EvmAsm.Evm64
