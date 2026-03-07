/-
  EvmAsm.Tactics.RunBlock

  Multi-instruction block composition with automatic address normalization.

  `runBlock s1 s2 ... sN` composes N cpsTriple hypotheses by:
  1. Framing the first spec against the goal's full precondition
  2. Normalizing addresses between consecutive specs via bv_omega
  3. Applying seqFrame for each consecutive pair
  4. Closing the goal with postcondition permutation
-/

import Lean
import EvmAsm.Tactics.SeqFrame

open Lean Meta Elab Tactic

namespace EvmAsm.Tactics

/-- Inline all leading `let` bindings and strip metadata wrappers.
    Handles `Expr.mdata`, `Expr.letE`, and `letFun v (fun x => body)` patterns. -/
private partial def inlineLets : Expr → Expr
  | .mdata _ e => inlineLets e
  | .letE _ _ val body _ => inlineLets (body.instantiate1 val)
  | e =>
    -- Check for letFun v (fun x => body) pattern
    if e.isAppOfArity ``letFun 4 then
      let f := e.getAppArgs[3]!
      let v := e.getAppArgs[2]!
      match f with
      | .lam _ _ body _ => inlineLets (body.instantiate1 v)
      | _ => e
    else e

/-- Normalize the exit address of a cpsTriple proof to match a target address.
    Proves equality via `bv_omega` when needed. -/
private def normalizeAddr (accExpr : Expr) (targetExit : Expr) : MetaM Expr := do
  let accType ← inferType accExpr
  let some (entry, exit₁, P, Q) ← parseCpsTriple? accType
    | throwError "runBlock: not a cpsTriple"
  if ← withoutModifyingState (isDefEq exit₁ targetExit) then
    return accExpr
  let eqType ← mkEq exit₁ targetExit
  let eqMVar ← mkFreshExprMVar eqType
  try
    let stx ← `(tactic| bv_omega)
    let _ ← Lean.Elab.runTactic eqMVar.mvarId! stx
  catch _ =>
    throwError "runBlock: cannot prove address equality:\n  {exit₁} = {targetExit}"
  let eqProof ← instantiateMVars eqMVar
  let addrType ← inferType exit₁
  withLocalDeclD `x addrType fun x => do
    let body := mkAppN (mkConst ``EvmAsm.cpsTriple) #[entry, x, P, Q]
    let motive ← mkLambdaFVars #[x] body
    let congrProof ← mkCongrArg motive eqProof
    mkEqMP congrProof accExpr

/-- Frame the first spec against the goal precondition and permute.
    Given s1 : cpsTriple entry exit P1 Q1 and goalPre (the goal's precondition),
    returns : cpsTriple entry exit goalPre (Q1 ** Frame) where Frame = goalPre \ P1. -/
private def frameFirstSpec (s1Expr : Expr) (goalPre : Expr) : MetaM Expr := do
  let s1Type ← inferType s1Expr
  let some (entry, exit_, preP1, postQ1) ← parseCpsTriple? s1Type
    | throwError "runBlock: first spec is not a cpsTriple"
  -- Compute frame: goalPre atoms not in P1
  let frameAtoms ← computeFrame goalPre preP1
  if frameAtoms.isEmpty then
    -- No frame needed, just permute precondition
    -- cpsTriple_consequence (P P' Q Q') (hpre : P' → P) (hpost : Q → Q') (h : cpsTriple P Q) : cpsTriple P' Q'
    -- P = preP1 (from s1), P' = goalPre (what we want), hpre : goalPre → preP1
    let prePermProof ← mkPermLambda goalPre preP1
    let postIdProof ← mkIdLambda postQ1
    return mkAppN (mkConst ``EvmAsm.cpsTriple_consequence)
      #[entry, exit_, preP1, goalPre, postQ1, postQ1, prePermProof, postIdProof, s1Expr]
  -- Build frame expression
  let frameExpr ← buildSepConjChain frameAtoms
  -- Prove pcFree for the frame
  let pcFreeType := mkApp (mkConst ``EvmAsm.Assertion.pcFree) frameExpr
  let pcFreeMVar ← mkFreshExprMVar pcFreeType
  try
    let stx ← `(tactic| pcFree)
    let _ ← Lean.Elab.runTactic pcFreeMVar.mvarId! stx
  catch _ =>
    throwError "runBlock: could not prove pcFree for initial frame:\n  {frameExpr}"
  let pcFreeProof ← instantiateMVars pcFreeMVar
  -- Frame s1: cpsTriple entry exit (P1 ** F) (Q1 ** F)
  let s1Framed := mkAppN (mkConst ``EvmAsm.cpsTriple_frame_left)
    #[entry, exit_, preP1, postQ1, frameExpr, pcFreeProof, s1Expr]
  -- Permute precondition: goalPre → (P1 ** F)
  let p1StarFrame := mkApp2 (mkConst ``EvmAsm.sepConj) preP1 frameExpr
  -- cpsTriple_consequence (P P' Q Q') (hpre : P' → P) (hpost : Q → Q') (h : cpsTriple P Q) : cpsTriple P' Q'
  -- P = p1StarFrame (from s1Framed), P' = goalPre, hpre : goalPre → p1StarFrame
  let prePermProof ← mkPermLambda goalPre p1StarFrame
  let q1StarFrame := mkApp2 (mkConst ``EvmAsm.sepConj) postQ1 frameExpr
  let postIdProof ← mkIdLambda q1StarFrame
  return mkAppN (mkConst ``EvmAsm.cpsTriple_consequence)
    #[entry, exit_, p1StarFrame, goalPre, q1StarFrame, q1StarFrame,
      prePermProof, postIdProof, s1Framed]

/-- Core: compose an array of cpsTriple proofs with initial framing,
    address normalization, and seqFrame chaining. -/
private def runBlockCore (specs : Array Expr) (goalPre : Expr) : MetaM Expr := do
  if specs.size == 0 then
    throwError "runBlock: no specs provided"
  -- Frame the first spec against the goal precondition
  let mut acc ← frameFirstSpec specs[0]! goalPre
  -- Chain remaining specs via seqFrame with address normalization
  for i in [1:specs.size] do
    let nextSpec := specs[i]!
    let nextType ← inferType nextSpec
    let some (nextEntry, _, _, _) ← parseCpsTriple? nextType
      | throwError "runBlock: argument {i + 1} is not a cpsTriple"
    acc ← normalizeAddr acc nextEntry
    acc ← seqFrameCore acc nextSpec
  return acc

/-- Try to normalize a cpsTriple's exit to match the goal's exit address. -/
private def normalizeToGoal (composed : Expr) (goalType : Expr) : MetaM Expr := do
  if let some (_, goalExit, _, _) ← parseCpsTriple? goalType then
    try return ← normalizeAddr composed goalExit catch _ => return composed
  return composed

/-- `runBlock s1 s2 ... sN` composes N cpsTriple specs with automatic
    address normalization and frame extraction. -/
elab "runBlock" specs:ident* : tactic => withMainContext do
  let specExprs ← specs.mapM fun s => elabTerm s none
  let goal ← getMainGoal
  -- Strip leading let bindings and metadata from goal type
  let goalType := inlineLets (← instantiateMVars (← goal.getType))
  let some (_, _, goalPre, _) ← parseCpsTriple? goalType
    | throwError "runBlock: goal is not a cpsTriple"
  let composed ← runBlockCore specExprs goalPre
  let finalResult ← normalizeToGoal composed goalType
  -- Always permute postcondition to match goal (goal.assign doesn't type-check)
  let some (gEntry, gExit, gPre, goalPost) ← parseCpsTriple? goalType
    | throwError "runBlock: goal is not a cpsTriple (postcondition permutation)"
  let resultType ← inferType finalResult
  let some (_, _, _, resultPost) ← parseCpsTriple? resultType
    | throwError "runBlock: result is not a cpsTriple (internal error)"
  -- cpsTriple_consequence (P P' Q Q') (hpre : P' → P) (hpost : Q → Q') (h : cpsTriple P Q) : cpsTriple P' Q'
  -- P = gPre (what finalResult has), P' = gPre (same, identity), Q = resultPost, Q' = goalPost
  let postPerm ← mkPermLambda resultPost goalPost
  let idPre ← mkIdLambda gPre
  let permuted := mkAppN (mkConst ``EvmAsm.cpsTriple_consequence)
    #[gEntry, gExit, gPre, gPre, resultPost, goalPost, idPre, postPerm, finalResult]
  goal.assign permuted
  replaceMainGoal []

end EvmAsm.Tactics
