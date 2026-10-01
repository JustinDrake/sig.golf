import SigGolfCandidate.AlternativeSignAlgorithms

set_option profiler true
set_option profiler.threshold 1000
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace SigGolfCandidate.Base4Candidate.Reference
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal
open SigGolfCandidate.Ref (Val zeros byte le32 slice answerBytes)

def recoverLayerP (idx lay : Nat) (digits : List Nat) (op : LayerOpening) (padding : List Val) :
    OracleComp HashSpec Val := do
  let (e, tree) := route idx lay
  let ends ← (List.range 62).foldlM (fun out i => do
    let digit := digits.getD i 0
    let v ← walkP lay tree e i (digit+1) (3-digit)
      (padding.getD (62 * lay + i) (zeros 32)) (op.values.getD i [])
    pure (out ++ [v])) []
  let leaf ← h16 (input 2 lay tree 0 e ends.flatten)
  foldPath (treeNode lay tree) e leaf op.siblings

def recoverLayer (idx lay : Nat) (digits : List Nat) (op : LayerOpening) :
    OracleComp HashSpec Val := recoverLayerP idx lay digits op []

def shapeOK (sig : Signature) : Bool :=
  sig.randomness.length == 16 && sig.forest.length == 17 && sig.layers.length == 4 &&
    sig.forest.all (fun op => op.secret.length == 16 && op.siblings.length == 9 &&
      op.siblings.all (fun v => v.length == 16)) &&
    (List.range 4).all (fun lay =>
      let op := sig.layers.getD lay default
      op.values.length == 62 && op.values.all (fun v => v.length == 16) &&
        op.siblings.length == height lay && op.siblings.all (fun v => v.length == 16))

def recoverLayers (idx : Nat) (sig : Signature) (counters : List Nat) (padding : List Val) :
    Nat → Val → OracleComp HashSpec (Option Val)
  | 0, root => pure (some root)
  | n+1, root => do
    let (e, tree) := route idx n
    let counter := counters.getD n (2 ^ 22)
    if counter ≥ 2 ^ 22 then pure none else do
      match ← encoding n tree e root counter with
      | none => pure none
      | some digits => do
        let next ← recoverLayerP idx n digits (sig.layers.getD n default) padding
        recoverLayers idx sig counters padding n next

def verify (pk m : List Byte) (w : Witness) : OracleComp HashSpec Bool := do
  if !shapeOK w.signature || w.counters.length != 4 || w.padding.length != 248 ||
      !(w.padding.all fun p => p.length == 32) then pure false else do
    let d ← digest w.signature.randomness m
    if !digestOK d then pure false else do
      let root ← forestRecover d w.signature.forest
      let result ← recoverLayers (instanceIndex d) w.signature w.counters w.padding 4 root
      pure (result == some pk)


/-- Acceptance of the layer walk forces every visited counter into range.
This holds for arbitrary oracle answers and arbitrary witness fields. -/
theorem recoverLayers_some_counters (hash : Hash) (idx : Nat) (sig : Signature)
    (counters : List Nat) (padding : List Val) (n : Nat) (root result : Val)
    (hresult : evalWithAnswerFn hash (recoverLayers idx sig counters padding n root) =
      some result) :
    ∀ i, i < n → counters.getD i (2^22) < 2^22 := by
  induction n generalizing root result with
  | zero => intro i hi; omega
  | succ n ih =>
    rcases hroute : route idx n with ⟨e, tree⟩
    rw [recoverLayers, hroute] at hresult
    by_cases hc : 2^22 ≤ counters.getD n (2^22)
    · simp only [if_pos hc, evalWithAnswerFn_pure] at hresult
      cases hresult
    · rw [if_neg hc, evalWithAnswerFn_bind] at hresult
      cases he : evalWithAnswerFn hash
          (encoding n tree e root (counters.getD n (2^22))) with
      | none =>
        simp only [he, evalWithAnswerFn_pure] at hresult
        cases hresult
      | some digits =>
        simp only [he, evalWithAnswerFn_bind] at hresult
        intro i hi
        by_cases hin : i = n
        · subst i
          omega
        · exact ih _ _ hresult i (by omega)

/-- Every accepted reference witness passes the structural guards and all
four counter bounds; none of these conditions assume honest provenance. -/
theorem verify_accepted_guards (hash : Hash) (pk m : List Byte) (w : Witness)
    (haccept : evalWithAnswerFn hash (verify pk m w) = true) :
    shapeOK w.signature = true ∧ w.counters.length = 4 ∧ w.padding.length = 248 ∧
      (w.padding.all fun p => p.length == 32) = true ∧
      ∀ i, i < 4 → w.counters.getD i (2^22) < 2^22 := by
  unfold verify at haccept
  split at haccept
  · simp only [evalWithAnswerFn_pure, Bool.false_eq_true] at haccept
  · rename_i hguard
    have hshape : shapeOK w.signature = true ∧ w.counters.length = 4 ∧
        w.padding.length = 248 ∧ (w.padding.all fun p => p.length == 32) = true := by
      simpa [Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, not_or,
        and_assoc] using hguard
    simp only [evalWithAnswerFn_bind] at haccept
    split at haccept
    · simp only [evalWithAnswerFn_pure, Bool.false_eq_true] at haccept
    · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, beq_iff_eq] at haccept
      exact ⟨hshape.1, hshape.2.1, hshape.2.2.1, hshape.2.2.2,
        recoverLayers_some_counters hash _ _ _ _ 4 _ pk haccept⟩

def expandLayers (idx : Nat) (sig : Signature) :
    Nat → Val → OracleComp HashSpec (Option (Val × List Nat))
  | 0, root => pure (some (root, []))
  | n+1, root => do
    let (e, tree) := route idx n
    match ← findCounter n tree e root 0 (2 ^ 22) with
    | none => pure none
    | some (counter, digits) => do
      let next ← recoverLayer idx n digits (sig.layers.getD n default)
      match ← expandLayers idx sig n next with
      | none => pure none
      | some (top, rest) => pure (some (top, rest ++ [counter]))

def expand (pk m : List Byte) (sig : Signature) : OracleComp HashSpec (Option Witness) := do
  if !shapeOK sig then pure none else do
    let d ← digest sig.randomness m
    if !digestOK d then pure none else do
      let root ← forestRecover d sig.forest
      match ← expandLayers (instanceIndex d) sig 4 root with
      | none => pure none
      | some (top, counters) =>
        pure (if top == pk then some ⟨sig, counters, List.replicate 248 (zeros 32)⟩ else none)

end SigGolfCandidate.Base4Candidate.Reference
