import SigGolfCandidate.SphincsSecurity.Proof.IdealStatement
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Erasure
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.DerivationTable
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.StatementLemmas
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.CacheDerivation
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Secrets
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.AdaptiveSeedGuessing
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryCapAccounting

section

namespace SphincsSecurity.Concrete
open OracleComp
variable {m : Type → Type} [Monad m] [LawfulMonad m]
def unpairFin {α : Type} {n N : Nat} (hN : N = 2 * n) (p : Fin n → α × α) (i : Fin N) : α :=
  if i.val % 2 = 0 then (p ⟨i.val / 2, by have := i.isLt; omega⟩).1 else (p ⟨i.val / 2, by have := i.isLt; omega⟩).2
def pairStep {α : Type} {n N : Nat} (hN : N = 2 * n) (f : Fin N → m α) (k : Fin n) : m (α × α) := do
  let a ← f ⟨2 * k.val, by have := k.isLt; omega⟩
  let b ← f ⟨2 * k.val + 1, by have := k.isLt; omega⟩
  pure (a, b)
theorem sequenceFin_pairs {α : Type} (n : Nat) :
    ∀ (N : Nat) (hN : N = 2 * n) (f : Fin N → m α),
      sequenceFin f = unpairFin hN <$> sequenceFin (pairStep hN f) := by
  induction n with
  | zero =>
      intro N hN f
      subst hN
      simp only [Nat.mul_zero, sequenceFin, map_pure]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      intro N hN f
      obtain rfl : N = (2 * n + 1) + 1 := by omega
      have htail := ih (2 * n) rfl (fun i => f i.succ.succ)
      conv_lhs => simp only [sequenceFin]
      rw [htail]
      conv_rhs => simp only [sequenceFin]
      simp only [pairStep, map_bind, bind_assoc, map_pure, pure_bind, bind_map_left]
      have e0 : (⟨2 * (0 : Fin (n + 1)).val, by omega⟩ : Fin (2 * n + 1 + 1)) = 0 := rfl
      have e1 : (⟨2 * (0 : Fin (n + 1)).val + 1, by omega⟩ : Fin (2 * n + 1 + 1)) = (0 : Fin (2 * n + 1)).succ := rfl
      rw [e0, e1]
      apply bind_congr
      intro a
      apply bind_congr
      intro b
      have hpairs : (pairStep (n := n) (N := 2 * n) rfl fun i => f i.succ.succ) =
          (fun k : Fin n => do
            let a ← f ⟨2 * (k.succ).val, by have := k.isLt; omega⟩
            let b ← f ⟨2 * (k.succ).val + 1, by have := k.isLt; omega⟩
            pure (a, b)) := by
        funext k
        simp only [pairStep]
        congr 2
      rw [hpairs]
      apply bind_congr
      intro rest
      congr 1
      funext i
      obtain ⟨i, hi⟩ := i
      match i, hi with
      | 0, _ =>
          rw [show (⟨0, by omega⟩ : Fin (2 * n + 1 + 1)) = 0 from rfl, Fin.cases_zero]
          simp [unpairFin]
      | 1, _ =>
          rw [show (⟨1, by omega⟩ : Fin (2 * n + 1 + 1)) = (0 : Fin (2 * n + 1)).succ from rfl, Fin.cases_succ,
            Fin.cases_zero]
          simp [unpairFin]
      | j + 2, hj =>
          rw [show (⟨j + 2, hj⟩ : Fin (2 * n + 1 + 1)) = (⟨j, by omega⟩ : Fin (2 * n)).succ.succ from rfl,
            Fin.cases_succ, Fin.cases_succ]
          have hidx : (⟨(j + 2) / 2, by omega⟩ : Fin (n + 1)) = (⟨j / 2, by omega⟩ : Fin n).succ :=
            Fin.ext (by simp only [Fin.val_succ]; omega)
          unfold unpairFin
          simp only [Fin.val_succ, show j + 1 + 1 = j + 2 from rfl, show (j + 2) % 2 = j % 2 by omega, hidx,
            Fin.cases_succ]
theorem numChains_eq_two_mul : numChains = 2 * (numChains / 2) := rfl
theorem ftsLeaves_eq_two_mul : 2 ^ ftsTreeHeight = 2 * (2 ^ (ftsTreeHeight - 1)) := rfl
theorem unpairChains_eq {α : Type} (pairs : ChainPair → α × α) :
    unpairChains pairs = unpairFin numChains_eq_two_mul pairs := by
  funext i
  rfl
theorem unpairFtsLeaves_eq {α : Type} (pairs : FtsPair → α × α) :
    unpairFtsLeaves pairs = unpairFin ftsLeaves_eq_two_mul pairs := by
  funext i
  rfl
variable [HasQuery HashSpec m]
def pairOf (secret : ChainIndex → Digest) (pair : ChainPair) : Digest × Digest :=
  (secret (evenChain pair), secret (oddChain pair))
def ftsPairOf (secret : FtsLeaf → Digest) (pair : FtsPair) : Digest × Digest :=
  (secret (evenFtsLeaf pair), secret (oddFtsLeaf pair))
theorem buildLeafPaired_pure (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (digits : Encoding) :
    (buildLeafPaired parameter lay tree leaf (fun pair => pure (pairOf secret pair)) digits : m _) =
      buildLeaf parameter lay tree leaf (fun chainIdx => pure (secret chainIdx)) digits := by
  unfold buildLeafPaired buildLeaf
  rw [sequenceFin_pairs (numChains / 2) numChains numChains_eq_two_mul, bind_map_left]
  simp only [pure_bind, unpairChains_eq]
  rfl
theorem buildLayerTablePaired_pure (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (digits : Encoding) :
    (buildLayerTablePaired parameter lay tree (fun leaf pair => pure (pairOf (secret leaf) pair)) leaf digits : m _) =
      buildLayerTable parameter lay tree (fun leaf chainIdx => pure (secret leaf chainIdx)) leaf digits := by
  unfold buildLayerTablePaired buildLayerTable
  simp only [buildLeafPaired_pure]
theorem buildLayerTreePaired_pure (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (digits : Encoding) :
    (buildLayerTreePaired parameter lay tree (fun leaf pair => pure (pairOf (secret leaf) pair)) leaf digits : m _) =
      buildLayerTree parameter lay tree (fun leaf chainIdx => pure (secret leaf chainIdx)) leaf digits := by
  unfold buildLayerTreePaired
  rw [buildLayerTablePaired_pure]
  unfold buildLayerTree buildLayerTable
  simp only [bind_assoc, pure_bind]
theorem buildFtsTreePaired_pure (parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → Digest) :
    (buildFtsTreePaired parameter index (fun pair => pure (ftsPairOf secret pair)) : m _) =
      buildFtsTree parameter index (fun leaf => pure (secret leaf)) := by
  unfold buildFtsTreePaired buildFtsTree
  rw [sequenceFin_pairs (2 ^ (ftsTreeHeight - 1)) (2 ^ ftsTreeHeight) ftsLeaves_eq_two_mul, bind_map_left]
  simp only [pure_bind]
  have hstep : (fun pair : FtsPair => (do
      let first ← ftsLeafHash parameter index porsTree (evenFtsLeaf pair).val (ftsPairOf secret pair).1
      let second ← ftsLeafHash parameter index porsTree (oddFtsLeaf pair).val (ftsPairOf secret pair).2
      return (((ftsPairOf secret pair).1, first), ((ftsPairOf secret pair).2, second)) : m _)) =
      pairStep ftsLeaves_eq_two_mul (fun leafIdx : FtsLeaf => (do
        let hashed ← ftsLeafHash parameter index porsTree leafIdx.val (secret leafIdx)
        return (secret leafIdx, hashed) : m _)) := by
    funext pair
    simp only [pairStep, pure_bind, bind_assoc]
    rfl
  rw [hstep]
  simp only [unpairFtsLeaves_eq]
theorem signTopLayerPaired_pure (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainIndex → Digest) (topNode : Nat → Nat → m Digest) (message : Digest) :
    signTopLayerPaired parameter index (fun leaf pair => pure (pairOf (secret leaf) pair)) topNode message =
      signTopLayer parameter index (fun leaf chainIdx => pure (secret leaf chainIdx)) topNode message := by
  unfold signTopLayerPaired signTopLayer
  apply bind_congr
  intro search
  rcases search with _ | ⟨counter, encoding⟩
  · rfl
  · dsimp only
    simp only [pure_bind]
    rw [sequenceFin_pairs (numChains / 2) numChains numChains_eq_two_mul, bind_map_left]
    simp only [unpairChains_eq]
    rfl
theorem signLayersPaired_pure (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (topNode : Nat → Nat → m Digest)
    (remaining : Nat) (message : Digest) :
    signLayersPaired parameter index (fun lay tree leaf pair => pure (pairOf (secret lay tree leaf) pair)) topNode
        remaining message =
      signLayers parameter index (fun lay tree leaf chainIdx => pure (secret lay tree leaf chainIdx)) topNode
        remaining message := by
  induction remaining generalizing message with
  | zero => rfl
  | succ remaining ih =>
      simp only [signLayersPaired, signLayers]
      split
      · split
        · rw [signTopLayerPaired_pure]
        · apply bind_congr
          intro search
          rcases search with _ | ⟨counter, encoding⟩
          · rfl
          · dsimp only
            rw [buildLayerTreePaired_pure (secret := secret _ _)]
            apply bind_congr
            intro built
            rw [ih]
      · rfl
theorem signFromPaired_pure (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsLeaf → Digest) (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (topNode : Nat → Nat → m Digest) (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    signFromPaired parameter index (fun tree pair => pure (ftsPairOf (ftsSecret tree) pair))
        (fun lay tree leaf pair => pure (pairOf (otsSecret lay tree leaf) pair)) topNode randomness leaves =
      signFrom parameter index (fun tree leaf => pure (ftsSecret tree leaf))
        (fun lay tree leaf chainIdx => pure (otsSecret lay tree leaf chainIdx)) topNode randomness leaves := by
  unfold signFromPaired signFrom
  rw [buildFtsTreePaired_pure]
  apply bind_congr
  rintro ⟨secrets, table⟩
  dsimp only
  rw [signLayersPaired_pure]
end SphincsSecurity.Concrete
end

section




open OracleComp OracleSpec
namespace SphincsSecurity.Seeded
set_option backward.isDefEq.respectTransparency false
theorem sequenceFin_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    {n : Nat} (values : Fin n → α) : Concrete.sequenceFin (fun i => (pure (values i) : m α)) = pure values := by
  induction n with
  | zero =>
      simp only [Concrete.sequenceFin]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [Concrete.sequenceFin, pure_bind, ih]
      congr 1
      funext i
      cases i using Fin.cases <;> rfl
theorem Erases.sequenceFin {ι : Type} {spec : OracleSpec ι} {α : Type} {n : Nat}
    (known : QueryCache spec) (left right : Fin n → OracleComp spec α)
    (h : ∀ i, Erases known (left i) (right i)) :
    Erases known (Concrete.sequenceFin left) (Concrete.sequenceFin right) := by
  induction n with
  | zero => exact .pure _
  | succ n ih =>
      simp only [Concrete.sequenceFin]
      apply (h 0).bind
      intro head
      apply (ih _ _ (fun i => h i.succ)).bind
      intro tail
      exact .pure _
theorem Erases.bind_map_right {ι : Type} {spec : OracleSpec ι} {α β γ : Type}
    {known : QueryCache spec} {left : OracleComp spec α} {right : OracleComp spec β}
    {f : β → α} (h : Erases known left (f <$> right))
    (nextLeft : α → OracleComp spec γ) (nextRight : β → OracleComp spec γ)
    (hnext : ∀ value, Erases known (nextLeft (f value)) (nextRight value)) :
    Erases known (left >>= nextLeft) (right >>= nextRight) := by
  apply Erases.trans (h.bind nextLeft nextLeft (fun _ => Erases.refl known _))
  simpa only [bind_map_left] using (Erases.refl known right).bind _ _ hnext
def tableOts (outputs : SecretOutputs) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) : Digest :=
  unpairChains (fun pair => splitSecrets (outputs (.inl (lay, tree, leaf, pair)))) chain
def tableFts (outputs : SecretOutputs) (index : Index) (tree : FtsTree) (leaf : FtsLeaf) : Digest :=
  unpairFtsLeaves (fun pair => splitSecrets (outputs (.inr (index, tree, pair)))) leaf
theorem pairOf_tableOts (outputs : SecretOutputs) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (pair : ChainPair) :
    Concrete.pairOf (tableOts outputs lay tree leaf) pair = splitSecrets (outputs (.inl (lay, tree, leaf, pair))) := by
  unfold Concrete.pairOf tableOts unpairChains
  have he : (evenChain pair).val % 2 = 0 := by simp [evenChain]
  have ho : ¬ (oddChain pair).val % 2 = 0 := by simp [oddChain]
  have hpe : chainPairOf (evenChain pair) = pair := Fin.ext (by simp [chainPairOf, evenChain])
  have hpo : chainPairOf (oddChain pair) = pair := Fin.ext (by simp [chainPairOf, oddChain]; omega)
  simp only [he, ho, if_true, if_false, hpe, hpo]
theorem ftsPairOf_tableFts (outputs : SecretOutputs) (index : Index) (tree : FtsTree) (pair : FtsPair) :
    Concrete.ftsPairOf (tableFts outputs index tree) pair = splitSecrets (outputs (.inr (index, tree, pair))) := by
  unfold Concrete.ftsPairOf tableFts unpairFtsLeaves
  have he : (evenFtsLeaf pair).val % 2 = 0 := by simp [evenFtsLeaf]
  have ho : ¬ (oddFtsLeaf pair).val % 2 = 0 := by simp [oddFtsLeaf]
  have hpe : ftsPairOf (evenFtsLeaf pair) = pair := Fin.ext (by simp [ftsPairOf, evenFtsLeaf])
  have hpo : ftsPairOf (oddFtsLeaf pair) = pair := Fin.ext (by simp [ftsPairOf, oddFtsLeaf]; omega)
  simp only [he, ho, if_true, if_false, hpe, hpo]
def tableKey (parameter : PublicParameter) (top : Nat → Nat → Digest) (outputs : SecretOutputs) :
    SphincsSecurity.SecretKey where
  parameter := parameter
  root := top (layerHeight topLayer) 0
  otsSecret := tableOts outputs
  ftsSecret := tableFts outputs
  top := top
section Builders
open Concrete
variable {known : QueryCache HashSpec} (parameter : PublicParameter)
theorem erases_buildChain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    {left right : OracleComp HashSpec Digest} (h : Erases known left right) (digit : Nat) :
    Erases known (buildChain parameter lay tree leaf chainIdx left digit)
      (buildChain parameter lay tree leaf chainIdx right digit) := by
  unfold buildChain
  exact h.bind _ _ fun _ => .refl _ _
theorem erases_buildLeaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    {left right : ChainIndex → OracleComp HashSpec Digest}
    (h : ∀ chainIdx, Erases known (left chainIdx) (right chainIdx)) (digits : Encoding) :
    Erases known (buildLeaf parameter lay tree leaf left digits)
      (buildLeaf parameter lay tree leaf right digits) := by
  unfold buildLeaf
  exact (Erases.sequenceFin known _ _ fun chainIdx =>
    erases_buildChain parameter lay tree leaf chainIdx (h chainIdx) _).bind _ _ fun _ => .refl _ _
theorem erases_buildLayerTable (lay : Layer) (tree : TreeIndex)
    {left right : LeafIndex → ChainIndex → OracleComp HashSpec Digest}
    (h : ∀ leaf chainIdx, Erases known (left leaf chainIdx) (right leaf chainIdx))
    (leaf : LeafIndex) (digits : Encoding) :
    Erases known (buildLayerTable parameter lay tree left leaf digits)
      (buildLayerTable parameter lay tree right leaf digits) := by
  unfold buildLayerTable
  exact (Erases.sequenceFin known _ _ fun _ =>
    erases_buildLeaf parameter lay tree _ (h _) _).bind _ _ fun _ => .refl _ _
theorem erases_buildLayerTree (lay : Layer) (tree : TreeIndex)
    {left right : LeafIndex → ChainIndex → OracleComp HashSpec Digest}
    (h : ∀ leaf chainIdx, Erases known (left leaf chainIdx) (right leaf chainIdx))
    (leaf : LeafIndex) (digits : Encoding) :
    Erases known (buildLayerTree parameter lay tree left leaf digits)
      (buildLayerTree parameter lay tree right leaf digits) := by
  unfold buildLayerTree
  exact (Erases.sequenceFin known _ _ fun _ =>
    erases_buildLeaf parameter lay tree _ (h _) _).bind _ _ fun _ => .refl _ _
theorem erases_buildFtsTree (index : Index)
    {left right : FtsLeaf → OracleComp HashSpec Digest}
    (h : ∀ leaf, Erases known (left leaf) (right leaf)) :
    Erases known (buildFtsTree parameter index left)
      (buildFtsTree parameter index right) := by
  unfold buildFtsTree
  exact (Erases.sequenceFin known _ _ fun leaf =>
    (h leaf).bind _ _ fun _ => .refl _ _).bind _ _ fun _ => .refl _ _
theorem erases_signTopLayer (index : Index)
    {left right : LeafIndex → ChainIndex → OracleComp HashSpec Digest}
    (h : ∀ leaf chainIdx, Erases known (left leaf chainIdx) (right leaf chainIdx))
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (message : Digest) :
    Erases known (signTopLayer parameter index left topLeft message)
      (signTopLayer parameter index right topRight message) := by
  unfold signTopLayer
  apply (Erases.refl known _).bind
  intro search
  rcases search with _ | ⟨counter, encoding⟩
  · exact .pure _
  · apply (Erases.sequenceFin known _ _ fun chainIdx =>
      (h _ chainIdx).bind _ _ fun _ => .refl _ _).bind
    intro values
    apply (Erases.sequenceFin known _ _ fun level => htop _ _).bind
    intro path
    exact .pure _
theorem erases_signLayers (index : Index)
    {left right : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest}
    (h : ∀ lay tree leaf chainIdx, Erases known (left lay tree leaf chainIdx) (right lay tree leaf chainIdx))
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (remaining : Nat) (message : Digest) :
    Erases known (signLayers parameter index left topLeft remaining message)
      (signLayers parameter index right topRight remaining message) := by
  induction remaining generalizing message with
  | zero => exact .pure _
  | succ remaining ih =>
      simp only [signLayers]
      split
      · split
        · apply (erases_signTopLayer parameter index (h _ _) htop message).bind
          intro output
          cases output <;> exact .pure _
        · apply (Erases.refl known _).bind
          intro search
          rcases search with _ | ⟨counter, encoding⟩
          · exact .pure _
          · apply (erases_buildLayerTree parameter _ _ (h _ _) _ _).bind
            rintro ⟨values, path, root⟩
            apply (ih root).bind
            intro rest
            cases rest <;> exact .pure _
      · exact .pure _
theorem erases_signFrom (index : Index)
    {ftsLeft ftsRight : FtsTree → FtsLeaf → OracleComp HashSpec Digest}
    (hfts : ∀ tree leaf, Erases known (ftsLeft tree leaf) (ftsRight tree leaf))
    {otsLeft otsRight : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest}
    (hots : ∀ lay tree leaf chainIdx,
      Erases known (otsLeft lay tree leaf chainIdx) (otsRight lay tree leaf chainIdx))
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    Erases known (signFrom parameter index ftsLeft otsLeft topLeft randomness leaves)
      (signFrom parameter index ftsRight otsRight topRight randomness leaves) := by
  unfold signFrom
  apply (erases_buildFtsTree parameter index (hfts porsTree)).bind
  rintro ⟨secrets, table⟩
  apply (erases_signLayers parameter index hots htop _ _).bind
  intro parts
  cases parts <;> exact .pure _
theorem erases_buildLeafPaired (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    {left right : ChainPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ pair, Erases known (left pair) (right pair)) (digits : Encoding) :
    Erases known (buildLeafPaired parameter lay tree leaf left digits)
      (buildLeafPaired parameter lay tree leaf right digits) := by
  unfold buildLeafPaired
  exact (Erases.sequenceFin known _ _ fun pair =>
    (h pair).bind _ _ fun _ => .refl _ _).bind _ _ fun _ => .refl _ _
theorem erases_buildLayerTablePaired (lay : Layer) (tree : TreeIndex)
    {left right : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ leaf pair, Erases known (left leaf pair) (right leaf pair))
    (leaf : LeafIndex) (digits : Encoding) :
    Erases known (buildLayerTablePaired parameter lay tree left leaf digits)
      (buildLayerTablePaired parameter lay tree right leaf digits) := by
  unfold buildLayerTablePaired
  exact (Erases.sequenceFin known _ _ fun _ =>
    erases_buildLeafPaired parameter lay tree _ (h _) _).bind _ _ fun _ => .refl _ _
theorem erases_buildLayerTreePaired (lay : Layer) (tree : TreeIndex)
    {left right : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ leaf pair, Erases known (left leaf pair) (right leaf pair))
    (leaf : LeafIndex) (digits : Encoding) :
    Erases known (buildLayerTreePaired parameter lay tree left leaf digits)
      (buildLayerTreePaired parameter lay tree right leaf digits) := by
  unfold buildLayerTreePaired
  exact (erases_buildLayerTablePaired parameter lay tree h leaf digits).bind _ _ fun _ => .refl _ _
theorem erases_buildFtsTreePaired (index : Index)
    {left right : FtsPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ pair, Erases known (left pair) (right pair)) :
    Erases known (buildFtsTreePaired parameter index left)
      (buildFtsTreePaired parameter index right) := by
  unfold buildFtsTreePaired
  exact (Erases.sequenceFin known _ _ fun pair =>
    (h pair).bind _ _ fun _ => .refl _ _).bind _ _ fun _ => .refl _ _
theorem erases_signTopLayerPaired (index : Index)
    {left right : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ leaf pair, Erases known (left leaf pair) (right leaf pair))
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (message : Digest) :
    Erases known (signTopLayerPaired parameter index left topLeft message)
      (signTopLayerPaired parameter index right topRight message) := by
  unfold signTopLayerPaired
  apply (Erases.refl known _).bind
  intro search
  rcases search with _ | ⟨counter, encoding⟩
  · exact .pure _
  · apply (Erases.sequenceFin known _ _ fun pair =>
      (h _ pair).bind _ _ fun _ => .refl _ _).bind
    intro values
    apply (Erases.sequenceFin known _ _ fun level => htop _ _).bind
    intro path
    exact .pure _
theorem erases_signLayersPaired (index : Index)
    {left right : Layer → TreeIndex → LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ lay tree leaf pair, Erases known (left lay tree leaf pair) (right lay tree leaf pair))
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (remaining : Nat) (message : Digest) :
    Erases known (signLayersPaired parameter index left topLeft remaining message)
      (signLayersPaired parameter index right topRight remaining message) := by
  induction remaining generalizing message with
  | zero => exact .pure _
  | succ remaining ih =>
      simp only [signLayersPaired]
      split
      · split
        · apply (erases_signTopLayerPaired parameter index (h _ _) htop message).bind
          intro output
          cases output <;> exact .pure _
        · apply (Erases.refl known _).bind
          intro search
          rcases search with _ | ⟨counter, encoding⟩
          · exact .pure _
          · apply (erases_buildLayerTreePaired parameter _ _ (h _ _) _ _).bind
            rintro ⟨values, path, root⟩
            apply (ih root).bind
            intro rest
            cases rest <;> exact .pure _
      · exact .pure _
theorem erases_signFromPaired (index : Index)
    {ftsLeft ftsRight : FtsTree → FtsPair → OracleComp HashSpec (Digest × Digest)}
    (hfts : ∀ tree pair, Erases known (ftsLeft tree pair) (ftsRight tree pair))
    {otsLeft otsRight : Layer → TreeIndex → LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (hots : ∀ lay tree leaf pair,
      Erases known (otsLeft lay tree leaf pair) (otsRight lay tree leaf pair))
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    Erases known (signFromPaired parameter index ftsLeft otsLeft topLeft randomness leaves)
      (signFromPaired parameter index ftsRight otsRight topRight randomness leaves) := by
  unfold signFromPaired
  apply (erases_buildFtsTreePaired parameter index (hfts porsTree)).bind
  rintro ⟨secrets, table⟩
  apply (erases_signLayersPaired parameter index hots htop _ _).bind
  intro parts
  cases parts <;> exact .pure _
end Builders
section FirstSecret
open Concrete
variable {m : Type → Type} [Monad m] [LawfulMonad m]
theorem sequenceFin_split_first {α β : Type} {n : Nat} (hn : 0 < n) (computation : Fin n → m α)
    (first : m β) (rest : β → Fin n → m α)
    (hfirst : computation ⟨0, hn⟩ = first >>= fun value => rest value ⟨0, hn⟩)
    (hrest : ∀ value i, i.val ≠ 0 → rest value i = computation i) :
    sequenceFin computation = first >>= fun value => sequenceFin (rest value) := by
  cases n with
  | zero => omega
  | succ n =>
      simp only [sequenceFin]
      rw [show (0 : Fin (n + 1)) = ⟨0, hn⟩ from rfl, hfirst, bind_assoc]
      apply bind_congr
      intro value
      have htail : (fun i : Fin n => rest value i.succ) = fun i => computation i.succ :=
        funext fun i => hrest value i.succ (by simp)
      rw [htail]
def withFirst {m : Type → Type} [Monad m] (secret : LeafIndex → ChainIndex → m Digest) (first : Digest) :
    LeafIndex → ChainIndex → m Digest :=
  fun leaf chainIdx => if leaf.val = 0 ∧ chainIdx.val = 0 then pure first else secret leaf chainIdx
theorem leafOfNat_val_ne_zero (lay : Layer) (i : Fin (2 ^ layerHeight lay)) (hi : i.val ≠ 0) :
    (leafOfNat i.val).val ≠ 0 := by
  have hheight : layerHeight lay ≤ maxLayerHeight := by
    unfold layerHeight maxLayerHeight
    split <;> (try split) <;> omega
  have hlt : i.val < 2 ^ maxLayerHeight :=
    lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by decide) hheight)
  simp only [leafOfNat, Nat.mod_eq_of_lt hlt]
  exact hi
variable [HasQuery HashSpec m]
theorem buildChain_split_first (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : m Digest) (digit : Nat) :
    buildChain parameter lay tree leaf chainIdx secret digit =
      secret >>= fun value => buildChain parameter lay tree leaf chainIdx (pure value) digit := by
  simp only [buildChain, pure_bind]
theorem buildLayerTree_split_first (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    buildLayerTree parameter lay tree secret leaf digits =
      secret (leafOfNat 0) ⟨0, by decide⟩ >>= fun first =>
        buildLayerTree parameter lay tree (withFirst secret first) leaf digits := by
  unfold buildLayerTree
  rw [sequenceFin_split_first (Nat.two_pow_pos _) _ (secret (leafOfNat 0) ⟨0, by decide⟩)
    (fun first leafNat => buildLeaf parameter lay tree (leafOfNat leafNat.val)
      (withFirst secret first (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)), bind_assoc]
  · unfold buildLeaf
    rw [sequenceFin_split_first (by decide) _ (secret (leafOfNat 0) ⟨0, by decide⟩)
      (fun first chainIdx => buildChain parameter lay tree (leafOfNat 0) chainIdx
        (withFirst secret first (leafOfNat 0) chainIdx)
        ((if (0 : Nat) = leaf.val then digits else zeroEncoding) chainIdx).val), bind_assoc]
    · rw [buildChain_split_first]
      apply bind_congr
      intro first
      simp [withFirst, leafOfNat]
    · intro first chainIdx hchain
      simp [withFirst, hchain]
  · intro first leafNat hleaf
    have hne := leafOfNat_val_ne_zero lay leafNat hleaf
    congr 1
    funext chainIdx
    simp [withFirst, hne]
theorem buildLayerTable_split_first (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    buildLayerTable parameter lay tree secret leaf digits =
      secret (leafOfNat 0) ⟨0, by decide⟩ >>= fun first =>
        buildLayerTable parameter lay tree (withFirst secret first) leaf digits := by
  unfold buildLayerTable
  rw [sequenceFin_split_first (Nat.two_pow_pos _) _ (secret (leafOfNat 0) ⟨0, by decide⟩)
    (fun first leafNat => buildLeaf parameter lay tree (leafOfNat leafNat.val)
      (withFirst secret first (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)), bind_assoc]
  · unfold buildLeaf
    rw [sequenceFin_split_first (by decide) _ (secret (leafOfNat 0) ⟨0, by decide⟩)
      (fun first chainIdx => buildChain parameter lay tree (leafOfNat 0) chainIdx
        (withFirst secret first (leafOfNat 0) chainIdx)
        ((if (0 : Nat) = leaf.val then digits else zeroEncoding) chainIdx).val), bind_assoc]
    · rw [buildChain_split_first]
      apply bind_congr
      intro first
      simp [withFirst, leafOfNat]
    · intro first chainIdx hchain
      simp [withFirst, hchain]
  · intro first leafNat hleaf
    have hne := leafOfNat_val_ne_zero lay leafNat hleaf
    congr 1
    funext chainIdx
    simp [withFirst, hne]
def withFirstPair {m : Type → Type} [Monad m] (secret : LeafIndex → ChainPair → m (Digest × Digest))
    (first : Digest × Digest) : LeafIndex → ChainPair → m (Digest × Digest) :=
  fun leaf pair => if leaf.val = 0 ∧ pair.val = 0 then pure first else secret leaf pair
theorem buildLayerTablePaired_split_first (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (leaf : LeafIndex) (digits : Encoding) :
    buildLayerTablePaired parameter lay tree secret leaf digits =
      secret (leafOfNat 0) ⟨0, by decide⟩ >>= fun first =>
        buildLayerTablePaired parameter lay tree (withFirstPair secret first) leaf digits := by
  unfold buildLayerTablePaired
  rw [sequenceFin_split_first (Nat.two_pow_pos _) _ (secret (leafOfNat 0) ⟨0, by decide⟩)
    (fun first leafNat => buildLeafPaired parameter lay tree (leafOfNat leafNat.val)
      (withFirstPair secret first (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)), bind_assoc]
  · unfold buildLeafPaired
    rw [sequenceFin_split_first (by decide) _ (secret (leafOfNat 0) ⟨0, by decide⟩)
      (fun first pair => do
        let secrets ← withFirstPair secret first (leafOfNat 0) pair
        let a ← buildChain parameter lay tree (leafOfNat 0) (evenChain pair) (pure secrets.1)
          ((if (0 : Nat) = leaf.val then digits else zeroEncoding) (evenChain pair)).val
        let b ← buildChain parameter lay tree (leafOfNat 0) (oddChain pair) (pure secrets.2)
          ((if (0 : Nat) = leaf.val then digits else zeroEncoding) (oddChain pair)).val
        return (a, b)), bind_assoc]
    · apply bind_congr
      intro first
      simp [withFirstPair, leafOfNat]
    · intro first pair hpair
      simp [withFirstPair, hpair]
  · intro first leafNat hleaf
    have hne := leafOfNat_val_ne_zero lay leafNat hleaf
    congr 1
    funext pair
    simp [withFirstPair, hne]
end FirstSecret
section Algorithms
variable (known : QueryCache HashSpec) (parameter : PublicParameter) (seed : MasterSeed)
  (outputs : SecretOutputs)
  (hknown : ∀ position, known (secretInputs parameter seed position) = some (outputs position))
include hknown
theorem erases_derivePair (position : SecretPosition) :
    Erases known ((do return splitSecrets (← Concrete.oracleHash
        (keygenHashInput parameter (secretDomain position) seed))) : OracleComp HashSpec (Digest × Digest))
      (pure (splitSecrets (outputs position))) := by
  unfold Concrete.oracleHash
  exact Erases.skip _ _ (hknown position) _ _ (.pure _)
theorem erases_otsSecret (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (pair : ChainPair) :
    Erases known (otsSecret parameter seed lay tree leaf pair : OracleComp HashSpec (Digest × Digest))
      (pure (Concrete.pairOf (tableOts outputs lay tree leaf) pair)) := by
  rw [pairOf_tableOts]
  exact erases_derivePair known parameter seed outputs hknown (.inl (lay, tree, leaf, pair))
theorem erases_ftsSecret (index : Index) (tree : FtsTree) (pair : FtsPair) :
    Erases known (ftsSecret parameter seed index tree pair : OracleComp HashSpec (Digest × Digest))
      (pure (Concrete.ftsPairOf (tableFts outputs index tree) pair)) := by
  rw [ftsPairOf_tableFts]
  exact erases_derivePair known parameter seed outputs hknown (.inr (index, tree, pair))
theorem erases_signFrom_table (top : Nat → Nat → Digest) (index : Index) (randomness : Randomness)
    (leaves : IndexGroup → FtsLeaf) {topNode : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topNode level nodeIdx) (pure (top level nodeIdx))) :
    Erases known
      (Concrete.signFromPaired parameter index (ftsSecret parameter seed index) (otsSecret parameter seed)
        topNode randomness leaves : OracleComp HashSpec (Option Signature))
      (Concrete.signAfterDigest (tableKey parameter top outputs) randomness index leaves) := by
  rw [Concrete.signAfterDigest, ← Concrete.signFromPaired_pure]
  exact erases_signFromPaired parameter index
    (fun tree pair => erases_ftsSecret known parameter seed outputs hknown index tree pair)
    (fun lay tree leaf pair => erases_otsSecret known parameter seed outputs hknown lay tree leaf pair)
    htop randomness leaves
end Algorithms
end SphincsSecurity.Seeded
end

section


open OracleComp OracleSpec
namespace SphincsSecurity.Seeded
set_option backward.isDefEq.respectTransparency false
open Concrete
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]
def tableDigestLoop (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (message : Message) : Nat → Nat → m (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := truncateHash (randomizers (message, BitVec.ofNat 32 trial))
      match ← Concrete.signAttempt secretKey message randomness with
      | some (index, leaves) => return some (randomness, index, leaves)
      | none => tableDigestLoop randomizers secretKey message attempts (trial + 1)
def tableSign (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (message : Message) : OracleComp HashSpec (Option Signature) := do
  match ← tableDigestLoop randomizers secretKey message digestAttemptLimit 0 with
  | none => return none
  | some (randomness, index, leaves) => Concrete.signAfterDigest secretKey randomness index leaves
noncomputable def tableScheme (randomizers : RandomizerOutputs) : Scheme SphincsSecurity.SecretKey where
  keygen := Concrete.scheme.keygen
  sign := fun sk message => liftM (tableSign randomizers sk message : OracleComp HashSpec _)
  verify := Concrete.scheme.verify
theorem erases_deterministicDigestLoop (known : QueryCache HashSpec) (parameter : PublicParameter)
    (seed : MasterSeed) (top : Nat → Nat → Digest) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (hknown : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (message : Message) (attempts trial : Nat) :
    Erases known (signDigestLoop ⟨seed, parameter, top (layerHeight topLayer) 0⟩ message attempts trial :
        OracleComp HashSpec _)
      (tableDigestLoop randomizers (tableKey parameter top outputs) message attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
      unfold signDigestLoop tableDigestLoop deriveRandomizer Concrete.oracleHash
      simp only [bind_assoc, pure_bind]
      apply Erases.skip _ _ (hknown (message, BitVec.ofNat 32 trial))
      change Erases known (Concrete.signAttempt (tableKey parameter top outputs) message
        (truncateHash (randomizers (message, BitVec.ofNat 32 trial))) >>= _)
          (Concrete.signAttempt (tableKey parameter top outputs) message
            (truncateHash (randomizers (message, BitVec.ofNat 32 trial))) >>= _)
      apply (Erases.refl known _).bind
      intro attempt
      cases attempt with
      | none => exact ih _
      | some result => exact .pure _
def maskRegionWith {m : Type → Type} [Monad m] (getMask : Nat → Nat → m Digest) (table : Nat → Nat → Digest) :
    m TopRegion := do
  let rows ← Concrete.sequenceFin fun level : Fin maxLayerHeight => do
    let row ← Concrete.sequenceFin fun nodeIdx : Fin (2 ^ (maxLayerHeight - level.val)) => do
      let mask ← getMask level.val nodeIdx.val
      return table level.val nodeIdx.val ^^^ mask
    return fun nodeIdx : Nat => if h : nodeIdx < 2 ^ (maxLayerHeight - level.val) then row ⟨nodeIdx, h⟩ else 0
  return fun level nodeIdx => rows level nodeIdx.val
theorem maskRegion_eq_with {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter)
    (seed : MasterSeed) (table : Nat → Nat → Digest) :
    (maskRegion parameter seed table : m TopRegion) = maskRegionWith (maskSecret parameter seed) table := rfl
def tableRegion (table : Nat → Nat → Digest) (masks : MaskOutputs) : TopRegion :=
  fun level nodeIdx => table level.val nodeIdx.val ^^^ maskValue masks level.val nodeIdx.val
theorem maskRegionWith_pure {m : Type → Type} [Monad m] [LawfulMonad m] (table : Nat → Nat → Digest)
    (masks : MaskOutputs) :
    maskRegionWith (m := m) (fun level nodeIdx => pure (maskValue masks level nodeIdx)) table =
      pure (tableRegion table masks) := by
  unfold maskRegionWith
  simp only [pure_bind, sequenceFin_pure]
  congr 1
  funext level nodeIdx
  simp [tableRegion, nodeIdx.isLt]
def cachedTableSignChecked (randomizers : RandomizerOutputs) (masks : MaskOutputs)
    (secretKey : SphincsSecurity.SecretKey) (cache : TopCache) (message : Message) :
    OracleComp HashSpec (Option Signature) := do
  match ← tableDigestLoop randomizers secretKey message digestAttemptLimit 0 with
  | none => return none
  | some (randomness, index, leaves) =>
      Concrete.signFrom secretKey.parameter index (fun tree leaf => pure (secretKey.ftsSecret index tree leaf))
        (fun lay tree leaf chainIdx => pure (secretKey.otsSecret lay tree leaf chainIdx))
        (fun level nodeIdx => pure (cache.node level nodeIdx ^^^ maskValue masks level nodeIdx)) randomness leaves
def cachedTableSign (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs)
    (secretKey : SphincsSecurity.SecretKey) (cache : TopCache) (message : Message) :
    OracleComp HashSpec (Option Signature) :=
  if macs cache.region = cache.tag then cachedTableSignChecked randomizers masks secretKey cache message
  else pure none
section Cached
variable (known : QueryCache HashSpec) (parameter : PublicParameter) (seed : MasterSeed)
  (top : Nat → Nat → Digest) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
  (masks : MaskOutputs) (macs : MacOutputs)
theorem erases_maskSecret
    (hmasks : ∀ position, known (maskInputs parameter seed position) = some (masks position))
    (level nodeIdx : Nat) :
    Erases known (maskSecret parameter seed level nodeIdx : OracleComp HashSpec Digest)
      (pure (maskValue masks level nodeIdx)) := by
  unfold maskSecret deriveKey Concrete.oracleHash
  exact Erases.skip _ _ (hmasks (maskPosition level nodeIdx)) _ _ (.pure _)
theorem erases_cachedTopNode
    (hmasks : ∀ position, known (maskInputs parameter seed position) = some (masks position))
    (cache : TopCache) (level nodeIdx : Nat) :
    Erases known (cachedTopNode parameter seed cache level nodeIdx : OracleComp HashSpec Digest)
      (pure (cache.node level nodeIdx ^^^ maskValue masks level nodeIdx)) := by
  unfold cachedTopNode maskSecret deriveKey Concrete.oracleHash
  simp only [bind_assoc, pure_bind]
  exact Erases.skip _ _ (hmasks (maskPosition level nodeIdx)) _ _ (.pure _)
theorem erases_maskRegion
    (hmasks : ∀ position, known (maskInputs parameter seed position) = some (masks position))
    (table : Nat → Nat → Digest) :
    Erases known (maskRegion parameter seed table : OracleComp HashSpec TopRegion)
      (pure (tableRegion table masks)) := by
  rw [maskRegion_eq_with, ← maskRegionWith_pure]
  unfold maskRegionWith
  apply (Erases.sequenceFin known _ _ fun level =>
    (Erases.sequenceFin known _ _ fun nodeIdx =>
      (erases_maskSecret known parameter seed masks hmasks _ _).bind _ _ fun _ => .pure _).bind _ _
        fun _ => .pure _).bind
  intro _
  exact .pure _
theorem erases_signChecked
    (hsecrets : ∀ position, known (secretInputs parameter seed position) = some (outputs position))
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (hmasks : ∀ position, known (maskInputs parameter seed position) = some (masks position))
    (cache : TopCache) (message : Message) :
    Erases known (signChecked ⟨seed, parameter, top (layerHeight topLayer) 0⟩ cache message :
        OracleComp HashSpec _)
      (cachedTableSignChecked randomizers masks (tableKey parameter top outputs) cache message) := by
  unfold signChecked cachedTableSignChecked
  apply (erases_deterministicDigestLoop known parameter seed top outputs randomizers hrandomizers message _ _).bind
  intro attempt
  rcases attempt with _ | ⟨randomness, index, leaves⟩
  · exact .pure _
  · dsimp only
    rw [← Concrete.signFromPaired_pure]
    exact erases_signFromPaired parameter index
      (fun tree pair => erases_ftsSecret known parameter seed outputs hsecrets index tree pair)
      (fun lay tree leaf pair => erases_otsSecret known parameter seed outputs hsecrets lay tree leaf pair)
      (fun level nodeIdx => erases_cachedTopNode known parameter seed masks hmasks cache level nodeIdx)
      randomness leaves
theorem erases_cachedSign
    (hsecrets : ∀ position, known (secretInputs parameter seed position) = some (outputs position))
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (hmasks : ∀ position, known (maskInputs parameter seed position) = some (masks position))
    (hmacs : ∀ region, known (macInputs parameter seed region) = some (macs region))
    (cache : TopCache) (message : Message) :
    Erases known (sign ⟨seed, parameter, top (layerHeight topLayer) 0⟩ cache message : OracleComp HashSpec _)
      (cachedTableSign randomizers masks macs (tableKey parameter top outputs) cache message) := by
  unfold sign cachedTableSign Concrete.oracleHash
  apply Erases.skip _ _ (hmacs cache.region)
  change Erases known (if macs cache.region = cache.tag then _ else _) _
  split
  · exact erases_signChecked known parameter seed top outputs randomizers masks hsecrets hrandomizers hmasks
      cache message
  · exact .pure _
end Cached
end SphincsSecurity.Seeded
end

section


open OracleComp OracleSpec
namespace SphincsSecurity.Seeded
set_option backward.isDefEq.respectTransparency false
theorem Erases.simulateQ_writer {ι κ τ : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    {logSpec : OracleSpec τ} {α : Type} (known : QueryCache target)
    (left right : QueryImpl source (WriterT (QueryLog logSpec) (OracleComp target)))
    (h : ∀ input, Erases known (left input).run (right input).run)
    (computation : OracleComp source α) :
    Erases known (simulateQ left computation).run (simulateQ right computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure _
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, WriterT.run_bind]
      apply (h input).bind
      intro result
      exact (ih result.1).map _
open Concrete
def keygenCachedWith (secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (getMask : Nat → Nat → OracleComp HashSpec Digest) (getMac : TopRegion → OracleComp HashSpec HashOutput) :
    OracleComp HashSpec ((Nat → Nat → Digest) × TopCache) := do
  let (_, table) ← buildLayerTablePaired 0 topLayer rootTree secret ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  let region ← maskRegionWith getMask table
  let tag ← getMac region
  return (table, ⟨tag, region⟩)
def keysOf (seed : MasterSeed) (result : (Nat → Nat → Digest) × TopCache) : PublicKey × TopCache × SecretKey :=
  (⟨result.1 (layerHeight topLayer) 0, 0⟩, result.2, ⟨seed, 0, result.1 (layerHeight topLayer) 0⟩)
theorem keygenFromSeed_eq (seed : MasterSeed) :
    keygenFromSeed seed = keysOf seed <$> keygenCachedWith (otsSecret 0 seed topLayer rootTree)
      (maskSecret 0 seed) (fun region => oracleHash (macHashInput 0 seed region)) := by
  simp only [keygenFromSeed, keygenCachedWith, maskRegion_eq_with, keysOf, map_bind, bind_assoc, map_pure]
theorem keygenCachedWith_pure (outputs : SecretOutputs) (masks : MaskOutputs) (macs : MacOutputs) :
    keygenCachedWith (fun leaf pair => pure (pairOf (tableOts outputs topLayer rootTree leaf) pair))
        (fun level nodeIdx => pure (maskValue masks level nodeIdx)) (fun region => pure (macs region)) =
      (fun top => (top, (⟨macs (tableRegion top masks), tableRegion top masks⟩ : TopCache))) <$>
        (keygenTable 0 (tableOts outputs topLayer rootTree) : OracleComp HashSpec _) := by
  unfold keygenCachedWith keygenTable
  rw [buildLayerTablePaired_pure]
  simp only [maskRegionWith_pure, pure_bind, map_bind, map_pure]
def firstSecretPosition : SecretPosition :=
  .inl (topLayer, rootTree, leafOfNat 0, ⟨0, by decide⟩)
theorem keygenCachedWith_first (secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (getMask : Nat → Nat → OracleComp HashSpec Digest) (getMac : TopRegion → OracleComp HashSpec HashOutput) :
    keygenCachedWith secret getMask getMac =
      secret (leafOfNat 0) ⟨0, by decide⟩ >>= fun first =>
        keygenCachedWith (withFirstPair secret first) getMask getMac := by
  unfold keygenCachedWith
  rw [buildLayerTablePaired_split_first, bind_assoc]
theorem otsSecret_first (seed : MasterSeed) :
    (otsSecret 0 seed topLayer rootTree (leafOfNat 0) ⟨0, by decide⟩ : OracleComp HashSpec (Digest × Digest)) =
      (splitSecrets <$> (HashSpec.query (secretInputs 0 seed firstSecretPosition) : OracleComp HashSpec _)) := by
  simp only [otsSecret, oracleHash, bind_pure_comp]
  rfl
section Keygen
variable {known : QueryCache HashSpec} {seed : MasterSeed} {outputs : SecretOutputs}
  {masks : MaskOutputs} {macs : MacOutputs}
  (hsecrets : ∀ position, known (secretInputs 0 seed position) = some (outputs position))
  (hmasks : ∀ position, known (maskInputs 0 seed position) = some (masks position))
  (hmacs : ∀ region, known (macInputs 0 seed region) = some (macs region))
include hsecrets hmasks hmacs
theorem erases_keygenCachedWith {secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (hsecret : ∀ leaf pair, Erases known (secret leaf pair)
      (pure (pairOf (tableOts outputs topLayer rootTree leaf) pair))) :
    Erases known (keygenCachedWith secret (maskSecret 0 seed)
        (fun region => oracleHash (macHashInput 0 seed region)))
      (keygenCachedWith (fun leaf pair => pure (pairOf (tableOts outputs topLayer rootTree leaf) pair))
        (fun level nodeIdx => pure (maskValue masks level nodeIdx)) (fun region => pure (macs region))) := by
  unfold keygenCachedWith
  apply (erases_buildLayerTablePaired 0 _ _ hsecret _ _).bind
  rintro ⟨_, table⟩
  dsimp only
  rw [maskRegionWith_pure, pure_bind, ← maskRegion_eq_with]
  apply Erases.bind_known (erases_maskRegion known 0 seed masks hmasks table)
  unfold oracleHash
  exact Erases.skip _ _ (hmacs (tableRegion table masks)) _ _ (.pure _)
theorem erases_keygen :
    Erases known (keygenCachedWith (otsSecret 0 seed topLayer rootTree) (maskSecret 0 seed)
        (fun region => oracleHash (macHashInput 0 seed region)))
      (keygenCachedWith (fun leaf pair => pure (pairOf (tableOts outputs topLayer rootTree leaf) pair))
        (fun level nodeIdx => pure (maskValue masks level nodeIdx)) (fun region => pure (macs region))) :=
  erases_keygenCachedWith hsecrets hmasks hmacs fun leaf pair =>
    erases_otsSecret known 0 seed outputs hsecrets _ _ leaf pair
theorem erases_keygen_first :
    Erases known (keygenCachedWith (withFirstPair (otsSecret 0 seed topLayer rootTree)
          (splitSecrets (outputs firstSecretPosition))) (maskSecret 0 seed)
        (fun region => oracleHash (macHashInput 0 seed region)))
      (keygenCachedWith (fun leaf pair => pure (pairOf (tableOts outputs topLayer rootTree leaf) pair))
        (fun level nodeIdx => pure (maskValue masks level nodeIdx)) (fun region => pure (macs region))) := by
  refine erases_keygenCachedWith hsecrets hmasks hmacs fun leaf pair => ?_
  unfold withFirstPair
  split
  · next hfirst =>
      have hleaf : leaf = leafOfNat 0 := Fin.ext (by simp [hfirst.1, leafOfNat])
      have hpair : pair = ⟨0, by decide⟩ := Fin.ext hfirst.2
      subst hleaf hpair
      rw [pairOf_tableOts]
      exact .pure _
  · exact erases_otsSecret known 0 seed outputs hsecrets _ _ leaf pair
end Keygen
end SphincsSecurity.Seeded
end

section



open OracleComp OracleSpec ENNReal
namespace SphincsSecurity.Seeded
set_option backward.isDefEq.respectTransparency false
theorem countHashQueries_run'_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (countHashQueries (liftM (OracleWorld.query input) >>= next))).run' cache =
      ((romImpl input).run cache >>= fun step =>
        (fun result => (result.1, (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0) + result.2)) <$>
          (simulateQ romImpl (countHashQueries (next step.1))).run' step.2) := by
  rw [countHashQueries_query_bind, run'_query_bind]
  apply bind_congr
  intro step
  simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rfl
theorem Erases.probEvent_counted_le {α : Type} {known : QueryCache HashSpec}
    {left right : OracleComp OracleWorld α} (h : Erases (worldKnown known) left right)
    (cache : QueryCache HashSpec) (hcache : known ≤ cache) (event : α → Nat → Prop)
    (hmono : ∀ value count count', count' ≤ count → event value count → event value count') :
    Pr[fun result => event result.1 result.2 | (simulateQ romImpl (countHashQueries left)).run' cache] ≤
      Pr[fun result => event result.1 result.2 | (simulateQ romImpl (countHashQueries right)).run' cache] := by
  induction h generalizing cache event with
  | pure value => exact le_rfl
  | query input left right _ ih =>
      rw [countHashQueries_run'_query_bind, countHashQueries_run'_query_bind, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro step
      by_cases hstep : step ∈ support ((romImpl input).run cache)
      · apply mul_le_mul' le_rfl
        rw [probEvent_map, probEvent_map]
        exact ih step.1 step.2 (romImpl_preserves_known known cache hcache input step hstep) _
          (fun value count count' hle h => hmono value _ _ (Nat.add_le_add_left hle _) h)
      · rw [probOutput_eq_zero_of_not_mem_support hstep, zero_mul, zero_mul]
  | skip input answer hknown next right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          rw [countHashQueries_run'_query_bind]
          change Pr[_ | (randomOracle (spec := HashSpec) input).run cache >>= _] ≤ _
          rw [QueryImpl.withCaching_run_some _ hc, pure_bind, probEvent_map]
          refine le_trans ?_ (ih cache hcache event hmono)
          apply probEvent_mono
          intro result _ hresult
          exact hmono _ _ _ (Nat.le_add_left _ _) hresult
  | cached input answer hknown left right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          rw [countHashQueries_run'_query_bind, countHashQueries_run'_query_bind]
          change Pr[_ | (randomOracle (spec := HashSpec) input).run cache >>= _] ≤
            Pr[_ | (randomOracle (spec := HashSpec) input).run cache >>= _]
          rw [QueryImpl.withCaching_run_some _ hc, pure_bind, pure_bind, probEvent_map, probEvent_map]
          exact ih cache hcache _ (fun value count count' hle h => hmono value _ _ (Nat.add_le_add_left hle _) h)
  | trans _ _ first second => exact (first cache hcache event hmono).trans (second cache hcache event hmono)
open scoped Classical in
theorem romRun_cap_event {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget | (simulateQ romImpl (countHashQueries computation)).run' cache] =
      Pr[fun outcome => ∃ result, outcome = some result ∧ event result.1 |
        (simulateQ romImpl (QueryCap.run (fun input : OracleWorld.Domain => input matches .inr _) computation budget)).run' cache] := by
  induction computation using OracleComp.inductionOn generalizing cache budget with
  | pure value =>
      simp only [countHashQueries_pure, QueryCap.run_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      rw [probEvent_pure, probEvent_pure]
      simp
  | query_bind input next ih =>
      rw [countHashQueries_run'_query_bind, QueryCap.run_query_bind]
      cases input with
      | inl sample =>
          simp only [Bool.false_eq_true, if_false, zero_add, Prod.mk.eta, id_map']
          rw [run'_query_bind, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
          exact tsum_congr fun step => congrArg _ (ih step.1 step.2 budget)
      | inr hash =>
          simp only [if_true]
          cases budget with
          | zero =>
              rw [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, probEvent_pure]
              simp only [reduceCtorEq, false_and, exists_false, if_false]
              apply probEvent_eq_zero
              intro result hresult hev
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step, _, hr⟩ := hresult
              rw [support_map] at hr
              obtain ⟨inner, _, rfl⟩ := hr
              have := hev.2
              simp at this
          | succ remaining =>
              rw [run'_query_bind, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
              refine tsum_congr fun step => congrArg _ ?_
              rw [probEvent_map, ← ih step.1 step.2 remaining]
              apply probEvent_ext
              intro result _
              simp only [Function.comp_apply]
              constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
theorem hashQueryBound_cap {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (budget : Nat) :
    HashQueryBound (QueryCap.run (fun input : OracleWorld.Domain => input matches .inr _) computation budget) cache budget := by
  intro result hresult
  apply QueryCap.counted_le_of_queryBound (fun input : OracleWorld.Domain => input matches .inr _) _ budget
    (QueryCap.run_queryBound _ computation budget) result
  exact support_simulateQ_run'_subset _ _ _ hresult
open scoped Classical in
theorem probEvent_random_cache_change_event {α : Type} (computation : OracleComp OracleWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutside (fun input => SeedHit input seed) (initial seed) cache)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget | sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (countHashQueries computation)).run' (initial seed)] ≤
      Pr[fun result => event result.1 ∧ result.2 ≤ budget | (simulateQ romImpl (countHashQueries computation)).run' cache] +
        budget / ((2 ^ 207 : Nat) : ℝ≥0∞) := by
  have hleft : Pr[fun result => event result.1 ∧ result.2 ≤ budget | sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (countHashQueries computation)).run' (initial seed)] =
      Pr[fun outcome => ∃ result, outcome = some result ∧ event result.1 | sampleMasterSeed >>= fun seed =>
        (simulateQ romImpl (QueryCap.run (fun input : OracleWorld.Domain => input matches .inr _) computation budget)).run'
          (initial seed)] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    exact tsum_congr fun seed => congrArg _ (romRun_cap_event computation _ budget event)
  rw [hleft, romRun_cap_event computation cache budget event]
  exact probEvent_random_cache_change_le _ initial cache hagree budget (hashQueryBound_cap computation cache budget) _
end SphincsSecurity.Seeded
end
