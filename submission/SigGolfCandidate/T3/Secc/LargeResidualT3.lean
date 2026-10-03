import SigGolfCandidate.T3.Secc.CanonEncoding
import SigGolfCandidate.T3.Secc.LargeResidualBound

/-!
# LR-34 (T3 vocabulary): hidden coordinates, children, knowledge, disclosures and the contact test

* `Coord := CanonGraph.Node ⊕ CanonGraph.SecretIndex` — the hidden 128-bit values of the large route: the low halves
  of the canonical labels of every source-sized honest position (G), the chain seeds and the FTS secrets.
* `childSlots N` — the values a node's honest input carries, each with the 16-byte block of the input that holds it
  (`slotValue`); `honestValue A c` — the honest value of a coordinate under an answers table.
* `Known D` — the knowledge closure of a disclosed set: a node is known once all its children are (secrets only by
  disclosure). `keygenDisclosed` (the public key root) and `signDisclosed A published request` (exactly what a
  successful honest signature reveals: opened FTS secrets, FTS proof nodes, chain values at the reference digits, the
  authentication paths) generate the adversary's knowledge.
* `ContactTest A K input answer` — the large-route contact of one adversary/verifier query (first occurrence):
  a *guess* (the first unknown child's slot holds its honest value; an encoding row whose message is the hidden honest
  message) or a *hit* (a non-honest input at a parsed position whose low answer is the honest label; a non-reference
  encoding row decoding to the reference word).
-/

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeResidualT3 : DecidableEq T3.Cache := Classical.decEq _

/-- Hidden coordinates of the T3 large route: canonical label low halves and private secrets. -/
abbrev Coord := CanonGraph.Node ⊕ CanonGraph.SecretIndex

/-! ## Children and slots -/

/-- The value carried by a chain row: the seed (step 0) or the previous step's label. -/
def chainChild (p : ChainGraph.Point) : Coord :=
  if p.2.val = 0 then .inr (.inl p.1) else .inl (.chain (ChainGraph.predecessor p))

/-- The coordinate whose low half is the tree value at `(level, c)` (level 0 = leaf pks). -/
def treeChild (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option Coord :=
  if level = 0 then (if h : c < 4096 then some (.inl (.leaf ⟨lay, tree, ⟨c, h⟩⟩)) else none)
  else (treeNodeAt lay tree (level - 1) c).map fun n => .inl (.node n)

/-- The coordinate whose low half is the FTS tree value at `(level, c)` (level 0 = FTS leaves). -/
def ftsChild (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) : Option Coord :=
  if level = 0 then (if h : c < 2048 then some (.inl (.ftsLeaf ⟨index, coord, ⟨c, h⟩⟩)) else none)
  else (ftsNodeAt index coord (level - 1) c).map fun n => .inl (.ftsNode n)

/-- The chain point whose low label is the end value (step `2^w − 1`) of chain `i` of a leaf. -/
def endPoint (L : LeafPos) (i : Nat) : ChainGraph.Point :=
  (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(maxDigit L.lay i - 1) % 7, Nat.mod_lt _ (by decide)⟩)

/-- The block (16 bytes) of a "first, header, rest" input holding item `i`. -/
def listBlock (i : Nat) : Nat := if i = 0 then 0 else i + 1

/-- Children of a node, each with the 16-byte block of the node's input that carries its value. -/
def childSlots : CanonGraph.Node → List (Coord × Nat)
  | .chain p => [(chainChild p, 3)]
  | .leaf L => (List.range (chainCount L.lay)).map fun i => (.inl (.chain (endPoint L i)), listBlock i)
  | .node n => ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList
  | .ftsLeaf f => [(.inr (.inr f), 2)]
  | .ftsNode n => ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList
  | .forest index => (List.range 7).map fun c => (.inl (.ftsNode (ftsRootNode index (fin7 c))), listBlock c)

/-- The 128-bit value an input holds in a 16-byte block. -/
def slotValue (input : HashInput) (block : Nat) : Digest := readDigest ((input.drop (16 * block)).take 16)

/-- Honest value of a coordinate: the low half of the honest answer at its position, or the private secret. -/
noncomputable def honestValue (A : Answers) : Coord → Digest
  | .inl N => (A (.inl (.inr (Extract.honestInput A N.toPos)))).extractLsb' 0 128
  | .inr s => secretsOf A s

/-! ## Knowledge -/

/-- Knowledge closure of a disclosed set: disclosed coordinates are known; a node is known once all its children are. -/
inductive Known (D : Coord → Prop) : Coord → Prop
  | base {c : Coord} : D c → Known D c
  | node {N : CanonGraph.Node} : (∀ cs ∈ childSlots N, Known D cs.1) → Known D (.inl N)

/-- The first child (with its block) not yet known. -/
noncomputable def firstUnknown (K : Coord → Prop) (N : CanonGraph.Node) : Option (Coord × Nat) :=
  (childSlots N).find? fun cs => decide (¬K cs.1)

/-! ## Disclosures -/

/-- Key generation reveals the public key, and (conservatively, the cache being a one-time pad of them) every node of
the top tree at the cached levels: the tree values of levels `0 … 12` of the layer-0 tree. -/
def keygenDisclosed : List Coord :=
  (List.range' 0 13).flatMap fun level =>
    (List.range (2 ^ (12 - level))).filterMap fun node => treeChild 0 0 level node

/-- The chain value at digit `d` of chain `i` of a leaf: the seed (`d = 0`) or the label of step `d − 1`. -/
def chainItem (L : LeafPos) (i d : Nat) : Coord :=
  if d = 0 then .inr (.inl ⟨L.lay, L.tree, L.leaf, fin58 i⟩)
  else .inl (.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(d - 1) % 7, Nat.mod_lt _ (by decide)⟩))

/-- The opened secrets of one FTS coordinate (Core's `signPayload` order). -/
def ftsOpened (index : Fin (2^31)) (coord : Nat) (sel : Selection) : List Coord :=
  (sel.leaves.map (fun s => sel.bucket * 128 + s)).filterMap fun leaf =>
    if h : leaf < 2048 then some (.inr (.inr ⟨index, fin7 coord, ⟨leaf, h⟩⟩)) else none

/-- The proof nodes of one FTS coordinate: frontier (inner) nodes, then the four outer nodes. -/
def ftsProof (index : Fin (2^31)) (coord : Nat) (sel : Selection) : List Coord :=
  ((frontier (sel.leaves.map (fun s => sel.bucket * 128 + s)) 7 sel.bucket).filterMap fun p =>
      ftsChild index (fin7 coord) p.1 p.2) ++
    ((List.range 4).filterMap fun j => ftsChild index (fin7 coord) (7 + j) (sel.bucket / 2 ^ j ^^^ 1))

/-- The FTS part of a signature: opened secrets and proof nodes, coordinate by coordinate. -/
def ftsItems (index : Fin (2^31)) (chosen : List Selection) : List Coord :=
  (List.range 7).flatMap fun coord =>
    ftsOpened index coord (chosen.getD coord ⟨0, []⟩) ++ ftsProof index coord (chosen.getD coord ⟨0, []⟩)

/-- The route leaf of a layer as a W leaf address. -/
def routeAddr (index : Nat) (lay : Layer) : Wots.LeafAddr := ⟨lay, (route index lay).2, (route index lay).1⟩

/-- The chain values at the digits of the route leaf of one layer. -/
def layerChains (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 ∧ (route index.val lay).1 < 4096 then
    (List.range (chainCount lay)).map fun i =>
      chainItem ⟨lay, ⟨(route index.val lay).2, h.1⟩, ⟨(route index.val lay).1, h.2⟩⟩ i
        ((digitsOf (routeAddr index.val lay)).getD i 0)
  else []

/-- The authentication path of the route leaf of one layer. -/
def layerPath (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 then
    (List.range (height lay)).filterMap fun j =>
      treeChild lay ⟨(route index.val lay).2, h⟩ j ((route index.val lay).1 / 2 ^ j ^^^ 1)
  else []

/-- The hypertree part of a signature with reference digits `digitsOf`. -/
def layerItems (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) : List Coord :=
  (List.finRange 4).flatMap fun lay => layerChains digitsOf index lay ++ layerPath index lay

/-- The index of a digest output. -/
def digestIndex (N : HashOutput) : Fin (2^31) := ⟨N.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩

/-- What a successful signature with digest output `N` reveals, with reference digits `digitsOf`. -/
def signItemsWith (digitsOf : Wots.LeafAddr → List Nat) (N : HashOutput) : List Coord :=
  ftsItems (digestIndex N) (selections N) ++ layerItems digitsOf (digestIndex N)

/-- What a successful honest signature with digest output `N` reveals under `A`. -/
noncomputable def signItems (A : Answers) (N : HashOutput) : List Coord :=
  signItemsWith (Wots.referenceDigits A) N

/-- The honest signer succeeds after its digest search: every route encoding search succeeds. -/
def RouteOk (A : Answers) (index : Nat) : Prop := ∀ lay : Layer, (Wots.referenceSearch A (routeAddr index lay)).isSome

/-- The honest digest search of a request under `A`. -/
noncomputable def signDigest (A : Answers) (message : Message) : Option (BitVec 32 × HashOutput) :=
  evalWithAnswerFn A (digestSearch (evalWithAnswerFn A (privateNonce message)) message 0 attemptLimit)

/-- What the honest signer reveals on one request: `signItems` of its digest output when it returns a signature
(published cache, successful digest search, every route encoding search successful), nothing otherwise. -/
noncomputable def signDisclosed (A : Answers) (published : T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    List Coord :=
  if request.cache = published then
    match signDigest A request.message with
    | some (_, N) => if RouteOk A (N.toNat % 2 ^ 31) then signItems A N else []
    | none => []
  else []

/-! ## The contact test -/

/-- The coordinates of the honest message of a source leaf, each with the component of a message that carries its
value (E8): the two children of the child tree's root (`L`, `R`), or the forest pk at layer 3. -/
def msgSlots (L : EncLeaf) : List (Coord × (LayerMessage → Digest)) :=
  if h : L.1.lay.val < 3 then
    [(.inl (.node (childNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) 0)), fun m => m.1),
     (.inl (.node (childNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) 1)), fun m => m.2.2)]
  else [(.inl (.forest (childIndex L)), fun m => m.1)]

/-- The message coordinates. -/
def msgCoords (L : EncLeaf) : List Coord := (msgSlots L).map Prod.fst

/-- The honest message of a source leaf from coordinate values (zero pad). -/
def msgOf (L : EncLeaf) (f : Coord → Digest) : LayerMessage :=
  if h : L.1.lay.val < 3 then
    (f (.inl (.node (childNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) 0))), 0,
      f (.inl (.node (childNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) 1))))
  else (f (.inl (.forest (childIndex L))), 0, 0)

/-- The first hidden message coordinate (with the message component that carries it), if any. -/
noncomputable def firstUnknownMsg (K : Coord → Prop) (L : EncLeaf) : Option (Coord × (LayerMessage → Digest)) :=
  (msgSlots L).find? fun p => decide (¬K p.1)

theorem msgSlots_proj (L : EncLeaf) (f : Coord → Digest) : ∀ p ∈ msgSlots L, p.2 (msgOf L f) = f p.1 := by
  intro p hp
  unfold msgSlots at hp
  unfold msgOf
  split_ifs at hp ⊢ with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; rfl

theorem msgOf_congr (L : EncLeaf) (f g : Coord → Digest) (h : ∀ c ∈ msgCoords L, f c = g c) :
    msgOf L f = msgOf L g := by
  unfold msgCoords msgSlots at h
  unfold msgOf
  split_ifs at h ⊢ with hl
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h
    rw [h.1, h.2]
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at h
    rw [h]

theorem firstUnknownMsg_some {K : Coord → Prop} {L : EncLeaf} {p : Coord × (LayerMessage → Digest)}
    (h : firstUnknownMsg K L = some p) : p ∈ msgSlots L ∧ ¬K p.1 := by
  unfold firstUnknownMsg at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨hm, hp⟩

theorem firstUnknownMsg_none {K : Coord → Prop} {L : EncLeaf} (h : firstUnknownMsg K L = none) :
    ∀ c ∈ msgCoords L, K c := by
  unfold firstUnknownMsg at h
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  have := List.find?_eq_none.mp h p hp
  simpa using this

/-- Contact of a query at a parsed source position: the first unknown child's slot holds its honest value (guess),
or a non-honest input answers the honest label (hit). -/
def StructuralContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ N : CanonGraph.Node, Extract.posOf input = some N.toPos ∧
    ((∃ cs, firstUnknown K N = some cs ∧ slotValue input cs.2 = honestValue A cs.1) ∨
      (input ≠ Extract.honestInput A N.toPos ∧ answer.extractLsb' 0 128 = honestValue A (.inl N)))

/-- Contact of an encoding row of a source leaf: its message is the hidden honest message (guess), or it is not the
reference row and decodes to the reference word (hit). -/
def EncodingContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ (L : EncLeaf) (m : (Digest × BitVec 96 × Digest)) (ctr : BitVec 32), input = Wots.encodingRow L.toWots m ctr ∧
    ((∃ p, firstUnknownMsg K L = some p ∧ p.2 m = honestValue A p.1) ∨
      (Wots.referenceInput A L.toWots ≠ some input ∧
        decode L.1.lay (answer.extractLsb' 0 128) = some (Wots.referenceDigits A L.toWots)))

/-- **The large-route contact test** of one adversary/verifier public query. -/
def ContactTest (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  StructuralContact A K input answer ∨ EncodingContact A K input answer

/-- Digest rows (charged as one unit of creation mass, never a contact). -/
def IsDigestRow (input : HashInput) : Prop :=
  ∃ (rho : Digest) (message : Message) (counter : BitVec 32), input = pad64 (digestInput rho message counter)

end SigGolfCandidate.T3.Security.LargeResidual
