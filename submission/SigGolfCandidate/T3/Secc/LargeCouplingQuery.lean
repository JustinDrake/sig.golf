import SigGolfCandidate.T3.Secc.LargeCouplingObserved
import SigGolfCandidate.T3.Secc.LargeCouplingSign
import SigGolfCandidate.T3.Secc.LargeCouplingTrace
import SigGolfCandidate.T3.Secc.WotsStructuralHonest
import SigGolfCandidate.T3.Secc.WotsClasses

/-!
# LR-34 (coupling, one query): the router answers a query exactly as the monitor tests it

Fix an eager answers table `T` and the router's data: hidden values `vals : Coord → Digest`, residual table
`τ : Cell U → HashOutput`, presampled `a : AuxData`, related by **`Coherent`** (the canonical labels are
`joinLabels (vals ∘ inl) a.high`, the secrets are `vals ∘ inr`, every non-honest row of `U` outside the presampled
honest-message prefixes is `τ`, those prefixes are `a.rows`, the honest searches are the presampled selections, the
non-secret, non-nonce private coordinates are `a.priv`, the nonces' low halves are `nv`, and inputs outside `U`
answer `0`).

**`Rel`** relates a monitor state, a router state and an eager world state (same disclosures, inputs, calls, digest
count = mass, no contact yet; every hidden coordinate still has `2^128 − probes` candidates containing its value;
cached rows are `τ` rows of seen inputs or digest rows; seen honest cells have all children known; seen honest-message
encoding rows have their message known).

**`routeQuery_observed`**: one adversary/verifier query within the budget — the router's eager observed run is a single
outcome: it stops exactly when the monitor contacts, otherwise it answers `T X` and `Rel` is preserved.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingQuery : DecidableEq T3.Cache := Classical.decEq _

/-! ## Coherence of an eager table with the router's data -/

/-- The canonical labels of the router's data. -/
noncomputable def routerLabels (vals : Coord → Digest) (a : AuxData) : Labels :=
  joinLabels (fun N => vals (.inl N)) a.high

/-- An honest-message encoding row of a route leaf inside the presampled first-success prefix. -/
def HonestPrefix (vals : Coord → Digest) (a : AuxData) (X : HashInput) : Prop :=
  ∃ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr ∧ PrefixRow a L ctr

/-- **Coherence** of an eager answers table with the router's hidden values, residual table and presampled data. -/
structure Coherent (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) : Prop where
  agrees : Agrees T (routerLabels vals a)
  secrets : secretsOf T = fun s => vals (.inr s)
  residual : ∀ (X : HashInput) (hX : X ∈ U), (∀ N : CanonGraph.Node, X ≠ cell (secretsOf T) N (routerLabels vals a)) →
    ¬HonestPrefix vals a X → T (.inl (.inr X)) = τ ⟨X, hX⟩
  prefixRow : ∀ (L : EncLeaf) (ctr : BitVec 32), PrefixRow a L ctr →
    T (.inl (.inr (Wots.encodingRow L.toWots (vals (msgCoord L)) ctr))) = prefixValue a L ctr
  search : ∀ L : EncLeaf, Wots.referenceSearch T L.toWots =
    (a.sel L).bind fun r => (decode L.1.lay r.2).map fun d => (BitVec.ofNat 32 r.1.val, d)
  priv : ∀ c : Coordinate, (∀ i : Fin 2, (c, i) ∉ Set.range secretCoordinate) → (∀ m : Message, c ≠ .inr (.inl m)) →
    T (.inr c) = a.priv c
  outside : ∀ X, X ∉ U → T (.inl (.inr X)) = (0 : HashOutput)
  nonce : ∀ m : Message, (T (.inr (.inr (.inl m)))).extractLsb' 0 128 = nv m

section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}

theorem Coherent.honestValue (h : Coherent U T vals nv τ a) : LargeResidual.honestValue T = vals := by
  rw [honestValue_eq h.agrees, h.secrets]
  funext c
  cases c with
  | inl N => exact joinLabels_low _ _ N
  | inr s => rfl

/-- The honest input of a node is the cell of its children's values. -/
theorem Coherent.honestInput (h : Coherent U T vals nv τ a) (N : CanonGraph.Node) :
    Extract.honestInput T N.toPos = cellValues N vals := by
  rw [honestInput_eq h.agrees N, cell_eq_cellValues]
  congr 1
  rw [h.secrets]
  funext c
  cases c with
  | inl M => exact joinLabels_low _ _ M
  | inr s => rfl

theorem Coherent.cell (h : Coherent U T vals nv τ a) (N : CanonGraph.Node) :
    cell (secretsOf T) N (routerLabels vals a) = cellValues N vals := by
  rw [← honestInput_eq h.agrees N, h.honestInput N]

theorem Coherent.honest_answer (h : Coherent U T vals nv τ a) (N : CanonGraph.Node) :
    T (.inl (.inr (cellValues N vals))) = routerLabels vals a N := by
  rw [← h.honestInput N]
  exact CanonGraph.honest_answer h.agrees N

/-- The honest message of a route leaf is its message coordinate's value. -/
theorem Coherent.leafMsg (h : Coherent U T vals nv τ a) (L : EncLeaf) :
    Wots.leafMsg T L.toWots = vals (msgCoord L) := by
  rw [leafMsg_eq h.agrees L]
  unfold msgLabel msgCoord
  by_cases hl : L.1.lay.val < 3
  · rw [dif_pos hl, dif_pos hl, treeLabel_root]
    exact joinLabels_low _ _ _
  · rw [dif_neg hl, dif_neg hl]
    exact joinLabels_low _ _ _

end Coherent

/-! ## Structural facts -/

theorem encodingRow_parsed_none (L : Wots.LeafAddr) (m : Digest) (c : BitVec 32) :
    Extract.posOf (Wots.encodingRow L m c) = none :=
  Wots.Structural.posOf_encoding _ _ _ _ _

theorem digestRow_parsed_none {X : HashInput} (h : IsDigestRow X) : Extract.posOf X = none := by
  obtain ⟨rho, m, c, rfl⟩ := h
  exact Wots.Structural.posOf_digest _ _ _

theorem not_parsed_of_digest {X : HashInput} (h : IsDigestRow X) : ¬Parsed X := by
  rintro ⟨N, hN⟩
  rw [digestRow_parsed_none h] at hN
  cases hN

theorem not_parsed_of_encRow {X : HashInput} (h : EncRow X) : ¬Parsed X := by
  rintro ⟨N, hN⟩
  obtain ⟨L, m, c, rfl⟩ := h
  rw [encodingRow_parsed_none] at hN
  cases hN

theorem cellValues_parsed (N : CanonGraph.Node) (v : Coord → Digest) (s : Secrets) (labels : Labels)
    (hv : cellValues N v = cell s N labels) : Extract.posOf (cellValues N v) = some N.toPos := by
  rw [hv]
  exact posOf_cell s N labels

/-- Encoding rows of route leaves determine the leaf, the message and the counter. -/
theorem encodingRow_encLeaf_injective {L L' : EncLeaf} {m m' : Digest} {c c' : BitVec 32}
    (h : Wots.encodingRow L.toWots m c = Wots.encodingRow L'.toWots m' c') : L = L' ∧ m = m' ∧ c = c' := by
  have hb := congrArg Extract.hdrBlock h
  rw [Wots.SmallA.hdrBlock_encodingRow, Wots.SmallA.hdrBlock_encodingRow] at hb
  have hlay := L.1.lay.isLt
  have hlay' := L'.1.lay.isLt
  have htree := L.1.tree.isLt
  have htree' := L'.1.tree.isLt
  have hleaf := L.1.leaf.isLt
  have hleaf' := L'.1.leaf.isLt
  have fields := header_injective (by decide : 4 < 256) (by omega) (by simp [EncLeaf.toWots]; omega)
    (by decide) (by simp [EncLeaf.toWots]; omega) (by decide : 4 < 256) (by omega)
    (by simp [EncLeaf.toWots]; omega) (by decide) (by simp [EncLeaf.toWots]; omega) (bytesLE_injective hb)
  simp only [EncLeaf.toWots] at fields
  have hL : L = L' := by
    obtain ⟨⟨lay, tree, leaf⟩, hs⟩ := L
    obtain ⟨⟨lay', tree', leaf'⟩, hs'⟩ := L'
    simp only at fields
    have e1 : lay = lay' := Fin.ext fields.2.1
    have e2 : tree = tree' := Fin.ext fields.2.2.1
    have e3 : leaf = leaf' := Fin.ext fields.2.2.2.2
    subst e1 e2 e3
    rfl
  subst hL
  exact ⟨rfl, WotsExtract.encodingRow_injective h⟩

/-- A child's coordinate is never its parent node. -/
theorem childSlots_ne (N : CanonGraph.Node) : ∀ cs ∈ childSlots N, cs.1 ≠ .inl N := by
  intro cs hcs
  cases N with
  | chain p =>
      simp only [childSlots, List.mem_singleton] at hcs
      subst hcs
      unfold chainChild
      split_ifs with h0
      · exact Sum.inl_ne_inr.symm
      · intro heq
        have h1 := congrArg (fun c : Coord => match c with | .inl (.chain x) => x.2.val | _ => 0) heq
        simp only [ChainGraph.predecessor] at h1
        omega
  | leaf L =>
      simp only [childSlots, List.mem_map] at hcs
      obtain ⟨i, -, rfl⟩ := hcs
      simp
  | node n =>
      simp only [childSlots, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at hcs
      rcases hcs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ <;>
      · unfold treeChild at hc
        split_ifs at hc with hl
        · obtain ⟨⟩ := hc
          simp
        · simp only [Option.map_eq_some_iff] at hc
          obtain ⟨m, hm, rfl⟩ := hc
          intro heq
          have hlev := treeNodeAt_level hm
          have hmn : m = n := by
            simp only [Sum.inl.injEq, CanonGraph.Node.node.injEq] at heq
            exact heq
          subst hmn
          omega
  | ftsLeaf f =>
      simp only [childSlots, List.mem_singleton] at hcs
      subst hcs
      exact Sum.inr_ne_inl
  | ftsNode n =>
      simp only [childSlots, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at hcs
      rcases hcs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ <;>
      · unfold ftsChild at hc
        split_ifs at hc with hl
        · obtain ⟨⟩ := hc
          simp
        · simp only [Option.map_eq_some_iff] at hc
          obtain ⟨m, hm, rfl⟩ := hc
          intro heq
          have hlev := ftsNodeAt_level hm
          have hmn : m = n := by
            simp only [Sum.inl.injEq, CanonGraph.Node.ftsNode.injEq] at heq
            exact heq
          subst hmn
          omega
  | forest index =>
      simp only [childSlots, List.mem_map] at hcs
      obtain ⟨i, -, rfl⟩ := hcs
      simp

theorem firstUnknown_some {K : Coord → Prop} {N : CanonGraph.Node} {cs : Coord × Nat}
    (h : firstUnknown K N = some cs) : cs ∈ childSlots N ∧ ¬K cs.1 := by
  unfold firstUnknown at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨hm, hp⟩

theorem firstUnknown_none {K : Coord → Prop} {N : CanonGraph.Node} (h : firstUnknown K N = none) :
    ∀ cs ∈ childSlots N, K cs.1 := by
  unfold firstUnknown at h
  intro cs hcs
  have := List.find?_eq_none.mp h cs hcs
  simpa using this

/-! ## The contact test by input kind -/

theorem contactTest_parsed {A : Answers} {K : Coord → Prop} {X : HashInput} {y : HashOutput} {N : CanonGraph.Node}
    (hN : Extract.posOf X = some N.toPos) :
    ContactTest A K X y ↔
      (∃ cs, firstUnknown K N = some cs ∧ slotValue X cs.2 = LargeResidual.honestValue A cs.1) ∨
        (X ≠ Extract.honestInput A N.toPos ∧ y.extractLsb' 0 128 = LargeResidual.honestValue A (.inl N)) := by
  constructor
  · rintro (⟨N', hN', h⟩ | ⟨L, m, c, hX, -⟩)
    · rw [hN] at hN'
      have := toPos_injective (Option.some.inj hN')
      subst this
      exact h
    · rw [hX, encodingRow_parsed_none] at hN
      cases hN
  · intro h
    exact Or.inl ⟨N, hN, h⟩

theorem contactTest_enc {A : Answers} {K : Coord → Prop} {y : HashOutput} {L : EncLeaf} {m : Digest}
    {c : BitVec 32} :
    ContactTest A K (Wots.encodingRow L.toWots m c) y ↔
      (¬K (msgCoord L) ∧ m = LargeResidual.honestValue A (msgCoord L)) ∨
        (Wots.referenceInput A L.toWots ≠ some (Wots.encodingRow L.toWots m c) ∧
          decode L.1.lay (y.extractLsb' 0 128) = some (Wots.referenceDigits A L.toWots)) := by
  constructor
  · rintro (⟨N', hN', -⟩ | ⟨L', m', c', hX, h⟩)
    · rw [encodingRow_parsed_none] at hN'
      cases hN'
    · obtain ⟨rfl, rfl, rfl⟩ := encodingRow_encLeaf_injective hX
      exact h
  · intro h
    exact Or.inr ⟨L, m, c, rfl, h⟩

theorem contactTest_other {A : Answers} {K : Coord → Prop} {X : HashInput} {y : HashOutput}
    (hp : ¬Parsed X) (he : ¬EncRow X) : ¬ContactTest A K X y := by
  rintro (⟨N, hN, -⟩ | ⟨L, m, c, hX, -⟩)
  · exact hp ⟨N, hN⟩
  · exact he ⟨L, m, c, hX⟩

/-! ## Encoding references under coherence -/

theorem low_eq (y : HashOutput) : low y = y.extractLsb' 0 128 := rfl

theorem sel_valid (a : AuxData) (L : EncLeaf) (r : Fin (2 ^ 22) × Digest) (hr : a.sel L = some r) :
    ∃ w, decode L.1.lay r.2 = some w := by
  have h := (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ _ r.1 r.2).mp hr
  obtain ⟨-, hs⟩ := (decodeAt_eq_some L _ r.2).mp h.1
  exact Option.isSome_iff_exists.mp hs

theorem dummyDigest_decode' (lay : Layer) : decode lay (dummyDigest lay) = some (Wots.dummyDigits lay) :=
  Classical.choose_spec (Wots.dummyDigits_valid lay)

section Reference
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}

theorem Coherent.referenceDigits (h : Coherent U T vals nv τ a) (L : EncLeaf) :
    Wots.referenceDigits T L.toWots = ((a.sel L).bind fun r => decode L.1.lay r.2).getD (Wots.dummyDigits L.1.lay) := by
  unfold Wots.referenceDigits
  rw [h.search]
  cases hs : a.sel L with
  | none => rfl
  | some r =>
      simp only [Option.bind_some]
      cases decode L.1.lay r.2 <;> rfl

theorem Coherent.referenceInput (h : Coherent U T vals nv τ a) (L : EncLeaf) (X : HashInput)
    (hX : Wots.referenceInput T L.toWots = some X) :
    ∃ r, a.sel L = some r ∧ X = Wots.encodingRow L.toWots (vals (msgCoord L)) (BitVec.ofNat 32 r.1.val) := by
  unfold Wots.referenceInput at hX
  rw [h.search, h.leafMsg] at hX
  cases hs : a.sel L with
  | none => rw [hs] at hX; cases hX
  | some r =>
      rw [hs] at hX
      simp only [Option.bind_some, Option.map_map] at hX
      cases hd : decode L.1.lay r.2 with
      | none => rw [hd] at hX; cases hX
      | some w =>
          rw [hd] at hX
          exact ⟨r, rfl, (Option.some.inj hX).symm⟩

/-- **The reference-digest hit is a single digest** (decoder injectivity). -/
theorem Coherent.decode_ref (h : Coherent U T vals nv τ a) (L : EncLeaf) (d : Digest) :
    decode L.1.lay d = some (Wots.referenceDigits T L.toWots) ↔ d = refDigest a L := by
  rw [h.referenceDigits L]
  unfold refDigest
  cases hs : a.sel L with
  | none =>
      simp only [Option.bind_none, Option.getD_none]
      constructor
      · intro hd
        exact decode_some_injective hd (dummyDigest_decode' L.1.lay)
      · rintro rfl
        exact dummyDigest_decode' L.1.lay
  | some r =>
      obtain ⟨w, hw⟩ := sel_valid a L r hs
      simp only [Option.bind_some, hw, Option.getD_some]
      constructor
      · intro hd
        exact decode_some_injective hd hw
      · rintro rfl
        exact hw

/-- A presampled prefix row decoding to the reference word is the reference row itself. -/
theorem Coherent.prefix_ref (h : Coherent U T vals nv τ a) (L : EncLeaf) (ctr : BitVec 32) (hp : PrefixRow a L ctr)
    (hd : decode L.1.lay ((prefixValue a L ctr).extractLsb' 0 128) = some (Wots.referenceDigits T L.toWots)) :
    Wots.referenceInput T L.toWots = some (Wots.encodingRow L.toWots (vals (msgCoord L)) ctr) := by
  obtain ⟨hlt, hle⟩ := hp
  have hpv : prefixValue a L ctr = a.rows L ⟨ctr.toNat, hlt⟩ := by unfold prefixValue; rw [dif_pos hlt]
  rw [hpv] at hd
  cases hs : a.sel L with
  | none =>
      have hn := (SphincsSecurity.Concrete.FirstSuccessTable.select_none_iff _ _).mp hs ⟨ctr.toNat, hlt⟩
      rw [decodeAt_eq_none] at hn
      rw [hn] at hd
      cases hd
  | some r =>
      have hsel := (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ _ r.1 r.2).mp hs
      have hle' := hle r hs
      rcases Nat.lt_or_ge ctr.toNat r.1.val with hlt' | hge
      · have hn := hsel.2 ⟨ctr.toNat, hlt⟩ hlt'
        rw [decodeAt_eq_none] at hn
        rw [hn] at hd
        cases hd
      · have heq : ctr.toNat = r.1.val := by omega
        unfold Wots.referenceInput
        rw [h.search, h.leafMsg, hs]
        obtain ⟨w, hw⟩ := sel_valid a L r hs
        simp only [Option.bind_some, hw, Option.map_some]
        congr 2
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, ← heq]
        exact Nat.mod_eq_of_lt (by omega)

end Reference

/-! ## The relation between monitor, router and world states -/

/-- **The simulation relation** (no contact yet). -/
structure Rel (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) : Prop where
  disclosed : mon.disclosed = st.disclosed
  seen : mon.seen = st.seen
  calls : mon.calls = st.calls
  wcalls : ws.counters.calls = st.calls
  digests : mon.digests = ws.counters.mass
  contact : mon.contact = false
  probes : ws.counters.probes ≤ ws.counters.calls
  budget : st.calls ≤ q
  mem : ∀ c, Sum.elim vals nv c ∈ ws.candidates c
  hidden : ∀ c, ¬st.known c → 2 ^ 128 - ws.counters.probes ≤ (ws.candidates (.inl c)).card
  rowsEq : ∀ row v, ws.rows row = some v → v = τ row
  rowsSeen : ∀ row v, ws.rows row = some v → row.val ∈ st.seen ∨ IsDigestRow row.val
  seenCells : ∀ X ∈ st.seen, X ∈ U → ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1
  seenEnc : ∀ X ∈ st.seen, X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32),
    X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr → st.known (msgCoord L)

section Relation
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}

theorem Rel.known (h : Rel U T vals nv τ a q mon st ws) : mon.known = st.known := by
  unfold Monitor.known RouterState.known
  rw [h.disclosed]

/-- The monitor on one query within the budget. -/
theorem Rel.query (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (y : HashOutput) :
    mon.query U T q X y =
      if X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X y then
        ⟨mon.disclosed, X :: mon.seen, mon.calls + 1, mon.digests, true⟩
      else ⟨mon.disclosed, X :: mon.seen, mon.calls + 1,
        mon.digests + (if X ∈ U ∧ IsDigestRow X then 1 else 0), false⟩ := by
  have hc : mon.calls + 1 ≤ q := by rw [h.calls]; omega
  unfold Monitor.query
  rw [if_neg (by rw [h.contact]; decide), h.known, h.seen]
  by_cases ht : X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X y
  · rw [if_pos ⟨ht.1, ht.2.1, hc, ht.2.2⟩, if_pos ht]
  · rw [if_neg (fun h' => ht ⟨h'.1, h'.2.1, h'.2.2.2⟩), if_neg ht]
    by_cases hd : X ∈ U ∧ IsDigestRow X
    · rw [if_pos ⟨hd.1, hd.2, hc⟩, if_pos hd]
    · rw [if_neg (fun h' => hd ⟨h'.1, h'.2.1⟩), if_neg hd]

/-- Hidden coordinates have at least two candidates. -/
theorem Rel.two_le (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (c : Coord)
    (hc : ¬st.known c) : 2 ≤ (ws.candidates (.inl c)).card := by
  have h1 := h.hidden c hc
  have h2 := h.probes
  have h3 := h.wcalls
  omega

/-- **One step of the relation** (a non-contact query). -/
theorem Rel.next (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (ws' : LargeResidual.State WCoord (Cell U)) (δ : Nat)
    (hcalls : ws'.counters.calls = st.calls + 1) (hmass : ws'.counters.mass = ws.counters.mass + δ)
    (hprobes : ws'.counters.probes ≤ ws'.counters.calls)
    (hmem : ∀ c, Sum.elim vals nv c ∈ ws'.candidates c)
    (hhidden : ∀ c, ¬st.known c → 2 ^ 128 - ws'.counters.probes ≤ (ws'.candidates (.inl c)).card)
    (hrowsEq : ∀ row v, ws'.rows row = some v → v = τ row)
    (hrowsSeen : ∀ row v, ws'.rows row = some v → row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val)
    (hcell : X ∈ U → ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L))
    (st' : RouterState) (hd : st'.disclosed = st.disclosed) (hs : st'.seen = X :: st.seen)
    (hc : st'.calls = st.calls + 1) :
    Rel U T vals nv τ a q ⟨mon.disclosed, X :: mon.seen, mon.calls + 1, mon.digests + δ, false⟩ st' ws' := by
  have hk : st'.known = st.known := by unfold RouterState.known; rw [hd]
  refine ⟨by rw [hd]; exact h.disclosed, by rw [hs, h.seen], by rw [hc, h.calls], by rw [hcalls, hc], ?_, rfl,
    hprobes, (show st'.calls ≤ q by omega), hmem, ?_, hrowsEq, ?_, ?_, ?_⟩
  · simp only [hmass, h.digests]
  · rw [hk]; exact hhidden
  · intro row v hv
    rw [hs]
    rcases hrowsSeen row v hv with h1 | h1 | h1
    · exact Or.inl (by rw [h1]; exact List.mem_cons_self)
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · exact Or.inr h1
  · intro Y hY hYU N hN cs hcs
    rw [hk]
    rw [hs] at hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact hcell hYU N hN cs hcs
    · exact h.seenCells Y hY hYU N hN cs hcs
  · intro Y hY hYU L ctr hL
    rw [hk]
    rw [hs] at hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact henc hYU L ctr hL
    · exact h.seenEnc Y hY hYU L ctr hL

end Relation

/-! ## One query: the outcome -/

theorem _root_.SigGolfCandidate.T3.Security.LargeResidual.RouterState.next_of_not (U : Finset HashInput) (st : RouterState) (X : HashInput) (y : HashOutput)
    (h : ¬(X ∈ U ∧ IsDigestRow X)) : st.next U X y = st.after X := by
  unfold RouterState.next
  rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]

/-- The outcome of one routed query: a stop exactly when the monitor contacts (mass = the monitor's digests), or the
answer `T X` with the relation preserved. -/
def QueryOutcome (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U))
    (X : HashInput) (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U))) : Prop :=
  ∃ ws' : LargeResidual.State WCoord (Cell U),
    ((mon.query U T q X (T (.inl (.inr X)))).contact = true ∧ out = pure (none, ws') ∧
        ws'.counters.mass = mon.digests ∧ ws'.counters.calls ≤ q) ∨
      ((mon.query U T q X (T (.inl (.inr X)))).contact = false ∧
        out = pure (some (T (.inl (.inr X)), st.next U X (T (.inl (.inr X)))), ws') ∧
        Rel U T vals nv τ a q (mon.query U T q X (T (.inl (.inr X)))) (st.next U X (T (.inl (.inr X)))) ws')

section Query
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))

theorem observed_map {β γ : Type} (f : β → γ) (c : OracleComp (RWorld U) β) (s : LargeResidual.State WCoord (Cell U)) :
    observedRun aux q (Sum.elim vals nv) τ (f <$> c) s = (fun r => (r.1.map f, r.2)) <$> observedRun aux q (Sum.elim vals nv) τ c s :=
  runWith_map _ f c s

theorem observed_testReq (st' : RouterState) (X : HashInput) (hX : X ∈ U) (test : Probe WCoord)
    (hfresh : X ∉ st.seen → ws.rows ⟨X, hX⟩ = none) :
    observedRun aux q (Sum.elim vals nv) τ ((fun y => (y, st')) <$> testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ test) ws =
      if X ∉ st.seen then
        (if (test.effective ws.candidates).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) then
          pure (some (τ ⟨X, hX⟩, st'), probeState ws ⟨X, hX⟩ (test.effective ws.candidates) (τ ⟨X, hX⟩))
        else pure (none, stoppedState ws))
      else pure (some (τ ⟨X, hX⟩, st'), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call) := by
  rw [observed_map]
  by_cases hs : X ∈ st.seen
  · have hd : decide (X ∉ st.seen) = false := by simp [hs]
    rw [hd, if_neg (not_not.mpr hs)]
    simp only [testReq, Bool.false_eq_true, if_false]
    rw [← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
    rfl
  · have hd : decide (X ∉ st.seen) = true := by simp [hs]
    rw [hd, if_pos hs]
    simp only [testReq, if_true]
    rw [← bind_pure (probeReq U ⟨X, hX⟩ test), observed_probeReq_fresh U aux q (Sum.elim vals nv) τ _ _ _ _ (hfresh hs)]
    split_ifs
    · rw [observed_pure, map_pure]; rfl
    · rw [map_pure]; rfl

/-- An admissible probe is its own effective probe. -/
theorem effective_self {C : Type} [DecidableEq C] (cand : C → Finset Digest) (test : Probe C)
    (h : ∀ g ∈ test.guess, 2 ≤ (cand g.1).card ∧ ∀ parent, test.hit = Hit.label parent → g.1 ≠ parent) :
    test.effective cand = test := by
  obtain ⟨guess, hit⟩ := test
  unfold Probe.effective
  cases guess with
  | none => rfl
  | some g =>
      have hg' := h g rfl
      simp only [Option.filter_some, Probe.Admissible, decide_eq_true_eq]
      rw [if_pos hg']

theorem keep_guess_label {C : Type} (vals : C → Digest) (c p : C) (m : Digest) (y : HashOutput) :
    (⟨some (c, m), .label p⟩ : Probe C).keep vals y ↔ vals c ≠ m ∧ vals p ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]

theorem keep_label {C : Type} (vals : C → Digest) (p : C) (y : HashOutput) :
    (⟨none, .label p⟩ : Probe C).keep vals y ↔ vals p ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]

theorem keep_target {C : Type} (vals : C → Digest) (t : Digest) (y : HashOutput) :
    (⟨none, .target t⟩ : Probe C).keep vals y ↔ t ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]

theorem keep_guess_target {C : Type} (vals : C → Digest) (c : C) (m t : Digest) (y : HashOutput) :
    (⟨some (c, m), .target t⟩ : Probe C).keep vals y ↔ vals c ≠ m ∧ t ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]

end Query

/-! ## One query: the cases -/

section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))

theorem outcome_stop (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U)))
    (hc : X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X))))
    (hout : out = pure (none, stoppedState ws)) :
    QueryOutcome U T vals nv τ a q mon st ws X out := by
  refine ⟨stoppedState ws, Or.inl ⟨?_, hout, ?_, ?_⟩⟩
  · rw [hrel.query hlt, if_pos hc]
  · exact hrel.digests.symm
  · show ws.counters.calls + 1 ≤ q
    rw [hrel.wcalls]
    omega

theorem outcome_continue (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U)))
    (hc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (ws' : LargeResidual.State WCoord (Cell U))
    (hout : out = pure (some (T (.inl (.inr X)), st.next U X (T (.inl (.inr X)))), ws'))
    (hcalls : ws'.counters.calls = st.calls + 1)
    (hmass : ws'.counters.mass = ws.counters.mass + (if X ∈ U ∧ IsDigestRow X then 1 else 0))
    (hprobes : ws'.counters.probes ≤ ws'.counters.calls)
    (hmem : ∀ c, Sum.elim vals nv c ∈ ws'.candidates c)
    (hhidden : ∀ c, ¬st.known c → 2 ^ 128 - ws'.counters.probes ≤ (ws'.candidates (.inl c)).card)
    (hrowsEq : ∀ row v, ws'.rows row = some v → v = τ row)
    (hrowsSeen : ∀ row v, ws'.rows row = some v → row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val)
    (hcell : X ∈ U → ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L)) :
    QueryOutcome U T vals nv τ a q mon st ws X out := by
  refine ⟨ws', Or.inr ⟨?_, hout, ?_⟩⟩
  · rw [hrel.query hlt, if_neg hc]
  · rw [hrel.query hlt, if_neg hc]
    refine hrel.next hlt X ws' _ hcalls hmass hprobes hmem hhidden hrowsEq hrowsSeen hcell henc _ ?_ ?_ ?_ <;>
    · unfold RouterState.next
      split_ifs <;> rfl

/-- Rows of inputs never seen and not digest rows are fresh. -/
theorem Rel.fresh (hrel : Rel U T vals nv τ a q mon st ws) (X : HashInput) (hX : X ∈ U) (hd : ¬IsDigestRow X)
    (hs : X ∉ st.seen) : ws.rows ⟨X, hX⟩ = none := by
  cases hr : ws.rows ⟨X, hX⟩ with
  | none => rfl
  | some v =>
      rcases hrel.rowsSeen _ v hr with h | h
      · exact absurd h hs
      · exact absurd h hd

/-- A parsed input other than the honest cell of its node is no honest cell. -/
theorem Coherent.not_cell_parsed (hcoh : Coherent U T vals nv τ a) {X : HashInput} {N : CanonGraph.Node}
    (hN : Extract.posOf X = some N.toPos) (hne : X ≠ cellValues N vals) :
    ∀ N' : CanonGraph.Node, X ≠ cellValues N' vals := by
  intro N' heq
  have hp : Extract.posOf X = some N'.toPos := by
    rw [heq, ← hcoh.cell N']
    exact posOf_cell _ _ _
  rw [hN] at hp
  have := toPos_injective (Option.some.inj hp)
  subst this
  exact hne heq

theorem not_cell_unparsed (hcoh : Coherent U T vals nv τ a) {X : HashInput} (hp : ¬Parsed X) :
    ∀ N' : CanonGraph.Node, X ≠ cellValues N' vals := by
  intro N' heq
  apply hp
  refine ⟨N', ?_⟩
  rw [heq, ← hcoh.cell N']
  exact posOf_cell _ _ _

theorem not_prefix_parsed {X : HashInput} (hp : Parsed X) : ¬HonestPrefix vals a X := by
  rintro ⟨L, ctr, rfl, -⟩
  exact not_parsed_of_encRow ⟨L, _, ctr, rfl⟩ hp

theorem not_prefix_enc {X : HashInput} (he : ¬EncRow X) : ¬HonestPrefix vals a X := by
  rintro ⟨L, ctr, rfl, -⟩
  exact he ⟨L, _, ctr, rfl⟩

theorem not_enc_parsed {X : HashInput} (hp : Parsed X) (L : EncLeaf) (m : Digest) (ctr : BitVec 32) :
    X ≠ Wots.encodingRow L.toWots m ctr := by
  rintro rfl
  exact not_parsed_of_encRow ⟨L, m, ctr, rfl⟩ hp

/-- **Case A**: an input outside the universe (a tick, answer `0`). -/
theorem case_outside (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q)
    (X : HashInput) (hX : X ∉ U) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (tickReq U .call >>= fun _ =>
      pure ((0 : HashOutput), st.after X)) ws) := by
  rw [observed_tickReq, observed_pure]
  apply outcome_continue hrel hlt X _ (fun h => hX h.2.1) (tickState q ws .call)
  · rw [hcoh.outside X hX, RouterState.next_of_not U st X _ (fun h' => hX h'.1)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hX h.1), Nat.add_zero]
  · show ws.counters.probes ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact hrel.mem
  · exact hrel.hidden
  · exact hrel.rowsEq
  · intro row v hv; exact Or.inr (hrel.rowsSeen row v hv)
  · intro h; exact absurd h hX
  · intro h; exact absurd h hX

theorem rows_update_eq (hrel : Rel U T vals nv τ a q mon st ws) (row0 : Cell U) :
    ∀ row v, Function.update ws.rows row0 (some (τ row0)) row = some v → v = τ row := by
  intro row v hv
  by_cases hr : row = row0
  · subst hr
    rw [Function.update_self] at hv
    exact (Option.some.inj hv).symm
  · rw [Function.update_of_ne hr] at hv
    exact hrel.rowsEq row v hv

theorem rows_update_seen (hrel : Rel U T vals nv τ a q mon st ws) (X : HashInput) (hX : X ∈ U) :
    ∀ row v, Function.update ws.rows ⟨X, hX⟩ (some (τ ⟨X, hX⟩)) row = some v →
      row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val := by
  intro row v hv
  by_cases hr : row = ⟨X, hX⟩
  · exact Or.inl (by rw [hr])
  · rw [Function.update_of_ne hr] at hv
    exact Or.inr (hrel.rowsSeen row v hv)

/-- A read of a residual row (`.call`, or `.mass` for a digest row) that is not a contact. -/
theorem continue_read (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U)
    (ch : Charge) (hch : (ch = .call ∧ ¬IsDigestRow X) ∨ (ch = .mass ∧ IsDigestRow X))
    (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L)) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.next U X (τ ⟨X, hX⟩)),
        readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) ch)) := by
  apply outcome_continue hrel hlt X _ hnc (readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) ch)
  · rw [hTX]
  · rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    · show ws.counters.calls + 1 = st.calls + 1
      rw [hrel.wcalls]
  · rcases hch with ⟨rfl, hd⟩ | ⟨rfl, hd⟩
    · show ws.counters.mass = ws.counters.mass + _
      rw [if_neg (fun h => hd h.2), Nat.add_zero]
    · show ws.counters.mass + (if ws.counters.calls + 1 ≤ q then 1 else 0) = ws.counters.mass + _
      rw [if_pos (show ws.counters.calls + 1 ≤ q by rw [hrel.wcalls]; omega),
        if_pos (show X ∈ U ∧ IsDigestRow X from ⟨hX, hd⟩)]
  · have := hrel.probes
    rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · show ws.counters.probes ≤ ws.counters.calls + 1
      omega
    · show ws.counters.probes ≤ ws.counters.calls + 1
      omega
  · exact hrel.mem
  · rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hrel.hidden
    · exact hrel.hidden
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc

theorem continue_read_call (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (hX : X ∈ U) (hnd : ¬IsDigestRow X) (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L)) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.after X), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call)) := by
  have h := continue_read hrel hlt X hX .call (Or.inl ⟨rfl, hnd⟩) hTX hnc hcell henc
  rwa [RouterState.next_of_not U st X _ (fun h' => hnd h'.2)] at h

/-- A fresh probe that survives (no contact). -/
theorem continue_probe (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U)
    (test : Probe WCoord) (hk : test.keep (Sum.elim vals nv) (τ ⟨X, hX⟩))
    (hadm : ∀ g ∈ test.guess, ∀ parent, test.hit = Hit.label parent → g.1 ≠ parent)
    (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩) (hnd : ¬IsDigestRow X)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L)) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.after X),
        probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))) := by
  apply outcome_continue hrel hlt X _ hnc (probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))
  · rw [hTX, RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hnd h.2), Nat.add_zero]
  · show ws.counters.probes + 1 ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact (mem_restrict test ws.candidates (τ ⟨X, hX⟩) (Sum.elim vals nv)).mpr ⟨hrel.mem, hk.1, by
      rcases test with ⟨g, hit⟩
      cases hit with
      | label p => exact hk.2
      | target t => trivial⟩
  · intro c hc
    have h1 := hrel.hidden c hc
    have h2 := card_restrict_ge test ws.candidates (τ ⟨X, hX⟩) hadm (.inl c)
    show 2 ^ 128 - (ws.counters.probes + 1) ≤ (test.restrict ws.candidates (τ ⟨X, hX⟩) (.inl c)).card
    omega
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc

/-- **Case B**: a parsed input with an unknown child (guess of the first unknown child, label hit). -/
theorem case_unknownChild (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (X : HashInput) (hX : X ∈ U) (N : CanonGraph.Node)
    (hN : Extract.posOf X = some N.toPos) (cs : Coord × Nat) (hfu : firstUnknown st.known N = some cs) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩) ws) := by
  obtain ⟨hcsm, hcsk⟩ := firstUnknown_some hfu
  have hp : Parsed X := ⟨N, hN⟩
  have hnd : ¬IsDigestRow X := fun hd => not_parsed_of_digest hd hp
  have hadm : ∀ g ∈ (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).guess, ∀ parent,
      (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
    intro g hg parent hpar
    simp only [Option.mem_def, Option.some.injEq] at hg
    subst hg
    simp only [Hit.label.injEq] at hpar
    subst hpar
    exact fun h => childSlots_ne N cs hcsm (Sum.inl.inj h)
  have heff : (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).effective ws.candidates =
      ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ := by
    apply effective_self
    intro g hg
    refine ⟨?_, hadm g hg⟩
    simp only [Option.mem_def, Option.some.injEq] at hg
    subst hg
    exact hrel.two_le hlt hq cs.1 hcsk
  have hcomp := observed_testReq (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st) (ws := ws) aux
    (st.after X) X hX ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩
    (hrel.fresh X hX hnd)
  refine (congrArg (QueryOutcome U T vals nv τ a q mon st ws X) hcomp).mpr ?_
  rw [heff]
  have hct : ∀ y : HashOutput, ContactTest T st.known X y ↔
      slotValue X cs.2 = vals cs.1 ∨ (X ≠ cellValues N vals ∧ low y = vals (.inl N)) := by
    intro y
    rw [contactTest_parsed hN, hcoh.honestValue, hcoh.honestInput]
    constructor
    · rintro (⟨cs', hcs', h⟩ | h)
      · rw [hfu] at hcs'
        cases hcs'
        exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl ⟨cs, hfu, h⟩
      · exact Or.inr h
  have hres : X ≠ cellValues N vals → T (.inl (.inr X)) = τ ⟨X, hX⟩ := fun hXc =>
    hcoh.residual X hX (fun N' => by rw [hcoh.cell]; exact hcoh.not_cell_parsed hN hXc N') (not_prefix_parsed hp)
  have hcell : X ≠ cellValues N vals → ∀ N' : CanonGraph.Node, X = cellValues N' vals →
      ∀ cs ∈ childSlots N', st.known cs.1 := fun hXc N' hN' => absurd hN' (hcoh.not_cell_parsed hN hXc N')
  have henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L) := fun L ctr hL => absurd hL (not_enc_parsed hp L _ ctr)
  by_cases hs : X ∈ st.seen
  · rw [if_neg (not_not.mpr hs)]
    have hXc : X ≠ cellValues N vals := fun heq => hcsk (hrel.seenCells X hs hX N heq cs hcsm)
    exact continue_read_call hrel hlt X hX hnd (hres hXc) (fun h => h.1 hs) (hcell hXc) henc
  · rw [if_pos hs]
    by_cases hXc : X = cellValues N vals
    · have hslot : slotValue X cs.2 = vals cs.1 := by
        rw [hXc]
        exact slot_cellValues N vals cs hcsm
      have hkeep : ¬(⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) := by
        rw [keep_guess_label]
        intro h
        exact h.1 hslot.symm
      rw [if_neg hkeep]
      exact outcome_stop hrel hlt X _ ⟨hs, hX, (hct _).mpr (Or.inl hslot)⟩ rfl
    · have hTX := hres hXc
      by_cases hk : (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hk' := (keep_guess_label (Sum.elim vals nv) (.inl cs.1) (.inl (.inl N)) (slotValue X cs.2) _).mp hk
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX] at hc
          rcases hc with h | h
          · exact hk'.1 h.symm
          · exact hk'.2 h.2.symm
        exact continue_probe hrel hlt X hX _ hk hadm hTX hnd hnc (hcell hXc) henc
      · rw [if_neg hk]
        refine outcome_stop hrel hlt X _ ⟨hs, hX, (hct _).mpr ?_⟩ rfl
        rw [keep_guess_label, not_and_or, not_not, not_not] at hk
        rcases hk with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨hXc, by rw [hTX]; exact h.symm⟩

theorem queryOutcome_congr {X : HashInput}
    {out out' : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U))} (h : out = out')
    (h' : QueryOutcome U T vals nv τ a q mon st ws X out') : QueryOutcome U T vals nv τ a q mon st ws X out := h ▸ h'

theorem lookupVal_map (f : Coord → Digest) (cs : List Coord) (c : Coord) (hc : c ∈ cs) :
    lookupVal (cs.map fun c => (c, f c)) c = f c := by
  induction cs with
  | nil => cases hc
  | cons d rest ih =>
      unfold lookupVal
      simp only [List.map_cons, List.find?_cons]
      by_cases hd : d = c
      · subst hd
        simp
      · simp only [hd, decide_false]
        exact ih ((List.mem_cons.mp hc).resolve_left (Ne.symm hd))

theorem discloseStates_counters (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) :
    (discloseStates U q (Sum.elim vals nv) s cs).counters = s.counters := by
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih => exact (ih _).trans rfl

theorem discloseStates_rows (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) :
    (discloseStates U q (Sum.elim vals nv) s cs).rows = s.rows := by
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih => exact (ih _).trans rfl

theorem discloseStates_candidates (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) (c : WCoord) :
    (discloseStates U q (Sum.elim vals nv) s cs).candidates c =
      if c ∈ cs.map Sum.inl then {Sum.elim vals nv c} else s.candidates c := by
  induction cs generalizing s with
  | nil => simp [discloseStates]
  | cons d rest ih =>
      change (discloseStates U q (Sum.elim vals nv)
        (disclosedState q s (.inl d) (Sum.elim vals nv (.inl d)) .none) rest).candidates c = _
      rw [ih]
      change (if c ∈ rest.map Sum.inl then {Sum.elim vals nv c}
        else Function.update s.candidates (.inl d) {Sum.elim vals nv (.inl d)} c) = _
      by_cases hr : c ∈ rest.map Sum.inl
      · rw [if_pos hr, if_pos (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hr)]
      · rw [if_neg hr]
        by_cases hd : c = .inl d
        · subst hd
          rw [Function.update_self, if_pos (by rw [List.map_cons]; exact List.mem_cons_self)]
        · rw [Function.update_of_ne hd, if_neg (by simp only [List.map_cons, List.mem_cons]; tauto)]

/-- Uncharged disclosures of known coordinates keep the relation. -/
theorem Rel.discloseStates (hrel : Rel U T vals nv τ a q mon st ws) (cs : List Coord) (hk : ∀ c ∈ cs, st.known c) :
    Rel U T vals nv τ a q mon st (discloseStates U q (Sum.elim vals nv) ws cs) := by
  have hc := discloseStates_counters (U := U) (q := q) (vals := vals) (nv := nv) cs ws
  have hr := discloseStates_rows (U := U) (q := q) (vals := vals) (nv := nv) cs ws
  refine ⟨hrel.disclosed, hrel.seen, hrel.calls, by rw [hc]; exact hrel.wcalls, by rw [hc]; exact hrel.digests,
    hrel.contact, by rw [hc]; exact hrel.probes, hrel.budget, ?_, ?_, by rw [hr]; exact hrel.rowsEq,
    by rw [hr]; exact hrel.rowsSeen, hrel.seenCells, hrel.seenEnc⟩
  · intro c
    rw [discloseStates_candidates]
    split_ifs
    · exact Finset.mem_singleton_self _
    · exact hrel.mem c
  · intro c hck
    rw [discloseStates_candidates, hc]
    rw [if_neg (fun hm => hck (by
      obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hm
      have hdc' := Sum.inl.inj hdc
      subst hdc'
      exact hk _ hd))]
    exact hrel.hidden c hck

/-- **Cases C, D**: a parsed input whose children are all known — disclose them; the honest cell is answered by the
node's label, any other input is a label-hit probe. -/
theorem case_knownChildren (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (N : CanonGraph.Node)
    (hN : Extract.posOf X = some N.toPos) (hfu : firstUnknown st.known N = none) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (do
      let pairs ← discloseAll U ((childSlots N).map Prod.fst)
      if X = cellFrom N (lookupVal pairs) then do
        let v ← discloseReq U (.inl (.inl N)) .call
        pure (ChainGraph.joinOutput v (a.high N), st.after X)
      else (fun y => (y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨none, .label (.inl (.inl N))⟩) ws) := by
  have hall := firstUnknown_none hfu
  have hp : Parsed X := ⟨N, hN⟩
  have hnd : ¬IsDigestRow X := fun hd => not_parsed_of_digest hd hp
  have hkN : st.known (.inl N) := Known.node hall
  have hkc : ∀ c ∈ (childSlots N).map Prod.fst, st.known c := by
    intro c hc
    obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
    exact hall cs hcs
  have hrel1 := hrel.discloseStates _ hkc
  rw [observed_discloseAll]
  have hcf : cellFrom N (lookupVal (((childSlots N).map Prod.fst).map fun c => (c, Sum.elim vals nv (.inl c)))) =
      cellValues N vals := by
    rw [cellFrom_eq]
    apply cellValues_congr
    intro cs hcs
    exact lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ cs.1 (List.mem_map.mpr ⟨cs, hcs, rfl⟩)
  rw [hcf]
  have hct : ∀ y : HashOutput, ContactTest T st.known X y ↔ X ≠ cellValues N vals ∧ low y = vals (.inl N) := by
    intro y
    rw [contactTest_parsed hN, hcoh.honestValue, hcoh.honestInput, hfu]
    simp only [reduceCtorEq, false_and, exists_false, false_or]
    rfl
  have henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L) := fun L ctr hL => absurd hL (not_enc_parsed hp L _ ctr)
  by_cases hXc : X = cellValues N vals
  · rw [if_pos hXc, observed_discloseReq, observed_pure]
    have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))) := by
      rintro ⟨-, -, hc⟩
      exact ((hct _).mp hc).1 hXc
    apply outcome_continue hrel hlt X _ hnc
    · rw [RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
      congr 3
      rw [hXc, hcoh.honest_answer]
      rfl
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1 = st.calls + 1
      rw [discloseStates_counters, hrel.wcalls]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.mass = ws.counters.mass + _
      rw [discloseStates_counters, if_neg (fun h => hnd h.2), Nat.add_zero]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤ (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1
      rw [discloseStates_counters]
      have := hrel.probes; omega
    · intro c
      show Sum.elim vals nv c ∈ Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates
        (.inl (.inl N)) {Sum.elim vals nv (.inl (.inl N))} c
      by_cases hc : c = .inl (.inl N)
      · subst hc
        rw [Function.update_self]
        exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hc]
        exact hrel1.mem c
    · intro c hck
      show 2 ^ 128 - (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤
        (Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates (.inl (.inl N))
          {Sum.elim vals nv (.inl (.inl N))} (.inl c)).card
      rw [Function.update_of_ne (fun h => hck (by rw [Sum.inl.inj h]; exact hkN))]
      exact hrel1.hidden c hck
    · intro row v hv
      exact hrel1.rowsEq row v hv
    · intro row v hv
      exact Or.inr (hrel1.rowsSeen row v hv)
    · intro _ N' hN'
      have : N' = N := cell_eq_of_posOf _ _ hN (by rw [hN', hcoh.cell])
      subst this
      exact hall
    · exact fun _ => henc
  · rw [if_neg hXc]
    have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
      hcoh.residual X hX (fun N' => by rw [hcoh.cell]; exact hcoh.not_cell_parsed hN hXc N') (not_prefix_parsed hp)
    have hcell : ∀ N' : CanonGraph.Node, X = cellValues N' vals → ∀ cs ∈ childSlots N', st.known cs.1 :=
      fun N' hN' => absurd hN' (hcoh.not_cell_parsed hN hXc N')
    have hfresh : X ∉ st.seen → (discloseStates U q (Sum.elim vals nv) ws ((childSlots N).map Prod.fst)).rows ⟨X, hX⟩ = none :=
      hrel1.fresh X hX hnd
    have hcomp := observed_testReq (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st)
      (ws := discloseStates U q (Sum.elim vals nv) ws ((childSlots N).map Prod.fst)) aux
      (st.after X) X hX ⟨none, .label (.inl (.inl N))⟩ hfresh
    refine queryOutcome_congr hcomp ?_
    rw [effective_self _ _ (by intro g hg; cases hg)]
    have hadm : ∀ g ∈ (⟨none, .label (.inl (.inl N))⟩ : Probe WCoord).guess, ∀ parent,
        (⟨none, .label (.inl (.inl N))⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
      intro g hg; cases hg
    by_cases hs : X ∈ st.seen
    · rw [if_neg (not_not.mpr hs)]
      have h := continue_read_call hrel1 hlt X hX hnd hTX (fun h => h.1 hs) hcell henc
      exact h
    · rw [if_pos hs]
      by_cases hk : (⟨none, .label (.inl (.inl N))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX] at hc
          exact ((keep_label (Sum.elim vals nv) _ _).mp hk) hc.2.symm
        exact continue_probe hrel1 hlt X hX _ hk hadm hTX hnd hnc hcell henc
      · rw [if_neg hk]
        refine outcome_stop hrel1 hlt X _ ⟨hs, hX, (hct _).mpr ⟨hXc, ?_⟩⟩ rfl
        rw [keep_label, not_not] at hk
        rw [hTX]
        exact hk.symm

/-! ### Encoding rows, digest rows, other rows -/

theorem honestPrefix_iff {L : EncLeaf} {m : Digest} {ctr : BitVec 32} :
    HonestPrefix vals a (Wots.encodingRow L.toWots m ctr) ↔ m = vals (msgCoord L) ∧ PrefixRow a L ctr := by
  constructor
  · rintro ⟨L', ctr', hX, hp⟩
    obtain ⟨rfl, hm, rfl⟩ := encodingRow_encLeaf_injective hX
    exact ⟨hm, hp⟩
  · rintro ⟨rfl, hp⟩
    exact ⟨L, ctr, rfl, hp⟩

theorem Coherent.referenceInput_eq (hcoh : Coherent U T vals nv τ a) {L : EncLeaf} {m : Digest} {ctr : BitVec 32}
    (h : Wots.referenceInput T L.toWots = some (Wots.encodingRow L.toWots m ctr)) :
    m = vals (msgCoord L) ∧ PrefixRow a L ctr := by
  obtain ⟨r, hr, hX⟩ := hcoh.referenceInput L _ h
  obtain ⟨-, hm, hc⟩ := encodingRow_encLeaf_injective hX
  refine ⟨hm, ?_, ?_⟩
  · rw [hc, BitVec.toNat_ofNat]
    have := r.1.isLt
    omega
  · intro r' hr'
    rw [hr] at hr'
    cases hr'
    rw [hc, BitVec.toNat_ofNat]
    have := r.1.isLt
    omega

theorem encRow_not_digest (L : EncLeaf) (m : Digest) (ctr : BitVec 32) :
    ¬IsDigestRow (Wots.encodingRow L.toWots m ctr) := by
  rintro ⟨rho, m', c, h⟩
  exact Wots.SmallA.encodingRow_ne_digest _ _ _ _ _ _ h

/-- **Case E1**: an encoding row of a route leaf whose honest message is known. -/
theorem case_enc_known (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (L : EncLeaf) (m : Digest) (ctr : BitVec 32)
    (hXe : X = Wots.encodingRow L.toWots m ctr) (hkm : st.known (msgCoord L)) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (do
      let msg ← discloseReq U (.inl (msgCoord L)) .none
      if m = msg ∧ PrefixRow a L ctr then do
        tickReq U .call
        pure (prefixValue a L ctr, st.after X)
      else (fun y => (y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨none, .target (refDigest a L)⟩) ws) := by
  have hnp : ¬Parsed X := by rw [hXe]; exact not_parsed_of_encRow ⟨L, m, ctr, rfl⟩
  have hnd : ¬IsDigestRow X := by rw [hXe]; exact encRow_not_digest L m ctr
  have hnext : st.next U X (T (.inl (.inr X))) = st.after X := RouterState.next_of_not U st X _ (fun h => hnd h.2)
  have hrel1 := hrel.discloseStates [msgCoord L] (by intro c hc; rw [List.mem_singleton] at hc; subst hc; exact hkm)
  rw [observed_discloseReq]
  change QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (_)
    (discloseStates U q (Sum.elim vals nv) ws [msgCoord L]))
  simp only [Sum.elim_inl]
  have hct : ∀ y : HashOutput, ContactTest T st.known X y ↔
      Wots.referenceInput T L.toWots ≠ some X ∧ low y = refDigest a L := by
    intro y
    rw [hXe, contactTest_enc, hcoh.honestValue, hcoh.decode_ref, ← hXe]
    simp only [hkm, not_true_eq_false, false_and, false_or]
    rfl
  have hcell : ∀ N' : CanonGraph.Node, X = cellValues N' vals → ∀ cs ∈ childSlots N', st.known cs.1 :=
    fun N' hN' => absurd hN' (not_cell_unparsed hcoh hnp N')
  have henc : ∀ (L' : EncLeaf) (ctr' : BitVec 32), X = Wots.encodingRow L'.toWots (vals (msgCoord L')) ctr' →
      st.known (msgCoord L') := by
    intro L' ctr' hL'
    rw [hXe] at hL'
    obtain ⟨rfl, -, -⟩ := encodingRow_encLeaf_injective hL'
    exact hkm
  by_cases hpre : m = vals (msgCoord L) ∧ PrefixRow a L ctr
  · rw [if_pos hpre, observed_tickReq, observed_pure]
    have hTX : T (.inl (.inr X)) = prefixValue a L ctr := by
      rw [hXe, hpre.1]
      exact hcoh.prefixRow L ctr hpre.2
    have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))) := by
      rintro ⟨-, -, hc⟩
      rw [hct] at hc
      apply hc.1
      rw [hXe, hpre.1]
      apply hcoh.prefix_ref L ctr hpre.2
      rw [← hTX]
      exact (hcoh.decode_ref L _).mpr hc.2
    apply outcome_continue hrel1 hlt X _ hnc (tickState q (discloseStates U q (Sum.elim vals nv) ws [msgCoord L]) .call)
    · rw [hnext, hTX]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1 = st.calls + 1
      rw [discloseStates_counters, hrel.wcalls]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.mass = ws.counters.mass + _
      rw [discloseStates_counters, if_neg (fun h => hnd h.2), Nat.add_zero]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤
        (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1
      rw [discloseStates_counters]
      have := hrel.probes; omega
    · exact hrel1.mem
    · exact hrel1.hidden
    · exact hrel1.rowsEq
    · intro row v hv; exact Or.inr (hrel1.rowsSeen row v hv)
    · exact fun _ => hcell
    · exact fun _ => henc
  · rw [if_neg hpre]
    have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
      hcoh.residual X hX (fun N' => by rw [hcoh.cell]; exact not_cell_unparsed hcoh hnp N')
        (by rw [hXe, honestPrefix_iff]; exact hpre)
    have hri : Wots.referenceInput T L.toWots ≠ some X := by
      rw [hXe]
      intro h
      exact hpre (hcoh.referenceInput_eq h)
    have hfresh := hrel1.fresh X hX hnd
    have hcomp := observed_testReq (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st)
      (ws := discloseStates U q (Sum.elim vals nv) ws [msgCoord L]) aux
      (st.after X) X hX ⟨none, .target (refDigest a L)⟩ hfresh
    refine queryOutcome_congr hcomp ?_
    rw [effective_self _ _ (by intro g hg; cases hg)]
    have hadm : ∀ g ∈ (⟨none, .target (refDigest a L)⟩ : Probe WCoord).guess, ∀ parent,
        (⟨none, .target (refDigest a L)⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
      intro g hg; cases hg
    by_cases hs : X ∈ st.seen
    · rw [if_neg (not_not.mpr hs)]
      exact continue_read_call hrel1 hlt X hX hnd hTX (fun h => h.1 hs) hcell henc
    · rw [if_pos hs]
      by_cases hk : (⟨none, .target (refDigest a L)⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX] at hc
          exact ((keep_target (Sum.elim vals nv) _ _).mp hk) hc.2.symm
        exact continue_probe hrel1 hlt X hX _ hk hadm hTX hnd hnc hcell henc
      · rw [if_neg hk]
        refine outcome_stop hrel1 hlt X _ ⟨hs, hX, (hct _).mpr ⟨hri, ?_⟩⟩ rfl
        rw [keep_target, not_not] at hk
        rw [hTX]
        exact hk.symm

/-- **Case E2**: an encoding row of a route leaf whose honest message is hidden (guess of the message, reference-digest
hit). -/
theorem case_enc_unknown (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (X : HashInput) (hX : X ∈ U) (L : EncLeaf) (m : Digest)
    (ctr : BitVec 32) (hXe : X = Wots.encodingRow L.toWots m ctr) (hkm : ¬st.known (msgCoord L)) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨some (.inl (msgCoord L), m), .target (refDigest a L)⟩) ws) := by
  have hnp : ¬Parsed X := by rw [hXe]; exact not_parsed_of_encRow ⟨L, m, ctr, rfl⟩
  have hnd : ¬IsDigestRow X := by rw [hXe]; exact encRow_not_digest L m ctr
  have hct : ∀ y : HashOutput, ContactTest T st.known X y ↔
      m = vals (msgCoord L) ∨ (Wots.referenceInput T L.toWots ≠ some X ∧ low y = refDigest a L) := by
    intro y
    rw [hXe, contactTest_enc, hcoh.honestValue, hcoh.decode_ref, ← hXe]
    simp only [hkm, not_false_eq_true, true_and]
    rfl
  have hcell : ∀ N' : CanonGraph.Node, X = cellValues N' vals → ∀ cs ∈ childSlots N', st.known cs.1 :=
    fun N' hN' => absurd hN' (not_cell_unparsed hcoh hnp N')
  have hadm : ∀ g ∈ (⟨some (.inl (msgCoord L), m), .target (refDigest a L)⟩ : Probe WCoord).guess, ∀ parent,
      (⟨some (.inl (msgCoord L), m), .target (refDigest a L)⟩ : Probe WCoord).hit = Hit.label parent →
        g.1 ≠ parent := by
    intro g hg parent hpar
    cases hpar
  have heff : (⟨some (.inl (msgCoord L), m), .target (refDigest a L)⟩ : Probe WCoord).effective ws.candidates =
      ⟨some (.inl (msgCoord L), m), .target (refDigest a L)⟩ := by
    apply effective_self
    intro g hg
    refine ⟨?_, hadm g hg⟩
    simp only [Option.mem_def, Option.some.injEq] at hg
    subst hg
    exact hrel.two_le hlt hq _ hkm
  have hcomp := observed_testReq (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st) (ws := ws) aux
    (st.after X) X hX ⟨some (.inl (msgCoord L), m), .target (refDigest a L)⟩ (hrel.fresh X hX hnd)
  refine queryOutcome_congr hcomp ?_
  rw [heff]
  -- a non-honest-message row is a residual row and not the reference row
  have hres : m ≠ vals (msgCoord L) → T (.inl (.inr X)) = τ ⟨X, hX⟩ := fun hm =>
    hcoh.residual X hX (fun N' => by rw [hcoh.cell]; exact not_cell_unparsed hcoh hnp N')
      (by rw [hXe, honestPrefix_iff]; exact fun h => hm h.1)
  have hri : m ≠ vals (msgCoord L) → Wots.referenceInput T L.toWots ≠ some X := fun hm h => by
    rw [hXe] at h
    exact hm (hcoh.referenceInput_eq h).1
  have henc : m ≠ vals (msgCoord L) → ∀ (L' : EncLeaf) (ctr' : BitVec 32),
      X = Wots.encodingRow L'.toWots (vals (msgCoord L')) ctr' → st.known (msgCoord L') := by
    intro hm L' ctr' hL'
    rw [hXe] at hL'
    obtain ⟨rfl, hm', -⟩ := encodingRow_encLeaf_injective hL'
    exact absurd hm' hm
  by_cases hs : X ∈ st.seen
  · rw [if_neg (not_not.mpr hs)]
    have hm : m ≠ vals (msgCoord L) := fun hm =>
      hkm (hrel.seenEnc X hs hX L ctr (by rw [hXe, hm]))
    exact continue_read_call hrel hlt X hX hnd (hres hm) (fun h => h.1 hs) hcell (henc hm)
  · rw [if_pos hs]
    by_cases hm : m = vals (msgCoord L)
    · have hkeep : ¬(⟨some (.inl (msgCoord L), m), .target (refDigest a L)⟩ : Probe WCoord).keep
          (Sum.elim vals nv) (τ ⟨X, hX⟩) := by
        rw [keep_guess_target]
        intro h
        exact h.1 hm.symm
      rw [if_neg hkeep]
      exact outcome_stop hrel hlt X _ ⟨hs, hX, (hct _).mpr (Or.inl hm)⟩ rfl
    · have hTX := hres hm
      by_cases hk : (⟨some (.inl (msgCoord L), m), .target (refDigest a L)⟩ : Probe WCoord).keep
          (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hk' := (keep_guess_target (Sum.elim vals nv) _ _ _ _).mp hk
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX] at hc
          rcases hc with h | h
          · exact hm h
          · exact hk'.2 h.2.symm
        exact continue_probe hrel hlt X hX _ hk hadm hTX hnd hnc hcell (henc hm)
      · rw [if_neg hk]
        refine outcome_stop hrel hlt X _ ⟨hs, hX, (hct _).mpr (Or.inr ⟨hri hm, ?_⟩)⟩ rfl
        rw [keep_guess_target, not_and_or, not_not, not_not] at hk
        rcases hk with h | h
        · exact absurd h.symm hm
        · rw [hTX]
          exact h.symm

/-- **Case F**: a digest row (one unit of mass; a fresh one is a birth). -/
theorem case_digest (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (hd : IsDigestRow X) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, if st.Fresh X then { st.after X with births := (X, y) :: st.births } else st.after X)) <$>
        readReq U ⟨X, hX⟩ .mass) ws) := by
  have hnp := not_parsed_of_digest hd
  have hne : ¬EncRow X := by
    rintro ⟨L, m, ctr, rfl⟩
    exact encRow_not_digest L m ctr hd
  have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
    hcoh.residual X hX (fun N' => by rw [hcoh.cell]; exact not_cell_unparsed hcoh hnp N') (not_prefix_enc hne)
  rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .mass), observed_readReq, observed_pure, map_pure]
  have h := continue_read hrel hlt X hX .mass (Or.inr ⟨rfl, hd⟩) hTX
    (fun h => contactTest_other hnp hne h.2.2)
    (fun N' hN' => absurd hN' (not_cell_unparsed hcoh hnp N'))
    (fun L' ctr' hL' => absurd ⟨L', _, ctr', hL'⟩ hne)
  have heq : (if st.Fresh X then { st.after X with births := (X, τ ⟨X, hX⟩) :: st.births } else st.after X) =
      st.next U X (τ ⟨X, hX⟩) := by
    unfold RouterState.next
    by_cases hf : st.Fresh X
    · rw [if_pos hf, if_pos ⟨hX, hd, hf⟩]
    · rw [if_neg hf, if_neg (fun h' => hf h'.2.2)]
  rw [← heq] at h
  exact h

/-- **Case G**: any other row of `U` (a read; never a contact). -/
theorem case_other (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (hnp : ¬Parsed X) (hne : ¬EncRow X) (hnd : ¬IsDigestRow X) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, st.after X)) <$> readReq U ⟨X, hX⟩ .call) ws) := by
  have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
    hcoh.residual X hX (fun N' => by rw [hcoh.cell]; exact not_cell_unparsed hcoh hnp N') (not_prefix_enc hne)
  rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
  exact continue_read_call hrel hlt X hX hnd hTX (fun h => contactTest_other hnp hne h.2.2)
    (fun N' hN' => absurd hN' (not_cell_unparsed hcoh hnp N'))
    (fun L' ctr' hL' => absurd ⟨L', _, ctr', hL'⟩ hne)

/-- **One routed query** (within the budget): the router's eager observed run stops exactly when the monitor
contacts, otherwise it answers `T X` with the relation preserved. -/
theorem routeQuery_observed (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (X : HashInput) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (observedRun aux q (Sum.elim vals nv) τ (routeQuery U a st X) ws) := by
  unfold routeQuery
  dsimp only
  by_cases hX : X ∈ U
  · rw [dif_pos hX]
    by_cases hp : Parsed X
    · rw [dif_pos hp]
      have hN := Classical.choose_spec hp
      split
      · rename_i cs hfu
        exact case_unknownChild aux hcoh hrel hlt hq X hX _ hN cs hfu
      · rename_i hfu
        exact case_knownChildren aux hcoh hrel hlt X hX _ hN hfu
    · rw [dif_neg hp]
      by_cases he : EncRow X
      · rw [dif_pos he]
        have hXe := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec he))
        by_cases hkm : st.known (msgCoord (Classical.choose he))
        · rw [if_pos hkm]
          exact case_enc_known aux hcoh hrel hlt X hX _ _ _ hXe hkm
        · rw [if_neg hkm]
          exact case_enc_unknown aux hcoh hrel hlt hq X hX _ _ _ hXe hkm
      · rw [dif_neg he]
        by_cases hd : IsDigestRow X
        · rw [if_pos hd]
          exact case_digest aux hcoh hrel hlt X hX hd
        · rw [if_neg hd]
          exact case_other aux hcoh hrel hlt X hX hp he hd
  · rw [dif_neg hX]
    exact case_outside aux hcoh hrel hlt X hX

end Cases

end SigGolfCandidate.T3.Security.LargeCoupling
