import SigGolfCandidate.T3.Secc.WotsEvents

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem mem_entriesOf {answers : Answers} {qs : List Spec.Domain} {input : HashInput}
    (h : (.inl (.inr input) : Spec.Domain) ∈ qs) : (input, answers (.inl (.inr input))) ∈ entriesOf answers qs := by
  unfold entriesOf
  exact List.mem_filterMap.mpr ⟨_, h, rfl⟩
theorem mem_entriesOf_iff {answers : Answers} {qs : List Spec.Domain} {input : HashInput} {answer : HashOutput} :
    (input, answer) ∈ entriesOf answers qs ↔
      (.inl (.inr input) : Spec.Domain) ∈ qs ∧ answers (.inl (.inr input)) = answer := by
  unfold entriesOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, he⟩
    rcases q with (n | input') | c
    · simp at he
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hq, rfl⟩
    · simp at he
  · rintro ⟨hq, rfl⟩
    exact ⟨_, hq, rfl⟩
theorem entriesOf_mono {answers : Answers} {qs qs' : List Spec.Domain} (hsub : ∀ q ∈ qs, q ∈ qs') :
    ∀ e ∈ entriesOf answers qs, e ∈ entriesOf answers qs' := by
  rintro ⟨input, answer⟩ he
  obtain ⟨hq, ha⟩ := mem_entriesOf_iff.mp he
  exact mem_entriesOf_iff.mpr ⟨hsub _ hq, ha⟩
theorem seenRow_of_mem {answers : Answers} {qs : List Spec.Domain} {a : ChainAddr} {step : Nat}
    {value out : Digest} (hq : (.inl (.inr (chainRow a step value)) : Spec.Domain) ∈ qs)
    (hout : low (answers (.inl (.inr (chainRow a step value)))) = out) :
    SeenRow (entriesOf answers qs) a step value out :=
  ⟨_, mem_entriesOf hq, hout⟩
theorem hashPath_join_core (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (Good : Nat → Prop)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash (honestInput step)) = target (step + 1))
    (parse : ∀ step, step < count → ∀ value,
      pad64 (input step value) = pad64 (honestInput step) → value = target step ∧ Good step)
    (reaches : pathValue answers input initial count = target count) :
    (initial = target 0 ∧ ∀ step, step < count →
        Good step ∧ pad64 (pathInput answers input initial step) = pad64 (honestInput step)) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInput answers input initial step))) ∈
          queried answers (hashPath input count initial) ∧
        HashHit answers (pad64 (honestInput step)) (pad64 (pathInput answers input initial step)) ∧
        ∀ later, step < later → later < count →
          Good later ∧ pad64 (pathInput answers input initial later) = pad64 (honestInput later) := by
  induction count with
  | zero => exact Or.inl ⟨reaches, fun step hstep => by omega⟩
  | succ count ih =>
      by_cases heq : pad64 (pathInput answers input initial count) = pad64 (honestInput count)
      · obtain ⟨hprev, hgood⟩ := parse count (by omega) _ heq
        rcases ih (fun step hstep => reference step (by omega))
          (fun step hstep => parse step (by omega)) hprev with ⟨hinit, hall⟩ | ⟨step, hstep, _, hhit, hlater⟩
        · left
          refine ⟨hinit, fun step hstep => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
          · exact hall step hlt
          · exact ⟨hgood, heq⟩
        · refine Or.inr ⟨step, by omega, pathInput_queried answers input initial _ _ (by omega), hhit, ?_⟩
          intro later h1 h2
          rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with hlt | rfl
          · exact hlater later h1 hlt
          · exact ⟨hgood, heq⟩
      · right
        refine ⟨count, by omega, pathInput_queried answers input initial _ _ (by omega), ⟨heq, ?_⟩,
          fun later h1 h2 => by omega⟩
        rw [pathValue_succ] at reaches
        exact reaches.trans (reference count (by omega)).symm
theorem pathValue_succ_of_low (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (initial : Digest) (step : Nat) (next : Digest)
    (href : evalWithAnswerFn answers (shortHash (honestInput step)) = next)
    (hlow : (answers (.inl (.inr (pad64 (pathInput answers input initial step))))).extractLsb' 0 128 =
      (answers (.inl (.inr (pad64 (honestInput step))))).extractLsb' 0 128) :
    pathValue answers input initial (step + 1) = next := by
  rw [pathValue_succ, eval_shortHash, hlow]
  exact href
theorem hashPath_join (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (Good : Nat → Prop)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash (honestInput step)) = target (step + 1))
    (parse : ∀ step, step < count → ∀ value,
      pad64 (input step value) = pad64 (honestInput step) → value = target step ∧ Good step)
    (reaches : pathValue answers input initial count = target count) :
    (initial = target 0 ∧
      (∀ step, step < count → Good step ∧ pad64 (pathInput answers input initial step) = pad64 (honestInput step)) ∧
      ∀ s, s ≤ count → pathValue answers input initial s = target s) ∨
    ∃ step, step < count ∧
      .inl (.inr (pad64 (pathInput answers input initial step))) ∈ queried answers (hashPath input count initial) ∧
      HashHit answers (pad64 (honestInput step)) (pad64 (pathInput answers input initial step)) ∧
      (∀ later, step < later → later < count →
        Good later ∧ pad64 (pathInput answers input initial later) = pad64 (honestInput later)) ∧
      ∀ s, step < s → s ≤ count → pathValue answers input initial s = target s := by
  rcases hashPath_join_core answers input honestInput target Good initial count reference parse reaches with
    ⟨hinit, hall⟩ | ⟨step, hstep, hq, hhit, hlater⟩
  · refine Or.inl ⟨hinit, hall, ?_⟩
    intro s hs
    induction s with
    | zero => exact hinit
    | succ s ih =>
        exact pathValue_succ_of_low answers input honestInput initial s _ (reference s (by omega))
          (by rw [(hall s (by omega)).2])
  · refine Or.inr ⟨step, hstep, hq, hhit, hlater, ?_⟩
    intro s hs hsc
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    rcases Nat.lt_or_ge step k with hk | hk
    · exact pathValue_succ_of_low answers input honestInput initial k _ (reference k (by omega))
        (by rw [(hlater k hk (by omega)).2])
    · have hk' : k = step := by omega
      subst hk'
      exact pathValue_succ_of_low answers input honestInput initial k _ (reference k (by omega)) hhit.2
theorem chainP_join (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value seed : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8)
    (reaches : evalWithAnswerFn answers (chainP lay tree leaf i start count pad0 pad1 headerPad value) =
      honestChainValue answers lay tree leaf i seed (start + count)) :
    (value = honestChainValue answers lay tree leaf i seed start ∧ (0 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∧
      ∀ s, s ≤ count → pathValue answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value s =
        honestChainValue answers lay tree leaf i seed (start + s)) ∨
    ∃ step, step < count ∧
      .inl (.inr (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainP lay tree leaf i start count pad0 pad1 headerPad value) ∧
      HashHit answers
        (pad64 (chainInput lay tree leaf i (start + step)
          (honestChainValue answers lay tree leaf i seed (start + step))))
        (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step)) ∧
      (step + 1 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∧
      (∀ later, step < later → later < count →
        pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value later =
          chainInput lay tree leaf i (start + later)
            (honestChainValue answers lay tree leaf i seed (start + later))) ∧
      ∀ s, step < s → s ≤ count → pathValue answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value s =
        honestChainValue answers lay tree leaf i seed (start + s) := by
  rw [chainP_eq_hashPath] at reaches ⊢
  have h := hashPath_join answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad)
    (fun step => chainInput lay tree leaf i (start + step)
      (honestChainValue answers lay tree leaf i seed (start + step)))
    (fun step => honestChainValue answers lay tree leaf i seed (start + step))
    (fun _ => pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) value count
    (fun step _ => by simpa only [Nat.add_assoc] using
      honestChainValue_succ answers lay tree leaf i seed (start + step))
    (fun step hstep current heq => by
      have hs : start + step < 8 := by rcases hsteps with hz | hb <;> omega
      simp only [chainPathInput, chainInput_eq_zero _ _ _ _ _ _ ht hl hi hs, pad64_chainInputP] at heq
      have hhp := chainInputP_headerPad_eq heq
      obtain ⟨hp0, _, hp1, hv⟩ := chainInputP_fields heq
      exact ⟨hv, hp0, hp1, hhp⟩) reaches
  rcases h with ⟨hvalue, hpads, hvals⟩ | ⟨step, hstep, hq, hhit, hlater, hvals⟩
  · exact Or.inl ⟨by simpa using hvalue, fun hcount => (hpads 0 hcount).1, hvals⟩
  · refine Or.inr ⟨step, hstep, hq, hhit, fun h => (hlater (step + 1) (by omega) h).1, ?_, hvals⟩
    intro later h1 h2
    have he := (hlater later h1 h2).2
    simp only [pathInput, chainPathInput, chainInput_padded, pad64_chainInputP] at he ⊢
    exact he
theorem chainP_frontier (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value seed : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8)
    (reaches : evalWithAnswerFn answers (chainP lay tree leaf i start count pad0 pad1 headerPad value) =
      honestChainValue answers lay tree leaf i seed (start + count))
    (W : Nat) (hW : start < W) (hWc : W ≤ start + count) :
    (∃ step, step < count ∧
      .inl (.inr (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainP lay tree leaf i start count pad0 pad1 headerPad value) ∧
      HashHit answers
        (pad64 (chainInput lay tree leaf i (start + step)
          (honestChainValue answers lay tree leaf i seed (start + step))))
        (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step)) ∧
      (¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ W ≤ start + step)) ∨
    (pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0 ∧
      pathValue answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value (W - start) =
        honestChainValue answers lay tree leaf i seed W) := by
  rcases chainP_join answers lay tree leaf i start count pad0 pad1 headerPad value seed ht hl hi hsteps reaches with
    ⟨_, hpads, hvals⟩ | ⟨step, hstep, hq, hhit, _, _, hvals⟩
  · obtain ⟨h0, h1, hh⟩ := hpads (by omega)
    refine Or.inr ⟨h0, h1, hh, ?_⟩
    rw [hvals (W - start) (by omega), Nat.add_sub_cancel' (le_of_lt hW)]
  · by_cases hp : pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0
    · by_cases hs : W ≤ start + step
      · exact Or.inl ⟨step, hstep, hq, hhit, Or.inr hs⟩
      · refine Or.inr ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
        rw [hvals (W - start) (by omega) (by omega), Nat.add_sub_cancel' (le_of_lt hW)]
    · exact Or.inl ⟨step, hstep, hq, hhit, Or.inl hp⟩
theorem chainP_row (answers : Answers) (a : ChainAddr) (start count : Nat) (value : Digest) (s : Nat)
    (ht : a.key.tree < 2^31) (hl : a.key.leaf < 4096) (hi : a.chain < 64)
    (hsteps : start + count ≤ 8) (hs : s < count) :
    (.inl (.inr (chainRow a (start + s)
        (pathValue answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s))) :
        Spec.Domain) ∈
      queried answers (chainP a.key.lay a.key.tree a.key.leaf a.chain start count 0 0 0 value) ∧
    low (answers (.inl (.inr (chainRow a (start + s)
        (pathValue answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s))))) =
      pathValue answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value (s + 1) := by
  have hrow : pad64 (pathInput answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s) =
      chainRow a (start + s)
        (pathValue answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s) := by
    simp only [pathInput, chainPathInput, pad64_chainInputP, chainRow]
    exact (chainInput_eq_zero a.key.lay a.key.tree a.key.leaf a.chain (start + s) _ ht hl hi (by omega)).symm
  constructor
  · rw [chainP_eq_hashPath, ← hrow]
    exact pathInput_queried answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value count s hs
  · rw [pathValue_succ, eval_shortHash, hrow]
    rfl
theorem chain_seen (answers : Answers) (a : ChainAddr) (start count : Nat) (value out : Digest)
    (qs : List Spec.Domain)
    (ht : a.key.tree < 2^31) (hl : a.key.leaf < 4096) (hi : a.chain < 64)
    (hsteps : start + count ≤ 8)
    (hsub : ∀ q ∈ queried answers (chainP a.key.lay a.key.tree a.key.leaf a.chain start count 0 0 0 value), q ∈ qs)
    (W : Nat) (hW : start < W) (hWc : W ≤ start + count)
    (hval : pathValue answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value (W - start) = out) :
    (∃ x, SeenRow (entriesOf answers qs) a (W - 1) x out) ∧
      (start + 2 ≤ W → ∃ y x, SeenRow (entriesOf answers qs) a (W - 2) y x ∧
        SeenRow (entriesOf answers qs) a (W - 1) x out) := by
  have hlast := chainP_row answers a start count value (W - 1 - start) ht hl hi hsteps (by omega)
  have hstep1 : start + (W - 1 - start) = W - 1 := by omega
  have hsucc1 : W - 1 - start + 1 = W - start := by omega
  rw [hstep1, hsucc1, hval] at hlast
  have hcontact := seenRow_of_mem (hsub _ hlast.1) hlast.2
  refine ⟨⟨_, hcontact⟩, fun h2 => ?_⟩
  have hprev := chainP_row answers a start count value (W - 2 - start) ht hl hi hsteps (by omega)
  have hstep2 : start + (W - 2 - start) = W - 2 := by omega
  have hsucc2 : W - 2 - start + 1 = W - 1 - start := by omega
  rw [hstep2, hsucc2] at hprev
  exact ⟨_, _, seenRow_of_mem (hsub _ hprev.1) hprev.2, hcontact⟩
def SourceLeaf (L : LeafAddr) : Prop := L.tree < 2 ^ 31 ∧ L.leaf < 2 ^ height L.lay
def SourceChain (a : ChainAddr) : Prop := SourceLeaf a.key ∧ a.chain < chainCount a.key.lay
def PosSource : Extract.Pos → Prop
  | .chain lay tree leaf i step => tree < 2 ^ 31 ∧ leaf < 2 ^ height lay ∧ i < chainCount lay ∧ step + 1 < 2 ^ width lay i
  | .leaf lay tree leaf => tree < 2 ^ 31 ∧ leaf < 2 ^ height lay
  | .node lay tree level node => tree < 2 ^ 31 ∧ level < height lay ∧ node < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 31
  | .ftsLeaf index coord leaf => index < 2 ^ 31 ∧ coord < 7 ∧ leaf < 2048
  | .ftsNode index coord level node => index < 2 ^ 31 ∧ coord < 7 ∧ level < 11 ∧ node < 2 ^ (11 - level - 1)
def StructuralHitSrc (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ PosSource position ∧ StructuralClass answers input position ∧
    HashHit answers (Extract.honestInput answers position) input
theorem StructuralHitSrc.toStructuralHit {answers : Answers} {trace : List Entry}
    (h : StructuralHitSrc answers trace) : StructuralHit answers trace := by
  obtain ⟨position, input, answer, hm, hpos, hb, -, hc, hh⟩ := h
  exact ⟨position, input, answer, hm, hpos, hb, hc, hh⟩
theorem structuralHitSrc_mono {answers : Answers} {trace trace' : List Entry} (h : StructuralHitSrc answers trace)
    (hsub : ∀ e ∈ trace, e ∈ trace') : StructuralHitSrc answers trace' := by
  obtain ⟨position, input, answer, hm, hpos, hb, hs, hc, hh⟩ := h
  exact ⟨position, input, answer, hsub _ hm, hpos, hb, hs, hc, hh⟩
theorem otherChainRow_intro {answers : Answers} {input : HashInput} {a : ChainAddr} {step : Nat}
    (hpos : Extract.posOf input = some (.chain a.key.lay a.key.tree a.key.leaf a.chain step))
    (h : (∀ value, input ≠ chainRow a step value) ∨ depth answers a ≤ step) : OtherChainRow answers input :=
  ⟨a, step, hpos, h⟩
theorem structuralHit_intro {answers : Answers} {qs : List Spec.Domain} (pos : Extract.Pos) (actual : HashInput)
    (hb : pos.Bounded) (hsrc : PosSource pos) (hq : (.inl (.inr actual) : Spec.Domain) ∈ qs)
    (hhit : HashHit answers (Extract.honestInput answers pos) actual)
    (hsame : Extract.SameHeader actual (Extract.honestInput answers pos))
    (hclass : StructuralClass answers actual pos) : StructuralHitSrc answers (entriesOf answers qs) :=
  ⟨pos, actual, _, mem_entriesOf hq,
    Extract.posOf_key_eq hb (by rw [hsame, Extract.hdrBlock_honestInput, Extract.Pos.canonicalHeader_eq hb]),
    hb, hsrc, hclass, hhit⟩
theorem height_le' (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide
theorem chainCount_le' (lay : Layer) : chainCount lay ≤ 58 := by fin_cases lay <;> decide
theorem width_le' (lay : Layer) (i : Nat) : width lay i ≤ 3 := by unfold width; split <;> omega
theorem chain_bounded {a : ChainAddr} {step : Nat} (hsrc : SourceChain a)
    (hstep : step + 1 < 2 ^ width a.key.lay a.chain) :
    (Extract.Pos.chain a.key.lay a.key.tree a.key.leaf a.chain step).Bounded := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := hsrc
  have hh : 2 ^ height a.key.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (height_le' _)
  have hw : 2 ^ width a.key.lay a.chain ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (width_le' _ _)
  have hcc := chainCount_le' a.key.lay
  refine ⟨by omega, by omega, by omega, by omega⟩
theorem structuralHit_chain {answers : Answers} {qs : List Spec.Domain} (a : ChainAddr) (step : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (v : Digest)
    (hq : (.inl (.inr (chainInputP a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v)) : Spec.Domain) ∈ qs)
    (hsrc : SourceChain a) (hstep : step + 1 < 2 ^ width a.key.lay a.chain)
    (hhit : HashHit answers (Extract.honestInput answers (.chain a.key.lay a.key.tree a.key.leaf a.chain step))
      (chainInputP a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v))
    (hclass : ¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ depth answers a ≤ step) : StructuralHitSrc answers (entriesOf answers qs) := by
  have hb := chain_bounded hsrc hstep
  have hhdr : Extract.canonicalHeader (Extract.hdrBlock
      (chainInputP a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v)) =
      bytesLE 16 (Extract.Pos.chain a.key.lay a.key.tree a.key.leaf a.chain step).hdr := by
    rw [← pad64_chainInputP, Extract.hdrBlock_chainInputP, Extract.canonicalHeader_chainHeaderP]
    exact Extract.Pos.canonicalHeader_eq
      (p := .chain a.key.lay a.key.tree a.key.leaf a.chain step) hb
  have hpos := Extract.posOf_key_eq (p := .chain a.key.lay a.key.tree a.key.leaf a.chain step) hb hhdr
  refine ⟨_, _, _, mem_entriesOf hq, hpos, hb, ⟨hsrc.1.1, hsrc.1.2, hsrc.2, hstep⟩, ?_, hhit⟩
  refine otherChainRow_intro hpos ?_
  rcases hclass with hpad | hdepth
  · refine Or.inl fun value he => hpad ?_
    rw [chainRow, chainInput_eq_zero _ _ _ _ _ _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2] at he
    have hh := chainInputP_headerPad_eq he
    obtain ⟨h0, _, h1, _⟩ := chainInputP_fields he
    exact ⟨h0, h1, hh⟩
  · exact Or.inr hdepth
theorem chain_cases (answers : Answers) (a : ChainAddr) (start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value : Digest)
    (qs : List Spec.Domain)
    (hsub : ∀ q ∈ queried answers (chainP a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value),
      q ∈ qs)
    (hsrc : SourceChain a) (hcount : start + count < 2 ^ width a.key.lay a.chain)
    (hdepth : depth answers a ≤ start + count)
    (reaches : evalWithAnswerFn answers (chainP a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value) =
      honestChainValue answers a.key.lay a.key.tree a.key.leaf a.chain
        (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + count)) :
    StructuralHitSrc answers (entriesOf answers qs) ∨
      ((depth answers a ≤ start →
          value = honestChainValue answers a.key.lay a.key.tree a.key.leaf a.chain
            (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) start ∧
          (0 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0)) ∧
        (start < depth answers a →
          ContactAt answers (entriesOf answers qs) a ∧
            (start + 2 ≤ depth answers a → TwoEdgeAt answers (entriesOf answers qs) a))) := by
  classical
  by_cases hS : StructuralHitSrc answers (entriesOf answers qs)
  · exact Or.inl hS
  right
  have ht := hsrc.1.1
  have hh : 2 ^ height a.key.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (height_le' a.key.lay)
  have hl : a.key.leaf < 4096 := lt_of_lt_of_le hsrc.1.2 hh
  have hi : a.chain < 64 := lt_of_lt_of_le hsrc.2 (by have := chainCount_le' a.key.lay; omega)
  have hc8 : start + count ≤ 8 := by
    have hw : 2 ^ width a.key.lay a.chain ≤ 2 ^ 3 :=
      Nat.pow_le_pow_right (by decide) (width_le' a.key.lay a.chain)
    omega
  have hit : ∀ step, step < count →
      .inl (.inr (pad64 (pathInput answers
        (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainP a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value) →
      HashHit answers
        (pad64 (chainInput a.key.lay a.key.tree a.key.leaf a.chain (start + step)
          (honestChainValue answers a.key.lay a.key.tree a.key.leaf a.chain
            (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + step))))
        (pad64 (pathInput answers
          (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start pad0 pad1 headerPad) value step)) →
      (¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ depth answers a ≤ start + step) → False := by
    intro step hstep hq hhit hclass
    apply hS
    simp only [pathInput, chainPathInput, pad64_chainInputP] at hq hhit
    exact structuralHit_chain a (start + step) pad0 pad1 headerPad _ (hsub _ hq) hsrc (by omega) hhit hclass
  constructor
  · intro hle
    rcases chainP_extract answers a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value
        (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) ht hl hi (Or.inr hc8) reaches with
      ⟨hval, hpads⟩ | ⟨step, hstep, hq, hhit⟩
    · exact ⟨hval, hpads⟩
    · exact (hit step hstep hq hhit (Or.inr (by omega))).elim
  · intro hlt
    rcases chainP_frontier answers a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value
        (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) ht hl hi (Or.inr hc8) reaches (depth answers a) hlt hdepth with
      ⟨step, hstep, hq, hhit, hclass⟩ | ⟨h0, h1, hh, hval⟩
    · exact (hit step hstep hq hhit hclass).elim
    · subst h0 h1 hh
      obtain ⟨⟨x, hx⟩, htwo⟩ := chain_seen answers a start count value _ qs ht hl hi hc8 hsub (depth answers a) hlt hdepth hval
      exact ⟨⟨by omega, x, hx⟩, fun h2 => ⟨by omega, htwo h2⟩⟩
end SigGolfCandidate.T3.Security.WotsExtract
