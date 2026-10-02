import SigGolfCandidate.T3.Secc.LargeCouplingBankSearch

/-!
# LR-34 (bank, one signing): a signing request is a supermartingale step of the bank

**`bank_routeSign`**: for a lazy world state and a router state in the bank invariant, the routed signing's expected
continuation value is at most `psi q st + slackT q ws` whenever every continuation `(sig, st', ws')` in the invariant
(same calls) pays at most `psi q st' + slackT q ws'`.

* unpublished cache: nothing happens;
* repeated message: the memoized search result, disclosures only (the bank unchanged);
* fresh message: the nonce is a fresh uniform disclosure (`BankInv.nonce`), the lazy search is SEC's `roRun` search
  from the ghost cache (`bank_search`; the trial rows of an unsigned message agree with the births), and the ghost
  update is CC's `core_sign` step (`psi_signed`: the reuse flag on `Reuse`, else the selection exposed; the message's
  reuse mass removed, `reuseC_signed`).
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingBankSign : DecidableEq T3.Cache := Classical.decEq _

section Sign
variable {U : Finset HashInput}

/-! ## The bank state after a fresh signing -/

theorem reuseC_signed_eq (st : RouterState) (rho rho' : Digest) (m : Message)
    (found found' : Option (BitVec 32 × LargeResidual.HashOutput)) :
    reuseC (st.signed rho m found) = reuseC (st.signed rho' m found') := by
  obtain ⟨-, -, -, hb, -, hmemo⟩ := RouterState.signed_fields st rho m found
  obtain ⟨-, -, -, hb', -, hmemo'⟩ := RouterState.signed_fields st rho' m found'
  unfold reuseC
  have hc : (st.signed rho m found).cache = (st.signed rho' m found').cache := by
    funext X; simp only [RouterState.cache, hb, hb']
  rw [hc, hmemo, hmemo']
  apply tsum_congr
  intro m'
  by_cases h : m' = m
  · subst h; simp
  · have hb2 : (m' == m) = false := by simpa using h
    simp only [List.lookup_cons, hb2]

/-- **The potential after a fresh signing** (CC's `core_sign` integrand). -/
theorem psi_signed (q : Nat) (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × LargeResidual.HashOutput)) :
    psi q (st.signed rho m found) =
      if CaseC.Reuse st.cache rho m then
        CaseC.corePotential { bankOf q st with reused := true, reuse := reuseC (st.signed 0 m none) }
      else CaseC.corePotential ((bankOf q st).expose (reuseC (st.signed 0 m none)) (found.map Prod.snd)) := by
  rw [← reuseC_signed_eq st rho 0 m found none]
  unfold psi
  by_cases hr : CaseC.Reuse st.cache rho m
  · rw [if_pos hr]
    congr 1
    unfold bankOf RouterState.signed
    rw [if_pos hr]
  · rw [if_neg hr]
    congr 1
    unfold bankOf CaseC.BankCore.expose RouterState.signed
    rw [if_neg hr]
    rfl

/-! ## The invariant through a signing -/

theorem BankInv.disc {ws ws' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (hd : DiscFrame U ws ws') (d : List Coord) : BankInv U ws' { st with disclosed := d } := by
  obtain ⟨hr, hc, hn⟩ := hd
  refine ⟨by rw [hc]; exact h.calls, by rw [hc]; exact h.mass, h.births, fun m hm => by rw [hn m]; exact h.nonce m hm,
    fun X hX hd hs ht => by rw [hr]; exact h.fresh X hX hd hs ht,
    fun X hX hd hs ht => by rw [hr]; exact h.seenRows X hX hd hs ht, h.bornSeen, h.trials⟩

theorem BankInv.discloseSigned {ws : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (q : Nat) (m : Message) (hm : (st.memo.lookup m).isSome) (rho : Digest) :
    BankInv U (disclosedState q ws (.inr m) rho .none) st := by
  refine ⟨h.calls, h.mass, h.births, fun m' hm' => ?_, h.fresh, h.seenRows, h.bornSeen, h.trials⟩
  have hne : m' ≠ m := by
    intro he; subst he; rw [hm'] at hm; cases hm
  simp only [disclosedState, discloseTableValue]
  rw [Function.update_of_ne (by simpa using hne)]
  exact h.nonce m' hm'

theorem mem_trialRows (rho : Digest) (m : Message) (found : Option (BitVec 32 × LargeResidual.HashOutput)) (k : Nat)
    (hk : k < attemptLimit) (hf : ∀ k' out, found = some (k', out) → k ≤ k'.toNat) :
    pad64 (digestInput rho m (BitVec.ofNat 32 k)) ∈ trialRows rho m found := by
  unfold trialRows
  apply List.mem_map.mpr
  refine ⟨k, List.mem_range.mpr ?_, rfl⟩
  cases found with
  | none => exact hk
  | some f =>
      obtain ⟨k', out⟩ := f
      have := hf k' out rfl
      dsimp only
      omega

theorem BankInv.signed {ws s' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (q : Nat) (m : Message) (hm : st.memo.lookup m = none) (rho : Digest)
    (found : Option (BitVec 32 × LargeResidual.HashOutput))
    (hf : SearchFrame rho m 0 attemptLimit found (disclosedState q ws (.inr m) rho .none) s') :
    BankInv U s' (st.signed rho m found) := by
  obtain ⟨hdisc, hseen, hcalls, hbirths, htrials, hmemo⟩ := RouterState.signed_fields st rho m found
  obtain ⟨hcand, hcount, -, hrows⟩ := hf
  have hcache : (st.signed rho m found).cache = st.cache := by
    funext X; simp only [RouterState.cache, hbirths]
  -- rows off the new trial rows are unchanged
  have hkeep : ∀ (X : HashInput) (hX : X ∈ U), X ∉ trialRows rho m found → s'.rows ⟨X, hX⟩ = ws.rows ⟨X, hX⟩ := by
    intro X hX hnt
    by_contra hne
    obtain ⟨k, -, hk2, hk3, hk4⟩ := hrows ⟨X, hX⟩ hne
    exact hnt (by rw [show X = _ from hk3]; exact mem_trialRows rho m found k (by simpa using hk2) hk4)
  refine ⟨?_, ?_, ?_, fun m' hm' => ?_, fun X hX hd hs ht => ?_, fun X hX hd hs ht => ?_, ?_, ?_⟩
  · rw [hcount, hcalls]; exact h.calls
  · rw [hcount]; exact h.mass
  · rw [hbirths, hcalls]; exact h.births
  · have hne : m' ≠ m := by
      intro he; subst he
      rw [hmemo] at hm'
      simp at hm'
    have hm'' : st.memo.lookup m' = none := by
      rw [hmemo] at hm'
      have hb : (m' == m) = false := by simpa using hne
      simpa only [List.lookup_cons, hb] using hm'
    rw [hcand]
    simp only [disclosedState, discloseTableValue]
    rw [Function.update_of_ne (by simpa using hne)]
    exact h.nonce m' hm''
  · rw [htrials] at ht
    rw [hseen] at hs
    rw [hkeep X hX (fun hm2 => ht (List.mem_append_right _ hm2))]
    exact h.fresh X hX hd hs (fun hm2 => ht (List.mem_append_left _ hm2))
  · rw [htrials] at ht
    rw [hseen] at hs
    rw [hkeep X hX (fun hm2 => ht (List.mem_append_right _ hm2)), hcache]
    exact h.seenRows X hX hd hs (fun hm2 => ht (List.mem_append_left _ hm2))
  · intro p hp
    rw [hbirths] at hp
    rw [hseen]
    exact h.bornSeen p hp
  · intro X hX
    rw [htrials] at hX
    rcases List.mem_append.mp hX with hX | hX
    · obtain ⟨rho', m', c', hX', hs'⟩ := h.trials X hX
      refine ⟨rho', m', c', hX', ?_⟩
      rw [hmemo, List.lookup_cons]
      split
      · rfl
      · exact hs'
    · unfold trialRows at hX
      obtain ⟨k, -, hk⟩ := List.mem_map.mp hX
      refine ⟨rho, m, BitVec.ofNat 32 k, hk.symm, ?_⟩
      rw [hmemo, List.lookup_cons]
      simp

/-- The trial rows of an unsigned message agree with the ghost cache. -/
theorem BankInv.agree {ws : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (hUpub : SeccLaw.publicUniverse ⊆ U) (m : Message) (hm : st.memo.lookup m = none) (rho : Digest) (k : Nat) :
    ws.rows ⟨_, digestRow_mem hUpub rho m (BitVec.ofNat 32 k)⟩ =
      st.cache (pad64 (digestInput rho m (BitVec.ofNat 32 k))) := by
  have hd : IsDigestRow (pad64 (digestInput rho m (BitVec.ofNat 32 k))) := digestRow_isDigest _ _ _
  have ht : pad64 (digestInput rho m (BitVec.ofNat 32 k)) ∉ st.trials := by
    intro hX
    obtain ⟨rho', m', c', hX', hs'⟩ := h.trials _ hX
    obtain ⟨-, -, hmm⟩ := BPB.digestInput_injective hX'
    subst hmm
    rw [hm] at hs'
    cases hs'
  by_cases hs : pad64 (digestInput rho m (BitVec.ofNat 32 k)) ∈ st.seen
  · obtain ⟨y, h1, h2⟩ := h.seenRows _ _ hd hs ht
    rw [h1, h2]
  · rw [h.fresh _ _ hd hs ht, h.cache_none hs]

/-! ## The signing step -/

variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)

theorem ev_signFinish_le (a : AuxData) (st : RouterState) (rho : Digest)
    (found : Option (BitVec 32 × LargeResidual.HashOutput)) (s : LargeResidual.State WCoord (Cell U))
    (g : Option (Option Signature × RouterState) × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal)
    (h : ∀ sig (d : List Coord) s', DiscFrame U s s' → g (some (sig, { st with disclosed := d }), s') ≤ B) :
    expectedValue (lazyRun aux q (signFinish U a st rho found) s) g ≤ B := by
  unfold signFinish
  rcases found with _ | ⟨c, N⟩
  · rw [lazy_pure, expectedValue_pure]
    exact h none st.disclosed s (DiscFrame.refl U s)
  · dsimp only
    split
    · apply ev_discloseAll_le
      intro pairs s' hd
      rw [lazy_pure, expectedValue_pure]
      exact h _ _ s' hd
    · rw [lazy_pure, expectedValue_pure]
      exact h none st.disclosed s (DiscFrame.refl U s)

theorem expectedValue_cell_univ (f : LargeResidual.Digest → ENNReal) :
    expectedValue (cell (Finset.univ : Finset LargeResidual.Digest)) f =
      expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho => f rho) := by
  simp only [expectedValue_def]
  apply tsum_congr
  intro rho
  have h1 : Pr[= rho | ($ᵗ Digest : ProbComp Digest)] = (Fintype.card LargeResidual.Digest : ENNReal)⁻¹ :=
    probOutput_uniformSample _ rho
  have h2 : Pr[= rho | cell (Finset.univ : Finset LargeResidual.Digest)] =
      (Fintype.card LargeResidual.Digest : ENNReal)⁻¹ := by
    rw [cell, dif_pos Finset.univ_nonempty, SPMF.probOutput_eq_apply, SPMF.liftM_apply,
      PMF.uniformOfFinset_apply, if_pos (Finset.mem_univ _), Finset.card_univ]
  rw [h1, h2]

/-- **One routed signing is a supermartingale step of the bank** (CC's `core_sign`). -/
theorem bank_routeSign (hUpub : SeccLaw.publicUniverse ⊆ U) (a : AuxData) (published : T3.Cache) (st : RouterState)
    (ws : LargeResidual.State WCoord (Cell U)) (request : Security.Request) (hinv : BankInv U ws st)
    (g : Option (Option Signature × RouterState) × LargeResidual.State WCoord (Cell U) → ENNReal)
    (hcont : ∀ sig st' ws', BankInv U ws' st' → st'.calls = st.calls → g (some (sig, st'), ws') ≤ psi q st' + slackT q ws') :
    expectedValue (lazyRun aux q (routeSign U a published st request) ws) g ≤ psi q st + slackT q ws := by
  unfold routeSign
  split_ifs with hpub
  swap
  · rw [lazy_pure, expectedValue_pure]
    exact hcont none st ws hinv rfl
  rw [lazy_discloseReq]
  cases hm : st.memo.lookup request.message with
  | some found =>
      apply ev_bind_le
      intro rho
      apply ev_signFinish_le aux q a st rho found _ g
      intro sig d s' hd
      have hinv1 := hinv.discloseSigned q request.message (by rw [hm]; rfl) rho
      refine (hcont sig _ s' (hinv1.disc hd d) rfl).trans (le_of_eq ?_)
      rw [slackT_eq_of_mass q (show s'.counters.mass = ws.counters.mass by rw [hd.2.1] <;> rfl)]
      rfl
  | none =>
      set m := request.message with hmdef
      rw [hinv.nonce m hm, expectedValue_bind, expectedValue_cell_univ]
      set C0 := reuseC (st.signed 0 m none) with hC0
      have hC : C0 + CaseC.reuseMass st.cache m ≤ (bankOf q st).reuse := by
        rw [hC0, reuseC_signed st 0 m none hm]; exact le_rfl
      have hcore := CaseC.core_sign (bankOf q st) st.cache m C0 hC 0 attemptLimit (by decide)
      -- per nonce: the lazy search and finish are dominated by CC's integrand plus the slack
      have hrho : ∀ rho : Digest,
          expectedValue (lazyRun aux q (simulateQ (readImpl U a) (digestSearch rho m 0 attemptLimit) >>= fun found =>
              signFinish U a (st.signed rho m found) rho found) (disclosedState q ws (.inr m) rho .none)) g ≤
            (if CaseC.Reuse st.cache rho m then CaseC.corePotential { bankOf q st with reused := true, reuse := C0 }
              else expectedValue (Sampling.roRun 0 (digestSearch rho m 0 attemptLimit) st.cache)
                (fun result => CaseC.corePotential ((bankOf q st).expose C0 (result.1.map Prod.snd)))) +
              slackT q ws := by
        intro rho
        rw [lazyRun, ev_runWith_bind, ← lazyRun]
        have hsearch := bank_search aux q a rho m (digestRow_mem hUpub rho m) 0 attemptLimit 0 (by decide)
          (disclosedState q ws (.inr m) rho .none) st.cache
          (fun k _ _ => hinv.agree hUpub m hm rho k)
          (fun r => r.1.elim (g (none, r.2)) (fun found =>
            expectedValue (lazyRun aux q (signFinish U a (st.signed rho m found) rho found) r.2) g))
          (fun found => psi q (st.signed rho m found) + slackT q ws)
          (by
            intro found s' hf
            apply ev_signFinish_le aux q a _ rho found s' g
            intro sig d s'' hd
            have hinv' := (hinv.signed q m hm rho found hf).disc hd d
            refine (hcont sig _ s'' hinv' ?_).trans (le_of_eq ?_)
            · exact (RouterState.signed_fields st rho m found).2.2.1
            · have hmass : s''.counters.mass = ws.counters.mass := by
                rw [hd.2.1, hf.2.1] <;> rfl
              rw [slackT_eq_of_mass q hmass]
              rfl)
        refine hsearch.trans ?_
        rw [expectedValue_add]
        refine add_le_add ?_ (expectedValue_le_of_le _ fun _ => le_rfl)
        by_cases hr : CaseC.Reuse st.cache rho m
        · rw [if_pos hr]
          apply expectedValue_le_of_le
          intro result
          rw [psi_signed, if_pos hr]
        · rw [if_neg hr]
          apply le_of_eq
          congr 1
          funext result
          rw [psi_signed, if_neg hr]
      calc
        _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
            (if CaseC.Reuse st.cache rho m then CaseC.corePotential { bankOf q st with reused := true, reuse := C0 }
              else expectedValue (Sampling.roRun 0 (digestSearch rho m 0 attemptLimit) st.cache)
                (fun result => CaseC.corePotential ((bankOf q st).expose C0 (result.1.map Prod.snd)))) +
              slackT q ws) := expectedValue_mono _ hrho
        _ ≤ CaseC.corePotential (bankOf q st) + slackT q ws := by
          rw [expectedValue_add]
          exact add_le_add hcore (expectedValue_le_of_le _ fun _ => le_rfl)
        _ = _ := rfl

end Sign

end SigGolfCandidate.T3.Security.LargeCoupling
