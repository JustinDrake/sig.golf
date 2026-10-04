import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingCertDefs
import SigGolfCandidate.T3.Secc.LargeCouplingBankLazy
import SigGolfCandidate.ClaudeWCT.Bank.WCTRev3
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufRoute
import SigGolfCandidate.ClaudeWCT.Numerics.WCTPrice
import SigGolfCandidate.T3.Secc.LargeCouplingBankState
import SigGolfCandidate.T3.Secc.LargeCouplingBankStep
import SigGolfCandidate.T3.Secc.LargeCouplingBankSearch
import SigGolfCandidate.T3.Secc.LargeCouplingBankSign

section


namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell Charge Probe lazyRun readState probeState stoppedState
  disclosedState tickState lazyResponse)
open SigGolfCandidate.T3.Security.LargeCoupling (lazy_read lazy_pure lazy_probe_cached lazy_probe_fresh lazy_aux'
  lazy_disclose lazy_tick ev_bind_le)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Router
variable (U : Finset HashInput) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem lazy_coinReq {β : Type} (n : Nat) (k : Fin (n + 1) → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    lazyRun aux q (coinReq U n >>= k) s = ((liftM (aux (.coin n)) : SPMF _) >>= fun v => lazyRun aux q (k v) s) :=
  lazy_aux' aux q (.coin n) k s
theorem lazy_initReq {β : Type} (k : AuxData → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    lazyRun aux q (initReq U >>= k) s = ((liftM (aux .init) : SPMF _) >>= fun v => lazyRun aux q (k v) s) :=
  lazy_aux' aux q .init k s
theorem lazy_readReq {β : Type} (row : Cell U) (ch : Charge) (k : HashOutput → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    lazyRun aux q (readReq U row ch >>= k) s =
      (reply s.rows row >>= fun y => lazyRun aux q (k y) (readState q s row y ch)) :=
  lazy_read aux q row ch k s
theorem lazy_probeReq_cached {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (v : HashOutput)
    (h : s.rows row = some v) :
    lazyRun aux q (probeReq U row test >>= k) s = lazyRun aux q (k v) (readState q s row v .call) :=
  lazy_probe_cached aux q row test k s v h
theorem lazy_probeReq_fresh {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (h : s.rows row = none) :
    lazyRun aux q (probeReq U row test >>= k) s =
      observe (lazyResponse s.candidates (test.effective s.candidates)) (pure (none, stoppedState s))
        (fun y => lazyRun aux q (k y) (probeState s row (test.effective s.candidates) y)) :=
  lazy_probe_fresh aux q row test k s h
theorem lazy_discloseReq {β : Type} (c : WCoord) (ch : Charge) (k : Digest → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    lazyRun aux q (discloseReq U c ch >>= k) s =
      (cell (s.candidates c) >>= fun v => lazyRun aux q (k v) (disclosedState q s c v ch)) :=
  lazy_disclose aux q c ch k s
theorem lazy_tickReq {β : Type} (ch : Charge) (k : Unit → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    lazyRun aux q (tickReq U ch >>= k) s = lazyRun aux q (k ()) (tickState q s ch) :=
  lazy_tick aux q ch k s
def DiscFrame (s s' : State WCoord (Cell U)) : Prop :=
  s'.rows = s.rows ∧ s'.counters = s.counters ∧ ∀ m : Message, s'.candidates (.inr m) = s.candidates (.inr m)
theorem DiscFrame.refl (s : State WCoord (Cell U)) : DiscFrame U s s := ⟨rfl, rfl, fun _ => rfl⟩
theorem DiscFrame.trans {s1 s2 s3 : State WCoord (Cell U)} (h1 : DiscFrame U s1 s2) (h2 : DiscFrame U s2 s3) :
    DiscFrame U s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun m => (h2.2.2 m).trans (h1.2.2 m)⟩
theorem discFrame_disclose (s : State WCoord (Cell U)) (c : Coord) (v : Digest) :
    DiscFrame U s (disclosedState q s (.inl c) v .none) := by
  refine ⟨rfl, rfl, fun m => ?_⟩
  simp only [disclosedState, discloseTableValue]
  rw [Function.update_of_ne (by simp)]
theorem ev_discloseAll_le {β : Type} (cs : List Coord) (k : List (Coord × Digest) → OracleComp (RWorld U) β)
    (pay : Option β × State WCoord (Cell U) → ENNReal) (B : ENNReal) (s : State WCoord (Cell U))
    (h : ∀ pairs s', DiscFrame U s s' → expectedValue (lazyRun aux q (k pairs) s') pay ≤ B) :
    expectedValue (lazyRun aux q (discloseAll U cs >>= k) s) pay ≤ B := by
  induction cs generalizing s k with
  | nil =>
      simp only [discloseAll, pure_bind]
      exact h [] s (DiscFrame.refl U s)
  | cons c rest ih =>
      simp only [discloseAll, bind_assoc]
      rw [lazy_discloseReq]
      apply ev_bind_le
      intro v
      simp only [pure_bind]
      exact ih _ _ fun pairs s' hs' => h _ s' ((discFrame_disclose U q s c v).trans U hs')
end Router
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section

namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open CaseC (BankCore BankCore.expose theta)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate)
theorem wct_corePotential_rate (rate' : ENNReal) (hexc' : ExcessBound horizon rate') :
    (wctSpecL horizon rate hexc).corePotential = (wctSpecL horizon rate' hexc').corePotential := rfl
theorem wct_core_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + (wctSpecL horizon rate hexc).admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => (wctSpecL horizon rate hexc).corePotential
          { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      (wctSpecL horizon rate hexc).corePotential b + (theta + 1 / 64) / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).core_birth b s hs C' hC
theorem wct_core_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + (wctSpecL horizon rate hexc).reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if (wctSpecL horizon rate hexc).Reuse cache rho m then
        (wctSpecL horizon rate hexc).corePotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (WCT9.digestSearch rho m 0 fuel) cache)
        (fun result => (wctSpecL horizon rate hexc).corePotential (b.expose C' (result.1.map Prod.snd)))) ≤
      (wctSpecL horizon rate hexc).corePotential b := by
  have h := (wctSpecL horizon rate hexc).core_sign b cache m C' hC secret fuel hfuel
  simp only [← wct_digestSearch_public (wctSpecL horizon rate hexc).toFtsBankSpec rfl] at h
  exact h
theorem wct_core_win (b : BankCore) (halive : ¬horizon < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, WCT9.admissible N = true ∧ Covered b.exposures N) :
    1 ≤ (wctSpecL horizon rate hexc).corePotential b :=
  (wctSpecL horizon rate hexc).core_win b halive h
theorem wct_core_initial (budget : Nat) :
    (wctSpecL horizon rate hexc).corePotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).core_initial budget
end ClaudeWCT.Bank.WCT
end

section





namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (digestTrial_inj tsum_trial_indicator_le expectedValue_uniform_reply)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable def reuseC (st : RouterState) : ENNReal :=
  ∑' m : Message, if (st.memo.lookup m).isSome then 0 else CaseC.bankSpec.reuseMass st.cache m
noncomputable def bankOf (q : Nat) (st : RouterState) : CaseC.BankCore :=
  ⟨(st.births.map Prod.snd).reverse, st.exposures, st.reused, reuseC st, q - st.births.length⟩
noncomputable def psi (q : Nat) (st : RouterState) : ENNReal := CaseC.bankSpec.corePotential (bankOf q st)
noncomputable def slackT {U : Finset HashInput} (q : Nat) (ws : LargeResidual.State WCoord (Cell U)) : ENNReal :=
  ((q - ws.counters.mass : Nat) : ENNReal) / 2 ^ 128
structure BankInv (U : Finset HashInput) (ws : LargeResidual.State WCoord (Cell U)) (st : RouterState) : Prop where
  calls : ws.counters.calls = st.calls
  mass : ws.counters.mass ≤ ws.counters.calls
  births : st.births.length ≤ st.calls
  nonce : ∀ m, st.memo.lookup m = none → ws.candidates (.inr m) = Finset.univ
  fresh : ∀ (X : HashInput) (hX : X ∈ U), IsDigestRow X → X ∉ st.seen → X ∉ st.trials → ws.rows ⟨X, hX⟩ = none
  seenRows : ∀ (X : HashInput) (hX : X ∈ U), IsDigestRow X → X ∈ st.seen → X ∉ st.trials →
    ∃ y, st.cache X = some y ∧ ws.rows ⟨X, hX⟩ = some y
  bornSeen : ∀ p ∈ st.births, p.1 ∈ st.seen
  trials : ∀ X ∈ st.trials, ∃ rho m c, X = pad64 (digestInput rho m c) ∧ (st.memo.lookup m).isSome
def _root_.ClaudeWCT.W9.T3.Security.LargeResidual.RouterState.born (st : RouterState) (X : HashInput)
    (y : LargeResidual.HashOutput) : RouterState :=
  { st.after X with births := (X, y) :: st.births }
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.RouterState.next_eq (U : Finset HashInput) (st : RouterState)
    (X : HashInput) (y : LargeResidual.HashOutput) :
    st.next U X y = if X ∈ U ∧ IsDigestRow X ∧ st.Fresh X then st.born X y else st.after X := rfl
theorem bankOf_after (q : Nat) (st : RouterState) (X : HashInput) : bankOf q (st.after X) = bankOf q st := rfl
theorem psi_after (q : Nat) (st : RouterState) (X : HashInput) : psi q (st.after X) = psi q st := rfl
theorem cache_birth (st : RouterState) (X Z : HashInput) (y : LargeResidual.HashOutput) :
    (st.born X y).cache Z =
      if Z = X then some y else st.cache Z := by
  simp only [RouterState.born, RouterState.cache, List.lookup_cons]
  by_cases h : Z = X
  · subst h; simp
  · have hb : (Z == X) = false := by simpa using h
    rw [hb, if_neg h]
theorem admissibleEntry_birth (st : RouterState) (X Z : HashInput) (y : LargeResidual.HashOutput)
    (hX : st.cache X = none) :
    CaseC.bankSpec.admissibleEntry (st.born X y).cache Z ≤
      CaseC.bankSpec.admissibleEntry st.cache Z + if Z = X then CaseC.bankSpec.admInd y else 0 := by
  unfold ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
  simp only [cache_birth]
  by_cases h : Z = X
  · subst h
    simp only [if_true, hX, Option.elim_none, Option.elim_some, zero_add, ClaudeWCT.Bank.FtsBankSpec.admInd]
    exact le_rfl
  · simp only [h, if_false, add_zero]
    exact le_rfl
theorem reuseC_birth (st : RouterState) (X : HashInput) (y : LargeResidual.HashOutput) (hX : st.cache X = none) :
    reuseC (st.born X y) ≤ reuseC st + CaseC.bankSpec.admInd y / 2 ^ 128 := by
  unfold reuseC ClaudeWCT.Bank.FtsBankSpec.reuseMass
  have hmemo : (st.born X y).memo = st.memo := rfl
  rw [hmemo]
  calc
    _ ≤ ∑' m : Message, ((if (st.memo.lookup m).isSome then 0 else
          (∑' p : Digest × Fin (2 ^ 32),
            CaseC.bankSpec.admissibleEntry st.cache (Sampling.digestTrial p.1 m p.2.val)) / 2 ^ 128) +
          (∑' p : Digest × Fin (2 ^ 32),
            if Sampling.digestTrial p.1 m p.2.val = X then CaseC.bankSpec.admInd y else 0) / 2 ^ 128) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs
      · exact zero_le
      · rw [← ENNReal.add_div, ← ENNReal.tsum_add]
        apply ENNReal.div_le_div_right
        apply ENNReal.tsum_le_tsum
        intro p
        exact admissibleEntry_birth st X _ y hX
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := by
      apply add_le_add le_rfl
      simp only [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_mul' (tsum_trial_indicator_le X _) le_rfl
theorem reuseC_signed (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × LargeResidual.HashOutput))
    (hm : st.memo.lookup m = none) :
    reuseC (st.signed rho m found) + CaseC.bankSpec.reuseMass st.cache m = reuseC st := by
  obtain ⟨-, -, -, hb, -, hmemo⟩ := RouterState.signed_fields st rho m found
  have hcache : (st.signed rho m found).cache = st.cache := by
    funext X; simp only [RouterState.cache, hb]
  unfold reuseC
  rw [hmemo, hcache, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' => if (st.memo.lookup m').isSome then 0 else
    CaseC.bankSpec.reuseMass st.cache m')]
  simp only [hm, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro m'
  by_cases h : m' = m
  · subst h
    simp [List.lookup_cons]
  · have hb' : (m' == m) = false := by simpa using h
    simp only [List.lookup_cons, hb', if_neg h]
theorem psi_birth_le (q : Nat) (st : RouterState) (X : HashInput) (hX : st.cache X = none)
    (hlen : st.births.length < q) :
    expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)
        (fun y => psi q (st.born X y)) ≤
      psi q st + (CaseC.theta + 1 / 64) / 2 ^ 128 := by
  rw [expectedValue_uniform_reply]
  have hs : (bankOf q st).slack = (q - (st.births.length + 1)) + 1 := by
    change q - st.births.length = _
    omega
  have h := ClaudeWCT.Bank.WCT.wct_core_birth CaseC.horizon ⊤ CaseC.excessBound_top (bankOf q st) _ hs
    (fun y => reuseC (st.born X y))
    (fun y => reuseC_birth st X y hX)
  refine le_trans (le_of_eq ?_) h
  apply tsum_congr
  intro y
  have hb : bankOf q (st.born X y) = { bankOf q st with
      targets := (bankOf q st).targets ++ [(y : HashOutput)]
      slack := q - (st.births.length + 1)
      reuse := reuseC (st.born X y) } := by
    simp only [bankOf, RouterState.born, List.map_cons, List.reverse_cons, List.length_cons]
    rfl
  congr 1
  exact congrArg CaseC.bankSpec.corePotential hb
theorem psi_cert (q : Nat) (st : RouterState) (h : CertGhost st) : 1 ≤ psi q st := by
  apply ClaudeWCT.Bank.WCT.wct_core_win CaseC.horizon ⊤ CaseC.excessBound_top
  · exact not_lt.mpr h.1
  · rcases h.2 with h | ⟨p, hp, hadm, hcov⟩
    · exact Or.inl h
    · refine Or.inr ⟨p.2, ?_, hadm, hcov⟩
      change p.2 ∈ (st.births.map Prod.snd).reverse
      rw [List.mem_reverse]
      exact List.mem_map_of_mem hp
theorem psi_initial (q : Nat) : psi q RouterState.initial ≤ (q : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  have h0 : reuseC RouterState.initial = 0 := by
    unfold reuseC
    apply ENNReal.tsum_eq_zero.mpr
    intro m
    have hc : ∀ Z, RouterState.initial.cache Z = none := fun _ => rfl
    have hm : RouterState.initial.memo.lookup m = none := rfl
    simp only [hm, Option.isSome_none, Bool.false_eq_true, if_false]
    simp only [ClaudeWCT.Bank.FtsBankSpec.reuseMass, ClaudeWCT.Bank.FtsBankSpec.admissibleEntry, hc,
      Option.elim_none, tsum_zero, ENNReal.zero_div]
  have hinit := ClaudeWCT.Bank.WCT.wct_core_initial CaseC.horizon (11324 / 100000000)
    ClaudeWCT.Numerics.WCTPrice.wct_excessBound_2_32 q
  rw [ClaudeWCT.Bank.WCT.wct_corePotential_rate CaseC.horizon (11324 / 100000000)
    ClaudeWCT.Numerics.WCTPrice.wct_excessBound_2_32 ⊤ CaseC.excessBound_top] at hinit
  unfold psi bankOf
  rw [h0]
  exact hinit
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell Probe Hit IsDigestRow lazyRun runWith_map readState
  probeState)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_observe_le lazy_pure)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Frame
variable (U : Finset HashInput)
def QFrame (X : HashInput) (s s' : LargeResidual.State WCoord (Cell U)) : Prop :=
  (∀ row : Cell U, row.1 ≠ X → s'.rows row = s.rows row) ∧ s'.counters.calls = s.counters.calls + 1 ∧
    s'.counters.mass = s.counters.mass ∧ ∀ m : Message, s'.candidates (.inr m) = s.candidates (.inr m)
theorem QFrame.of_disc {X : HashInput} {s1 s2 s3 : LargeResidual.State WCoord (Cell U)} (h1 : DiscFrame U s1 s2)
    (h2 : QFrame U X s2 s3) : QFrame U X s1 s3 :=
  ⟨fun row hr => (h2.1 row hr).trans (by rw [h1.1]), by rw [h2.2.1, h1.2.1], by rw [h2.2.2.1, h1.2.1],
    fun m => (h2.2.2.2 m).trans (h1.2.2 m)⟩
def InlTest (test : Probe WCoord) : Prop :=
  (∀ g ∈ test.guess, ∃ c : Coord, g.1 = Sum.inl c) ∧ ∀ p, test.hit = .label p → ∃ c : Coord, p = Sum.inl c
theorem restrict_inr (test : Probe WCoord) (htest : InlTest test) (cand : WCoord → Finset Digest)
    (y : LargeResidual.HashOutput) (m : Message) :
    (test.effective cand).restrict cand y (.inr m) = cand (.inr m) := by
  have hg : (test.effective cand).guessRestrict cand (.inr m) = cand (.inr m) := by
    unfold LargeResidual.Probe.guessRestrict
    cases hgs : (test.effective cand).guess with
    | none => rfl
    | some g =>
        have hmem : g ∈ test.guess := by
          have : (test.effective cand).guess = test.guess.filter _ := rfl
          rw [this] at hgs
          exact (Option.filter_eq_some_iff.mp hgs).1
        obtain ⟨c, hc⟩ := htest.1 g hmem
        simp only [eraseTableValue]
        rw [Function.update_of_ne (by rw [hc]; simp)]
  unfold LargeResidual.Probe.restrict
  have hh : (test.effective cand).hit = test.hit := rfl
  cases hhit : test.hit with
  | label p =>
      obtain ⟨c, hc⟩ := htest.2 p hhit
      rw [hh, hhit]
      simp only [LargeResidual.Hit.restrict, eraseTableValue]
      rw [Function.update_of_ne (by rw [hc]; simp), hg]
  | target t =>
      rw [hh, hhit]
      simp only [LargeResidual.Hit.restrict]
      exact hg
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem ev_lazy_map {α β : Type} (f : α → β) (comp : OracleComp (RWorld U) α) (s : LargeResidual.State WCoord (Cell U))
    (g : Option β × LargeResidual.State WCoord (Cell U) → ENNReal) :
    expectedValue (lazyRun aux q (f <$> comp) s) g = expectedValue (lazyRun aux q comp s) (fun r => g (r.1.map f, r.2)) := by
  rw [lazyRun, runWith_map, expectedValue_map]
  rfl
def OutcomeLe {α : Type} (X : HashInput) (s : LargeResidual.State WCoord (Cell U))
    (g : Option α × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal) : Prop :=
  (∀ v s', QFrame U X s s' → g (some v, s') ≤ B) ∧ ∀ s', s'.counters.mass = s.counters.mass → g (none, s') ≤ B
theorem ev_probeReq_le (row : Cell U) (test : Probe WCoord) (htest : InlTest test) (s : LargeResidual.State WCoord (Cell U))
    (g : Option LargeResidual.HashOutput × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal)
    (h : OutcomeLe U row.1 s g B) : expectedValue (lazyRun aux q (probeReq U row test) s) g ≤ B := by
  rw [← bind_pure (probeReq U row test)]
  cases hr : s.rows row with
  | some v =>
      rw [lazy_probeReq_cached U aux q row test _ s v hr, lazy_pure, expectedValue_pure]
      apply h.1
      refine ⟨fun row' hne => ?_, rfl, rfl, fun _ => rfl⟩
      simp only [readState]
      rw [Function.update_of_ne (fun he => hne (by rw [he]))]
  | none =>
      rw [lazy_probeReq_fresh U aux q row test _ s hr]
      apply ev_observe_le
      · rw [expectedValue_pure]
        exact h.2 _ rfl
      · intro y
        rw [lazy_pure, expectedValue_pure]
        apply h.1
        refine ⟨fun row' hne => ?_, rfl, rfl, fun m => restrict_inr test htest _ y m⟩
        simp only [probeState]
        rw [Function.update_of_ne (fun he => hne (by rw [he]))]
theorem ev_readReq_call_le (row : Cell U) (s : LargeResidual.State WCoord (Cell U))
    (g : Option LargeResidual.HashOutput × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal)
    (h : OutcomeLe U row.1 s g B) : expectedValue (lazyRun aux q (readReq U row .call) s) g ≤ B := by
  rw [← bind_pure (readReq U row .call), lazy_readReq]
  apply ev_bind_le
  intro y
  rw [lazy_pure, expectedValue_pure]
  apply h.1
  refine ⟨fun row' hne => ?_, rfl, rfl, fun _ => rfl⟩
  simp only [readState]
  rw [Function.update_of_ne (fun he => hne (by rw [he]))]
theorem ev_testReq_le (first : Bool) (row : Cell U) (test : Probe WCoord) (htest : InlTest test)
    (s : LargeResidual.State WCoord (Cell U))
    (g : Option LargeResidual.HashOutput × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal)
    (h : OutcomeLe U row.1 s g B) : expectedValue (lazyRun aux q (testReq U first row test) s) g ≤ B := by
  unfold testReq
  split
  · exact ev_probeReq_le U aux q row test htest s g B h
  · exact ev_readReq_call_le U aux q row s g B h
theorem OutcomeLe.map {α β : Type} {X : HashInput} {s : LargeResidual.State WCoord (Cell U)}
    {g : Option β × LargeResidual.State WCoord (Cell U) → ENNReal} {B : ENNReal} (f : α → β)
    (h : OutcomeLe U X s g B) : OutcomeLe U X s (fun r => g (r.1.map f, r.2)) B :=
  ⟨fun v s' hs => h.1 (f v) s' hs, fun s' hs => h.2 s' hs⟩
theorem OutcomeLe.of_disc {α : Type} {X : HashInput} {s s1 : LargeResidual.State WCoord (Cell U)}
    {g : Option α × LargeResidual.State WCoord (Cell U) → ENNReal} {B : ENNReal} (hd : DiscFrame U s s1)
    (h : OutcomeLe U X s g B) : OutcomeLe U X s1 g B :=
  ⟨fun v s' hs => h.1 v s' (QFrame.of_disc U hd hs), fun s' hs => h.2 s' (by rw [hs, hd.2.1])⟩
end Frame
section Invariant
variable {U : Finset HashInput}
theorem BankInv.after {ws ws' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (X : HashInput) (hX : ¬(X ∈ U ∧ IsDigestRow X)) (hf : QFrame U X ws ws') : BankInv U ws' (st.after X) := by
  have hne : ∀ X' (hX' : X' ∈ U), IsDigestRow X' → X' ≠ X := fun X' hX' hd he => hX ⟨he ▸ hX', he ▸ hd⟩
  refine ⟨by rw [hf.2.1, h.calls]; rfl, by rw [hf.2.2.1, hf.2.1]; exact (h.mass).trans (Nat.le_succ _),
    (h.births).trans (Nat.le_succ _), fun m hm => by rw [hf.2.2.2 m]; exact h.nonce m hm, ?_, ?_, ?_, h.trials⟩
  · intro X' hX' hd hs ht
    rw [hf.1 ⟨X', hX'⟩ (hne X' hX' hd)]
    exact h.fresh X' hX' hd (fun hm => hs (List.mem_cons_of_mem _ hm)) ht
  · intro X' hX' hd hs ht
    rw [hf.1 ⟨X', hX'⟩ (hne X' hX' hd)]
    have hs' : X' ∈ st.seen := by
      rcases List.mem_cons.mp hs with he | hm
      · exact absurd he (hne X' hX' hd)
      · exact hm
    exact h.seenRows X' hX' hd hs' ht
  · intro p hp
    exact List.mem_cons_of_mem _ (h.bornSeen p hp)
theorem BankInv.cache_none {ws : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    {X : HashInput} (hs : X ∉ st.seen) : st.cache X = none := by
  unfold RouterState.cache
  apply List.lookup_eq_none_iff.mpr
  intro p hp
  simp only [bne_iff_ne, ne_eq]
  intro he
  exact hs (he ▸ h.bornSeen p hp)
theorem BankInv.born {ws : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st) (q : Nat)
    (X : HashInput) (hX : X ∈ U) (hd : IsDigestRow X) (hs : X ∉ st.seen) (y : LargeResidual.HashOutput) :
    BankInv U (readState q ws ⟨X, hX⟩ y .mass) (st.born X y) := by
  refine ⟨?_, ?_, ?_, fun m hm => h.nonce m hm, ?_, ?_, ?_, h.trials⟩
  · simp only [readState, LargeResidual.Counters.charge, RouterState.born, RouterState.after, h.calls]
  · simp only [readState, LargeResidual.Counters.charge]
    have := h.mass
    split_ifs <;> omega
  · simp only [RouterState.born, RouterState.after, List.length_cons]
    exact Nat.succ_le_succ h.births
  · intro X' hX' hd' hs' ht'
    have hne : X' ≠ X := fun he => hs' (by rw [he]; exact List.mem_cons_self)
    simp only [readState]
    rw [Function.update_of_ne (fun he => hne (congrArg Subtype.val he))]
    exact h.fresh X' hX' hd' (fun hm => hs' (List.mem_cons_of_mem _ hm)) ht'
  · intro X' hX' hd' hs' ht'
    by_cases hxe : X' = X
    · subst hxe
      refine ⟨y, ?_, ?_⟩
      · rw [cache_birth, if_pos rfl]
      · simp only [readState, Function.update_self]
    · have hs2 : X' ∈ st.seen := by
        rcases List.mem_cons.mp hs' with he | hm
        · exact absurd he hxe
        · exact hm
      obtain ⟨v, hv1, hv2⟩ := h.seenRows X' hX' hd' hs2 ht'
      refine ⟨v, ?_, ?_⟩
      · rw [cache_birth, if_neg hxe]; exact hv1
      · simp only [readState]
        rw [Function.update_of_ne (fun he => hxe (congrArg Subtype.val he))]
        exact hv2
  · intro p hp
    rcases List.mem_cons.mp hp with he | hm
    · rw [he]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h.bornSeen p hm)
end Invariant
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section


namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell Probe Hit IsDigestRow lazyRun readState)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le lazy_pure birth_pay)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Step
variable {U : Finset HashInput}
theorem BankInv.after' {ws ws' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (X : HashInput) (hrows : ∀ row : Cell U, row.1 ≠ X → ws'.rows row = ws.rows row)
    (hX : ∀ hX : X ∈ U, IsDigestRow X → X ∉ st.trials → ∃ y, st.cache X = some y ∧ ws'.rows ⟨X, hX⟩ = some y)
    (hcalls : ws'.counters.calls = ws.counters.calls + 1) (hmass : ws'.counters.mass ≤ ws'.counters.calls)
    (hcand : ∀ m : Message, ws'.candidates (.inr m) = ws.candidates (.inr m)) : BankInv U ws' (st.after X) := by
  refine ⟨by rw [hcalls, h.calls]; rfl, hmass, (h.births).trans (Nat.le_succ _),
    fun m hm => by rw [hcand m]; exact h.nonce m hm, ?_, ?_, ?_, h.trials⟩
  · intro X' hX' hd hs ht
    have hne : X' ≠ X := fun he => hs (by rw [he]; exact List.mem_cons_self)
    rw [hrows ⟨X', hX'⟩ hne]
    exact h.fresh X' hX' hd (fun hm => hs (List.mem_cons_of_mem _ hm)) ht
  · intro X' hX' hd hs ht
    by_cases hne : X' = X
    · subst hne
      exact hX hX' hd ht
    · rw [hrows ⟨X', hX'⟩ hne]
      have hs' : X' ∈ st.seen := by
        rcases List.mem_cons.mp hs with he | hm
        · exact absurd he hne
        · exact hm
      exact h.seenRows X' hX' hd hs' ht
  · intro p hp
    exact List.mem_cons_of_mem _ (h.bornSeen p hp)
theorem slackT_eq_of_mass {s s' : LargeResidual.State WCoord (Cell U)} (q : Nat)
    (h : s'.counters.mass = s.counters.mass) : slackT q s' = slackT q s := by
  unfold slackT; rw [h]
theorem slackT_le_of_mass {s s' : LargeResidual.State WCoord (Cell U)} (q : Nat)
    (h : s.counters.mass ≤ s'.counters.mass) : slackT q s' ≤ slackT q s := by
  unfold slackT
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.sub_le_sub_left h q
theorem inlTest_guess (c : Coord) (v : Digest) (hit : Hit WCoord) (hh : ∀ p, hit = .label p → ∃ c' : Coord, p = .inl c') :
    InlTest ⟨some (.inl c, v), hit⟩ :=
  ⟨fun g hg => ⟨c, by cases hg; rfl⟩, hh⟩
theorem inlTest_none (hit : Hit WCoord) (hh : ∀ p, hit = .label p → ∃ c' : Coord, p = .inl c') :
    InlTest ⟨none, hit⟩ :=
  ⟨fun g hg => absurd hg (by simp), hh⟩
theorem hit_label_inl (c : Coord) : ∀ p, (LargeResidual.Hit.label (Sum.inl c) : Hit WCoord) = .label p → ∃ c' : Coord, p = .inl c' :=
  fun p hp => ⟨c, by cases hp; rfl⟩
theorem hit_target (t : Digest) : ∀ p, (LargeResidual.Hit.target t : Hit WCoord) = .label p → ∃ c' : Coord, p = .inl c' :=
  fun p hp => by cases hp
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem bank_routeQuery (a : AuxData) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (X : HashInput)
    (hinv : BankInv U ws st) (hlt : st.calls < q)
    (g : Option (LargeResidual.HashOutput × RouterState) × LargeResidual.State WCoord (Cell U) → ENNReal)
    (hstop : ∀ ws', g (none, ws') ≤ slackT q ws')
    (hcont : ∀ y st' ws', BankInv U ws' st' → st'.calls ≤ q → g (some (y, st'), ws') ≤ psi q st' + slackT q ws') :
    expectedValue (lazyRun aux q (routeQuery U a st X) ws) g ≤ psi q st + slackT q ws := by
  have hnd : ¬(X ∈ U ∧ IsDigestRow X) →
      OutcomeLe U X ws (fun r : Option LargeResidual.HashOutput × _ => g (r.1.map fun y => (y, st.after X), r.2))
        (psi q st + slackT q ws) := by
    intro hX
    refine ⟨fun y s' hs => ?_, fun s' hs => ?_⟩
    · have hinv' := hinv.after X hX hs
      refine (hcont y (st.after X) s' hinv' (by change st.calls + 1 ≤ q; omega)).trans ?_
      rw [psi_after, slackT_eq_of_mass q hs.2.2.1]
    · exact (hstop s').trans ((le_of_eq (slackT_eq_of_mass q hs)).trans le_add_self)
  unfold routeQuery
  dsimp only
  by_cases hX : X ∈ U
  · rw [dif_pos hX]
    by_cases hp : Parsed X
    · rw [dif_pos hp]
      have hndX : ¬(X ∈ U ∧ IsDigestRow X) := fun h => not_parsed_of_digest h.2 hp
      split
      · rename_i cs hfu
        rw [ev_lazy_map]
        exact ev_testReq_le U aux q _ ⟨X, hX⟩ _ (inlTest_guess _ _ _ (hit_label_inl _)) ws _ _ ((hnd hndX).map U _)
      · rename_i hfu
        apply ev_discloseAll_le
        intro pairs s1 hd
        split
        · rw [lazy_discloseReq]
          apply ev_bind_le
          intro v
          rw [lazy_pure, expectedValue_pure]
          apply ((hnd hndX).of_disc U hd).1
          refine ⟨fun row hr => rfl, rfl, rfl, fun m => ?_⟩
          simp only [discloseTableValue]
          rw [Function.update_of_ne (by simp)]
        · rw [ev_lazy_map]
          exact ev_testReq_le U aux q _ ⟨X, hX⟩ _ (inlTest_none _ (hit_label_inl _))
            s1 _ _ (((hnd hndX).of_disc U hd).map U _)
    · rw [dif_neg hp]
      by_cases he : EncRow X
      · rw [dif_pos he]
        have hndX : ¬(X ∈ U ∧ IsDigestRow X) := by
          intro h
          obtain ⟨L, m, ctr, pad, -, hXe⟩ := he
          rw [hXe] at h
          exact encRow_not_digest L m ctr pad h.2
        split
        · rename_i cs hfu
          rw [ev_lazy_map]
          exact ev_testReq_le U aux q _ ⟨X, hX⟩ _ (inlTest_guess _ _ _ (hit_target _)) ws _ _ ((hnd hndX).map U _)
        · rename_i hfu
          apply ev_discloseAll_le
          intro pairs s1 hd
          split
          · rw [lazy_tickReq, lazy_pure, expectedValue_pure]
            apply ((hnd hndX).of_disc U hd).1
            exact ⟨fun row hr => rfl, rfl, rfl, fun m => rfl⟩
          · rw [ev_lazy_map]
            exact ev_testReq_le U aux q _ ⟨X, hX⟩ _ (inlTest_none _ (hit_target _))
              s1 _ _ (((hnd hndX).of_disc U hd).map U _)
      · rw [dif_neg he]
        by_cases hd : IsDigestRow X
        · rw [if_pos hd, ev_lazy_map, ← bind_pure (readReq U ⟨X, hX⟩ .mass), lazy_readReq]
          simp only [lazy_pure, expectedValue_bind, expectedValue_pure, Option.map_some]
          have hcalls : ws.counters.calls + 1 ≤ q := by rw [hinv.calls]; omega
          have hmass_lt : ws.counters.mass < q := by have := hinv.mass; omega
          by_cases hfr : st.Fresh X
          ·
            have hnone : ws.rows ⟨X, hX⟩ = none := hinv.fresh X hX hd hfr.1 hfr.2
            have hc0 : st.cache X = none := hinv.cache_none hfr.1
            have hlen : st.births.length < q := by have := hinv.births; omega
            rw [reply, hnone]
            dsimp only
            simp only [if_pos hfr]
            have hpt : ∀ y : LargeResidual.HashOutput,
                g (some (y, st.born X y), readState q ws ⟨X, hX⟩ y .mass) ≤
                  psi q (st.born X y) + ((q - (ws.counters.mass + 1) : Nat) : ENNReal) / 2 ^ 128 := by
              intro y
              refine (hcont y _ _ (hinv.born q X hX hd hfr.1 y) (by
                change st.calls + 1 ≤ q; omega)).trans (le_of_eq ?_)
              congr 1
              unfold slackT
              simp only [readState, LargeResidual.Counters.charge, if_pos hcalls]
            calc
              _ ≤ expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)
                  (fun y => psi q (st.born X y) + ((q - (ws.counters.mass + 1) : Nat) : ENNReal) / 2 ^ 128) :=
                expectedValue_mono _ hpt
              _ ≤ psi q st + (CaseC.theta + 1 / 64) / 2 ^ 128 + ((q - (ws.counters.mass + 1) : Nat) : ENNReal) / 2 ^ 128 := by
                rw [expectedValue_add]
                exact add_le_add (psi_birth_le q st X hc0 hlen) (expectedValue_le_of_le _ fun _ => le_rfl)
              _ ≤ _ := birth_pay _ q hmass_lt _
          · simp only [if_neg hfr]
            by_cases ht : X ∈ st.trials
            ·
              apply expectedValue_le_of_le
              intro y
              have hinv' : BankInv U (readState q ws ⟨X, hX⟩ y .mass) (st.after X) := by
                refine hinv.after' X (fun row hr => ?_) (fun _ _ ht' => absurd ht ht') rfl ?_ (fun _ => rfl)
                · simp only [readState]
                  rw [Function.update_of_ne (fun he' => hr (by rw [he']))]
                · simp only [readState, LargeResidual.Counters.charge, if_pos hcalls]
                  have := hinv.mass; omega
              refine (hcont y _ _ hinv' (by change st.calls + 1 ≤ q; omega)).trans ?_
              · rw [psi_after]
                exact add_le_add le_rfl (slackT_le_of_mass q (by
                  simp only [readState, LargeResidual.Counters.charge, if_pos hcalls]; omega))
            ·
              have hs : X ∈ st.seen := by
                by_contra hs'
                exact hfr ⟨hs', ht⟩
              obtain ⟨v, hv1, hv2⟩ := hinv.seenRows X hX hd hs ht
              rw [reply, hv2]
              dsimp only
              rw [expectedValue_pure]
              have hupd : Function.update ws.rows ⟨X, hX⟩ (some v) = ws.rows := by
                rw [← hv2, Function.update_eq_self]
              have hinv' : BankInv U (readState q ws ⟨X, hX⟩ v .mass) (st.after X) := by
                refine hinv.after' X (fun row hr => ?_) (fun _ _ _ => ⟨v, hv1, ?_⟩) rfl ?_ (fun _ => rfl)
                · simp only [readState, hupd]
                · simp only [readState, hupd]; exact hv2
                · simp only [readState, LargeResidual.Counters.charge, if_pos hcalls]
                  have := hinv.mass; omega
              refine (hcont v _ _ hinv' (by change st.calls + 1 ≤ q; omega)).trans ?_
              · rw [psi_after]
                exact add_le_add le_rfl (slackT_le_of_mass q (by
                  simp only [readState, LargeResidual.Counters.charge, if_pos hcalls]; omega))
        · rw [if_neg hd, ev_lazy_map]
          exact ev_readReq_call_le U aux q ⟨X, hX⟩ ws _ _ ((hnd fun h => hd h.2).map U _)
  · rw [dif_neg hX, lazy_tickReq, lazy_pure, expectedValue_pure]
    apply (hnd fun h => hX h.1).1
    exact ⟨fun row hr => rfl, rfl, rfl, fun m => rfl⟩
end Step
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section


namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell IsDigestRow lazyRun readState)
open SigGolfCandidate.T3.Security.LargeCoupling (lazy_pure trial_ne reply_of_some reply_of_none
  expectedValue_uniform_ro)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
section Search
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (a : AuxData) (rho : Digest) (m : Message)
def SearchFrame (c fuel : Nat) (found : Option (BitVec 32 × LargeResidual.HashOutput))
    (s s' : LargeResidual.State WCoord (Cell U)) : Prop :=
  s'.candidates = s.candidates ∧ s'.counters = s.counters ∧
    (∀ k' out, found = some (k', out) → c ≤ k'.toNat ∧ k'.toNat < c + fuel) ∧
    ∀ row : Cell U, s'.rows row ≠ s.rows row → ∃ k, c ≤ k ∧ k < c + fuel ∧
      row.1 = pad64 (digestInput rho m (BitVec.ofNat 32 k)) ∧ ∀ k' out, found = some (k', out) → k ≤ k'.toNat
theorem readImpl_digest (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U) (c : Nat) :
    simulateQ (readImpl U a) (digest rho m (BitVec.ofNat 32 c)) =
      readReq U ⟨_, hU (BitVec.ofNat 32 c)⟩ .none := by
  change simulateQ (readImpl U a) (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c))))))) = _
  rw [simulateQ_spec_query]
  simp only [readImpl, dif_pos (hU (BitVec.ofNat 32 c))]
theorem lazy_readImpl_digest (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U) (c : Nat) {β : Type}
    (k : HashOutput → OracleComp (RWorld U) β) (s : LargeResidual.State WCoord (Cell U)) :
    lazyRun aux q (simulateQ (readImpl U a) (digest rho m (BitVec.ofNat 32 c)) >>= k) s =
      (reply s.rows ⟨_, hU (BitVec.ofNat 32 c)⟩ >>= fun y =>
        lazyRun aux q (k y) (readState q s ⟨_, hU (BitVec.ofNat 32 c)⟩ y .none)) := by
  rw [readImpl_digest]
  exact lazy_readReq U aux q _ _ k s
theorem bank_search (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U) (secret : BitVec 256) :
    ∀ (fuel c : Nat), c + fuel ≤ 2 ^ 32 → ∀ (s : LargeResidual.State WCoord (Cell U)) (cache : Sampling.RCache),
      (∀ k, c ≤ k → k < 2 ^ 32 →
        s.rows ⟨_, hU (BitVec.ofNat 32 k)⟩ = cache (pad64 (digestInput rho m (BitVec.ofNat 32 k)))) →
      ∀ (G : Option (Option (BitVec 32 × LargeResidual.HashOutput)) × LargeResidual.State WCoord (Cell U) → ENNReal)
        (H : Option (BitVec 32 × LargeResidual.HashOutput) → ENNReal),
        (∀ found s', SearchFrame rho m c fuel found s s' → G (some found, s') ≤ H found) →
        expectedValue (lazyRun aux q (simulateQ (readImpl U a) (WCT9.digestSearch rho m c fuel)) s) G ≤
          expectedValue (Sampling.roRun secret (WCT9.digestSearch rho m c fuel) cache) (fun r => H r.1) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c _ s cache _ G H hG
      simp only [WCT9.digestSearch, simulateQ_pure, Sampling.roRun_pure, expectedValue_pure]
      rw [lazy_pure, expectedValue_pure]
      apply hG
      refine ⟨rfl, rfl, fun k' out h => (by cases h), fun row h => absurd rfl h⟩
  | succ fuel ih =>
      intro c hc s cache hagree G H hG
      have hc32 : c < 2 ^ 32 := by omega
      set X : Cell U := ⟨_, hU (BitVec.ofNat 32 c)⟩ with hXdef
      simp only [BPB.digestSearch_succ, simulateQ_bind, Sampling.roRun_bind]
      rw [lazy_readImpl_digest aux q a rho m hU c]
      have hro : Sampling.roRun secret (digest rho m (BitVec.ofNat 32 c)) cache =
          (randomOracle (spec := SphincsSecurity.HashSpec) (pad64 (digestInput rho m (BitVec.ofNat 32 c)))).run cache :=
        Sampling.roRun_publicQuery secret _ cache
      simp only [hro, randomOracle.run_eq]
      have hXc := hagree c le_rfl hc32
      have hstep : ∀ (y : LargeResidual.HashOutput) (cache' : Sampling.RCache),
          (∀ k, c + 1 ≤ k → k < 2 ^ 32 →
            cache' (pad64 (digestInput rho m (BitVec.ofNat 32 k))) =
              cache (pad64 (digestInput rho m (BitVec.ofNat 32 k)))) →
          expectedValue (lazyRun aux q (simulateQ (readImpl U a)
              (if WCT9.admissible y = true then pure (some (BitVec.ofNat 32 c, y))
                else WCT9.digestSearch rho m (c + 1) fuel)) (readState q s X y .none)) G ≤
            expectedValue (Sampling.roRun secret
              (if WCT9.admissible y = true then pure (some (BitVec.ofNat 32 c, y))
                else WCT9.digestSearch rho m (c + 1) fuel) cache') (fun r => H r.1) := by
        intro y cache' hcache'
        have hrowsX : ∀ row : Cell U, (readState q s X y .none).rows row ≠ s.rows row → row = X := by
          intro row hr
          by_contra hne
          apply hr
          simp only [readState]
          rw [Function.update_of_ne hne]
        by_cases hadm : WCT9.admissible y = true
        · simp only [hadm, if_true, simulateQ_pure, Sampling.roRun_pure, expectedValue_pure]
          rw [lazy_pure, expectedValue_pure]
          apply hG
          have hcn : (BitVec.ofNat 32 c).toNat = c := by
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc32]
          refine ⟨rfl, rfl, fun k' out h => ?_, fun row hr => ?_⟩
          · cases h
            rw [hcn]; omega
          · have hrX := hrowsX row hr
            refine ⟨c, le_rfl, by omega, by rw [hrX], fun k' out h => ?_⟩
            cases h
            rw [hcn]
        · simp only [hadm, Bool.false_eq_true, if_false]
          apply ih (c + 1) (by omega) (readState q s X y .none) cache'
          · intro k hk hk32
            have hne : (⟨_, hU (BitVec.ofNat 32 k)⟩ : Cell U) ≠ X := by
              intro he
              exact trial_ne rho m hk32 hc32 (by omega) (congrArg Subtype.val he)
            simp only [readState]
            rw [Function.update_of_ne hne, hcache' k hk hk32]
            exact hagree k (by omega) hk32
          · intro found s' hf
            apply hG
            obtain ⟨h1, h2, h3, h4⟩ := hf
            refine ⟨h1, h2, fun k' out h => ?_, fun row hr => ?_⟩
            · have := h3 k' out h; omega
            · by_cases hr1 : s'.rows row ≠ (readState q s X y .none).rows row
              · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := h4 row hr1
                exact ⟨k, by omega, by omega, hk3, hk4⟩
              · push Not at hr1
                have hrX := hrowsX row (by rw [← hr1]; exact hr)
                refine ⟨c, le_rfl, by omega, by rw [hrX], fun k' out h => ?_⟩
                have := (h3 k' out h).1; omega
      cases hcache : cache (pad64 (digestInput rho m (BitVec.ofNat 32 c))) with
      | some u =>
          have hsX : s.rows ⟨_, hU (BitVec.ofNat 32 c)⟩ = some u := hXc.trans hcache
          rw [reply_of_some hsX, pure_bind, pure_bind]
          exact hstep u cache (fun _ _ _ => rfl)
      | none =>
          have hsX : s.rows ⟨_, hU (BitVec.ofNat 32 c)⟩ = none := hXc.trans hcache
          rw [reply_of_none hsX, expectedValue_bind, bind_assoc, expectedValue_bind, expectedValue_uniform_ro]
          apply expectedValue_mono
          intro y
          rw [pure_bind]
          dsimp only
          have hc' : ∀ k, c + 1 ≤ k → k < 2 ^ 32 →
              (QueryCache.cacheQuery cache (pad64 (digestInput rho m (BitVec.ofNat 32 c))) y)
                (pad64 (digestInput rho m (BitVec.ofNat 32 k))) = cache (pad64 (digestInput rho m (BitVec.ofNat 32 k))) := by
            intro k hk hk32
            exact QueryCache.cacheQuery_of_ne _ _ (trial_ne rho m hk32 hc32 (by omega))
          exact hstep y _ hc'
end Search
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section


namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell IsDigestRow lazyRun disclosedState)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le lazy_pure ev_runWith_bind expectedValue_cell_univ
  digestRow_isDigest digestRow_mem)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingBankSign : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Sign
variable {U : Finset HashInput}
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
theorem psi_signed (q : Nat) (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × LargeResidual.HashOutput)) :
    psi q (st.signed rho m found) =
      if CaseC.bankSpec.Reuse st.cache rho m then
        CaseC.bankSpec.corePotential { bankOf q st with reused := true, reuse := reuseC (st.signed 0 m none) }
      else CaseC.bankSpec.corePotential ((bankOf q st).expose (reuseC (st.signed 0 m none)) (found.map Prod.snd)) := by
  rw [← reuseC_signed_eq st rho 0 m found none]
  unfold psi
  by_cases hr : CaseC.bankSpec.Reuse st.cache rho m
  · rw [if_pos hr]
    congr 1
    unfold bankOf RouterState.signed
    rw [if_pos hr]
  · rw [if_neg hr]
    congr 1
    unfold bankOf CaseC.BankCore.expose RouterState.signed
    rw [if_neg hr]
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
    (hk : k < WCT9.digestAttemptLimit) (hf : ∀ k' out, found = some (k', out) → k ≤ k'.toNat) :
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
    (hf : SearchFrame rho m 0 WCT9.digestAttemptLimit found (disclosedState q ws (.inr m) rho .none) s') :
    BankInv U s' (st.signed rho m found) := by
  obtain ⟨hdisc, hseen, hcalls, hbirths, htrials, hmemo⟩ := RouterState.signed_fields st rho m found
  obtain ⟨hcand, hcount, -, hrows⟩ := hf
  have hcache : (st.signed rho m found).cache = st.cache := by
    funext X; simp only [RouterState.cache, hbirths]
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
theorem bank_routeSign (hUpub : SeccLaw.publicUniverse ⊆ U) (a : AuxData) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
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
      have hC : C0 + CaseC.bankSpec.reuseMass st.cache m ≤ (bankOf q st).reuse := by
        rw [hC0, reuseC_signed st 0 m none hm]; exact le_rfl
      have hcore := ClaudeWCT.Bank.WCT.wct_core_sign CaseC.horizon ⊤ CaseC.excessBound_top (bankOf q st) st.cache m C0 hC 0
        WCT9.digestAttemptLimit WCT9.digestAttemptLimit_le
      have hrho : ∀ rho : Digest,
          expectedValue (lazyRun aux q (simulateQ (readImpl U a) (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit) >>= fun found =>
              signFinish U a (st.signed rho m found) rho found) (disclosedState q ws (.inr m) rho .none)) g ≤
            (if CaseC.bankSpec.Reuse st.cache rho m then CaseC.bankSpec.corePotential { bankOf q st with reused := true, reuse := C0 }
              else expectedValue (Sampling.roRun 0 (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit) st.cache)
                (fun result => CaseC.bankSpec.corePotential ((bankOf q st).expose C0 (result.1.map Prod.snd)))) +
              slackT q ws := by
        intro rho
        rw [lazyRun, ev_runWith_bind, ← lazyRun]
        have hsearch := bank_search aux q a rho m (digestRow_mem hUpub rho m) 0 WCT9.digestAttemptLimit 0
          (by rw [Nat.zero_add]; exact WCT9.digestAttemptLimit_le)
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
        by_cases hr : CaseC.bankSpec.Reuse st.cache rho m
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
            (if CaseC.bankSpec.Reuse st.cache rho m then CaseC.bankSpec.corePotential { bankOf q st with reused := true, reuse := C0 }
              else expectedValue (Sampling.roRun 0 (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit) st.cache)
                (fun result => CaseC.bankSpec.corePotential ((bankOf q st).expose C0 (result.1.map Prod.snd)))) +
              slackT q ws) := expectedValue_mono _ hrho
        _ ≤ CaseC.bankSpec.corePotential (bankOf q st) + slackT q ws := by
          rw [expectedValue_add]
          exact add_le_add hcore (expectedValue_le_of_le _ fun _ => le_rfl)
        _ = _ := rfl
end Sign
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
