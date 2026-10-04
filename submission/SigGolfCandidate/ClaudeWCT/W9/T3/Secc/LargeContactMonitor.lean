import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingSplit
import SigGolfCandidate.T3.Secc.LargeContactMonitor

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (slotValue IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (chargeOf EventsAgree)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem Known.mono {D D' : Coord → Prop} (h : ∀ c, D c → D' c) {c : Coord} (hk : Known D c) : Known D' c := by
  induction hk with
  | base hc => exact .base (h _ hc)
  | node _ ih => exact .node ih
def Clear (A : Answers) (K : Coord → Prop) (X : HashInput) (y : HashOutput) : Prop :=
  (∀ N : CanonGraph.Node, Extract.posOf X = some N.toPos →
      ¬(X ≠ Extract.honestInput A N.toPos ∧ y.extractLsb' 0 128 = honestValue A (.inl N))) ∧
  (∀ N : CanonGraph.Node, Extract.posOf X = some N.toPos → ∀ c b, childSlots N = [(c, b)] →
      slotValue X b = honestValue A c → K c) ∧
  (∀ (L : CanonEncoding.EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32) (pad : BitVec 96),
      Extract.msgFits L.1.lay m → X = Wots.encRow L.toWots m ctr pad →
      ¬(Wots.referenceInput A L.toWots ≠ some X ∧
        decode L.1.lay (y.extractLsb' 0 128) = some (Wots.referenceDigits A L.toWots)))
theorem firstUnknown_single (K : Coord → Prop) (N : CanonGraph.Node) (c : Coord) (b : Nat)
    (h : childSlots N = [(c, b)]) (hk : ¬K c) : firstUnknown K N = some (c, b) := by
  unfold firstUnknown
  rw [h]
  simp [hk]
theorem clear_of_not_contact {A : Answers} {K : Coord → Prop} {X : HashInput} {y : HashOutput}
    (h : ¬ContactTest A K X y) : Clear A K X y := by
  refine ⟨fun N hpos hhit => h (Or.inl ⟨N, hpos, Or.inr hhit⟩), fun N hpos c b hs hv => ?_,
    fun L m ctr pad hfit hX hhit => h (Or.inr ⟨L, m, ctr, pad, hfit, hX, Or.inr hhit⟩)⟩
  by_contra hk
  exact h (Or.inl ⟨N, hpos, Or.inl ⟨(c, b), firstUnknown_single K N c b hs hk, hv⟩⟩)
theorem Clear.mono {A : Answers} {K K' : Coord → Prop} {X : HashInput} {y : HashOutput}
    (h : Clear A K X y) (hK : ∀ c, K c → K' c) : Clear A K' X y :=
  ⟨h.1, fun N hpos c b hs hv => hK c (h.2.1 N hpos c b hs hv), h.2.2⟩
def MonitorOK (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) : Prop :=
  monitor.contact = false → monitor.calls ≤ q → ∀ X ∈ monitor.seen, X ∈ U →
    Clear A monitor.known X (A (.inl (.inr X)))
theorem monitorOK_initial (U : Finset HashInput) (A : Answers) (q : Nat) : MonitorOK U A q Monitor.initial := by
  intro _ _ X hX
  simp [Monitor.initial] at hX
theorem monitorOK_query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput)
    (h : MonitorOK U A q monitor) : MonitorOK U A q (monitor.query U A q X (A (.inl (.inr X)))) := by
  unfold Monitor.query
  by_cases hc : monitor.contact = true
  · rw [if_pos hc]; exact h
  rw [if_neg hc]
  by_cases ht : X ∉ monitor.seen ∧ X ∈ U ∧ monitor.calls + 1 ≤ q ∧ ContactTest A monitor.known X (A (.inl (.inr X)))
  · rw [if_pos ht]
    intro hfalse
    simp at hfalse
  · rw [if_neg ht]
    intro _ hq Y hY hYU
    change monitor.calls + 1 ≤ q at hq
    have hcf : monitor.contact = false := by simpa using hc
    have hq' : monitor.calls ≤ q := by omega
    simp only [List.mem_cons] at hY
    change Clear A monitor.known Y (A (.inl (.inr Y)))
    rcases hY with rfl | hY
    · by_cases hs : Y ∈ monitor.seen
      · exact h hcf hq' Y hs hYU
      · exact clear_of_not_contact (fun hct => ht ⟨hs, hYU, hq, hct⟩)
    · exact h hcf hq' Y hY hYU
theorem monitorOK_sign (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (monitor : Monitor) (request : Security.Request)
    (h : MonitorOK U A q monitor) : MonitorOK U A q (monitor.sign A published request) := by
  unfold Monitor.sign
  by_cases hc : monitor.contact = true
  · rw [if_pos hc]; exact h
  rw [if_neg hc]
  intro _ hq Y hY hYU
  have hcf : monitor.contact = false := by simpa using hc
  refine (h hcf hq Y hY hYU).mono fun c hk => Known.mono (fun d hd => ?_) hk
  rcases hd with hd | hd
  · exact Or.inl hd
  · exact Or.inr (List.mem_append_left _ hd)
theorem monitorOK_event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent)
    (hagree : SourceReplay.IsHash event.input → A event.input = event.answer) (h : MonitorOK U A q monitor) :
    MonitorOK U A q (monitor.event U A q event) := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · have hagree' : A (.inl (.inr X)) = answer := hagree trivial
    subst hagree'
    exact monitorOK_query U A q monitor X h
  · exact h
theorem monitorOK_events (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (hagree : EventsAgree A events)
    (monitor : Monitor) (h : MonitorOK U A q monitor) : MonitorOK U A q (events.foldl (Monitor.event U A q) monitor) := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih =>
      rw [List.foldl_cons]
      exact ih (fun e he => hagree e (List.mem_cons_of_mem _ he)) _
        (monitorOK_event U A q monitor event (hagree event List.mem_cons_self) h)
def StepsAgree (A : Answers) (steps : List TaggedStep) : Prop :=
  ∀ step ∈ steps, ∀ event, step = .world event → SourceReplay.IsHash event.input → A event.input = event.answer
theorem monitorOK_steps (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (hagree : StepsAgree A steps) (monitor : Monitor) (h : MonitorOK U A q monitor) :
    MonitorOK U A q (steps.foldl (Monitor.step U A q published) monitor) := by
  induction steps generalizing monitor with
  | nil => exact h
  | cons step rest ih =>
      rw [List.foldl_cons]
      apply ih (fun s hs e he => hagree s (List.mem_cons_of_mem _ hs) e he)
      cases step with
      | world event => exact monitorOK_event U A q monitor event (hagree _ List.mem_cons_self event rfl) h
      | sign request output events => exact monitorOK_sign U A q published monitor request h
theorem monitorRun_clear (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) (hsteps : StepsAgree A steps) (hverdict : EventsAgree A verdict)
    (hno : (monitorRun U A q published steps verdict).contact = false)
    (hcalls : (monitorRun U A q published steps verdict).calls ≤ q) :
    ∀ X ∈ (monitorRun U A q published steps verdict).seen, X ∈ U →
      Clear A (monitorRun U A q published steps verdict).known X (A (.inl (.inr X))) :=
  monitorOK_events U A q verdict hverdict _
    (monitorOK_steps U A q published steps hsteps _ (monitorOK_initial U A q)) hno hcalls
theorem contact_query_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput)
    (h : monitor.contact = true) : (monitor.query U A q X y).contact = true := by
  unfold Monitor.query; rw [if_pos h]; exact h
theorem contact_event_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent)
    (h : monitor.contact = true) : (monitor.event U A q event).contact = true := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · exact contact_query_mono U A q monitor X answer h
  · exact h
theorem contact_events_mono (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (h : monitor.contact = true) : (events.foldl (Monitor.event U A q) monitor).contact = true := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih => exact ih _ (contact_event_mono U A q monitor event h)
theorem seen_query_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X Y : HashInput) (y : HashOutput)
    (h : Y ∈ monitor.seen) : Y ∈ (monitor.query U A q X y).seen := by
  unfold Monitor.query
  split_ifs <;> simp [h]
theorem seen_event_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) (Y : HashInput)
    (h : Y ∈ monitor.seen) : Y ∈ (monitor.event U A q event).seen := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · exact seen_query_mono U A q monitor X Y answer h
  · exact h
theorem seen_events_mono (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (Y : HashInput) (h : Y ∈ monitor.seen) : Y ∈ (events.foldl (Monitor.event U A q) monitor).seen := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih => exact ih _ (seen_event_mono U A q monitor event Y h)
theorem events_seen (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (hno : (events.foldl (Monitor.event U A q) monitor).contact = false) :
    ∀ event ∈ events, ∀ X, event.input = .inl (.inr X) → X ∈ (events.foldl (Monitor.event U A q) monitor).seen := by
  induction events generalizing monitor with
  | nil => intro event he; cases he
  | cons event rest ih =>
      intro e he X hX
      rw [List.foldl_cons] at hno ⊢
      rcases List.mem_cons.mp he with rfl | he
      · apply seen_events_mono
        rcases e with ⟨before, (n | Y) | c, answer⟩
        · cases hX
        · simp only [Sum.inl.injEq, Sum.inr.injEq] at hX
          subst hX
          change Y ∈ (monitor.query U A q Y answer).seen
          by_cases hc : monitor.contact = true
          · exfalso
            have := contact_events_mono U A q rest _ (contact_event_mono U A q monitor ⟨before, .inl (.inr Y), answer⟩ hc)
            rw [hno] at this
            exact Bool.false_ne_true this
          · unfold Monitor.query
            rw [if_neg hc]
            split_ifs <;> exact List.mem_cons_self
        · cases hX
      · exact ih _ hno e he X hX
theorem disclosed_query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput) :
    (monitor.query U A q X y).disclosed = monitor.disclosed := by
  unfold Monitor.query
  split_ifs <;> rfl
theorem disclosed_event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) :
    (monitor.event U A q event).disclosed = monitor.disclosed := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact disclosed_query U A q monitor X answer
  · rfl
theorem disclosed_events (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor) :
    (events.foldl (Monitor.event U A q) monitor).disclosed = monitor.disclosed := by
  induction events generalizing monitor with
  | nil => rfl
  | cons event rest ih => rw [List.foldl_cons, ih, disclosed_event]
theorem disclosed_steps (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (monitor : Monitor) (c : Coord) (hc : c ∈ (steps.foldl (Monitor.step U A q published) monitor).disclosed) :
    c ∈ monitor.disclosed ∨ ∃ request, c ∈ signDisclosed A published request := by
  induction steps generalizing monitor with
  | nil => exact Or.inl hc
  | cons step rest ih =>
      rw [List.foldl_cons] at hc
      rcases ih _ hc with h | h
      · cases step with
        | world event =>
            change c ∈ (monitor.event U A q event).disclosed at h
            rw [disclosed_event] at h
            exact Or.inl h
        | sign request output events =>
            change c ∈ (monitor.sign A published request).disclosed at h
            unfold Monitor.sign at h
            split_ifs at h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact Or.inl h
              · exact Or.inr ⟨request, h⟩
      · exact Or.inr h
theorem monitorRun_known (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) (c : Coord) (hk : (monitorRun U A q published steps verdict).known c) :
    Known (fun d => d ∈ keygenDisclosed ∨ ∃ request, d ∈ signDisclosed A published request) c := by
  refine Known.mono (fun d hd => ?_) hk
  rcases hd with hd | hd
  · exact Or.inl hd
  · unfold monitorRun at hd
    rw [disclosed_events] at hd
    rcases disclosed_steps U A q published steps Monitor.initial d hd with h | h
    · simp [Monitor.initial] at h
    · exact Or.inr h
theorem calls_query_le (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput) :
    (monitor.query U A q X y).calls ≤ monitor.calls + 1 := by
  unfold Monitor.query
  split_ifs <;> simp
theorem calls_event_le (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) :
    (monitor.event U A q event).calls ≤ monitor.calls + FullGame.queryCharge event.input := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact Nat.le_add_right _ _
  · have h1 : FullGame.queryCharge (.inl (.inr X)) = 1 := by
      simp [FullGame.queryCharge, Derivation.charged]
    rw [h1]
    exact calls_query_le U A q monitor X answer
  · exact Nat.le_add_right _ _
theorem calls_events_le (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor) :
    (events.foldl (Monitor.event U A q) monitor).calls ≤ monitor.calls + chargeOf events := by
  induction events generalizing monitor with
  | nil => simp [chargeOf]
  | cons event rest ih =>
      rw [List.foldl_cons]
      have h1 := ih (monitor.event U A q event)
      have h2 := calls_event_le U A q monitor event
      simp only [chargeOf, List.map_cons, List.sum_cons] at h1 ⊢
      omega
theorem calls_steps_le (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) (monitor : Monitor) :
    (steps.foldl (Monitor.step U A q published) monitor).calls ≤ monitor.calls + chargeOf (steps.flatMap TaggedStep.events) := by
  induction steps generalizing monitor with
  | nil => simp [chargeOf]
  | cons step rest ih =>
      rw [List.foldl_cons]
      have h1 := ih (monitor.step U A q published step)
      have h2 : (monitor.step U A q published step).calls ≤ monitor.calls + chargeOf step.events := by
        cases step with
        | world event =>
            have := calls_event_le U A q monitor event
            simp only [Monitor.step, TaggedStep.events, chargeOf, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil] at this ⊢
            omega
        | sign request output events =>
            simp only [Monitor.step, Monitor.sign]
            split_ifs <;> simp
      simp only [chargeOf, List.flatMap_cons, List.map_append, List.sum_append] at h1 h2 ⊢
      omega
theorem monitorRun_calls_le (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    (monitorRun U A q published steps verdict).calls ≤ chargeOf (steps.flatMap TaggedStep.events ++ verdict) := by
  unfold monitorRun
  have h1 := calls_events_le U A q verdict (steps.foldl (Monitor.step U A q published) Monitor.initial)
  have h2 := calls_steps_le U A q published steps Monitor.initial
  have h0 : Monitor.initial.calls = 0 := rfl
  simp only [chargeOf, List.map_append, List.sum_append] at h1 h2 ⊢
  omega
end ClaudeWCT.W9.T3.Security.LargeCoupling
