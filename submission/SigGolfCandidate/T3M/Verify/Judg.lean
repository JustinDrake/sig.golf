import SigGolfCandidate.T3M.Verify.Code
import SigGolfCandidate.T3M.Sim

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M publicHash shortHash pad64 HashOutput Digest)
abbrev Obs := Bool × Nat
def obs (e : Execution) : Obs := (decide (e.exit = .success), e.hashCalls)
def Good (s : MachineState) (N C : Nat) (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F image s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F image s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ C
@[simp] theorem obs_charge (e : Execution) (c b : Nat) :
    obs (e.charge c 0 b) = obs e := by
  cases e; simp [obs, Execution.charge]
theorem obs_charge1 (e : Execution) (c b : Nat) :
    obs (e.charge c 1 b) = ((obs e).1, 1 + (obs e).2) := by
  cases e; rfl
theorem Good.mono {s : MachineState} {N C N' C' : Nat} {X : OracleComp HashSpec Obs}
    (h : Good s N C X) (hN : N ≤ N') (hC : C ≤ C') : Good s N' C' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  exact ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2; omega⟩⟩
theorem Good.congr {s : MachineState} {N C : Nat} {X Y : OracleComp HashSpec Obs}
    (h : Good s N C X) (hXY : X = Y) : Good s N C Y := hXY ▸ h
theorem Good.steps {s t : MachineState} {k c N C : Nat} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : Good t N C X) : Good s (N + k) (C + c) X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h (F - k) (by omega)
  have hF' : F = (F - k) + k := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hst.execute_le (by omega : k ≤ F), Functor.map_map]
    simp only [obs_charge]
    exact h1
  · rw [hF', hst.evalWith hash (F - k)]
    simp only [Execution.charge_exit, Execution.charge_cycles]
    exact ⟨(h2 hash).1, by have := (h2 hash).2; omega⟩
theorem Good.steps' {s t : MachineState} {k c N C N' C' : Nat} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : Good t N C X) (hN : N + k ≤ N') (hC : C + c ≤ C') :
    Good s N' C' X := (h.steps hst).mono hN hC
def cc {α : Type} (oa : OracleComp HashSpec α) (K : α → OracleComp HashSpec Obs) :
    OracleComp HashSpec Obs :=
  countCalls oa >>= fun p => (fun q => (q.1, p.2 + q.2)) <$> K p.1
@[simp] theorem cc_pure {α : Type} (a : α) (K : α → OracleComp HashSpec Obs) :
    cc (pure a) K = K a := by
  simp only [cc, countCalls, countWith_pure, pure_bind, Nat.zero_add]
  exact id_map' _
theorem cc_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β)
    (K : β → OracleComp HashSpec Obs) : cc (oa >>= f) K = cc oa (fun a => cc (f a) K) := by
  simp only [cc, countCalls_bind, bind_assoc, map_bind, Functor.map_map, bind_map_left]
  congr 1; funext p; congr 1; funext r
  simp only [Nat.add_assoc]
theorem cc_map {α β : Type} (f : α → β) (oa : OracleComp HashSpec α)
    (K : β → OracleComp HashSpec Obs) : cc (f <$> oa) K = cc oa (fun a => K (f a)) := by
  rw [map_eq_bind_pure_comp, cc_bind]
  simp only [Function.comp, cc_pure]
theorem cc_query (q : Query) (K : BitVec 256 → OracleComp HashSpec Obs) :
    cc (liftM (HashSpec.query q) : OracleComp HashSpec _) K = (do
      let a ← (liftM (HashSpec.query q) : OracleComp HashSpec _)
      (fun r => (r.1, 1 + r.2)) <$> K a) := by
  simp only [cc, countCalls_query, bind_map_left]
def Kb : Bool → OracleComp HashSpec Obs := fun b => pure (b, 0)
theorem cc_Kb (oa : OracleComp HashSpec Bool) : cc oa Kb = countCalls oa := by
  simp only [cc, Kb, map_pure, Nat.add_zero]
  exact bind_pure _
def ccM {α : Type} (p : M α) (K : α → OracleComp HashSpec Obs) : OracleComp HashSpec Obs :=
  cc (mrealize 0 p) K
@[simp] theorem ccM_pure {α : Type} (a : α) (K : α → OracleComp HashSpec Obs) :
    ccM (pure a : M α) K = K a := by
  simp only [ccM, mrealize_pure, cc_pure]
theorem ccM_bind {α β : Type} (p : M α) (f : α → M β) (K : β → OracleComp HashSpec Obs) :
    ccM (p >>= f) K = ccM p (fun a => ccM (f a) K) := by
  simp only [ccM, mrealize_bind, cc_bind]
theorem ccM_map {α β : Type} (f : α → β) (p : M α) (K : β → OracleComp HashSpec Obs) :
    ccM (f <$> p) K = ccM p (fun a => K (f a)) := by
  simp only [ccM, mrealize_map, cc_map]
theorem ccM_ite {α : Type} (c : Prop) [Decidable c] (p q : M α) (K : α → OracleComp HashSpec Obs) :
    ccM (if c then p else q) K = if c then ccM p K else ccM q K := by
  split <;> rfl
theorem ccM_Kb (p : M Bool) : ccM p Kb = countCalls (mrealize 0 p) := cc_Kb _
theorem ccM_publicHash_bind {β : Type} (input : List UInt8) (f : HashOutput → M β)
    (K : β → OracleComp HashSpec Obs) :
    ccM (publicHash input >>= f) K = (do
      let a ← (liftM (HashSpec.query (toQ (pad64 input))) : OracleComp HashSpec _)
      (fun r => (r.1, 1 + r.2)) <$> ccM (f a) K) := by
  rw [ccM_bind]
  simp only [ccM, mrealize_publicHash, cc_query]
theorem ccM_shortHash_bind {β : Type} (input : List UInt8) (f : Digest → M β)
    (K : β → OracleComp HashSpec Obs) :
    ccM (shortHash input >>= f) K = (do
      let a ← (liftM (HashSpec.query (toQ (pad64 input))) : OracleComp HashSpec _)
      (fun r => (r.1, 1 + r.2)) <$> ccM (f (a.extractLsb' 0 128)) K) := by
  have : shortHash input >>= f = publicHash input >>= fun a => f (a.extractLsb' 0 128) := by
    unfold shortHash; rw [bind_assoc]; simp only [pure_bind]
  rw [this, ccM_publicHash_bind]
theorem Good.query {s : MachineState} {N C : Nat} {q : Query}
    {K : BitVec 256 → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = q)
    (h : ∀ a, Good (writeHash s a) N C (K a)) :
    Good s (N + 1) (C + 8 * q.blocks) (cc (liftM (HashSpec.query q) : OracleComp HashSpec _) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_query, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2⟩ := (h (hash q) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    exact ⟨h1, by omega⟩
theorem Good.publicHash_bind {β : Type} {s : MachineState} {N C : Nat} {input : List UInt8}
    {f : HashOutput → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a, Good (writeHash s a) N C (ccM (f a) K)) :
    Good s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) (ccM (publicHash input >>= f) K) := by
  have := Good.query (K := fun a => ccM (f a) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_publicHash_bind]
theorem Good.shortHash_bind {β : Type} {s : MachineState} {N C : Nat} {input : List UInt8}
    {f : Digest → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, Good (writeHash s a) N C (ccM (f (a.extractLsb' 0 128)) K)) :
    Good s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) (ccM (shortHash input >>= f) K) := by
  have := Good.query (K := fun a => ccM (f (a.extractLsb' 0 128)) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_shortHash_bind]
theorem Good.halt {s : MachineState} (hf : fetch image s = some (.base .ECALL))
    (ht0 : s.getReg .x5 = 1) : Good s 1 1 (pure (decide (s.getReg .x10 = 0), 0)) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_halt (F - 1) hf ht0, map_pure]
    by_cases hx : s.getReg .x10 = 0
    · simp only [obs, hx, if_true]
    · simp only [obs, hx, if_false]; rfl
  · rw [hF', evalWith_halt hash (F - 1) hf ht0]
    refine ⟨?_, le_refl _⟩
    by_cases hx : s.getReg .x10 = 0
    · simp only [hx, if_true]; decide
    · simp only [hx, if_false]; decide
def GoodQ (s : MachineState) (N C : Nat) (Q : Prop) (A : Nat) (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F image s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F image s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ C ∧
      ((evalWithAnswerFn hash (Riscv.execute F image s)).exit = .success →
        Q ∧ (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ A)
theorem Good.toQ {s : MachineState} {N C : Nat} {X : OracleComp HashSpec Obs} (h : Good s N C X) :
    GoodQ s N C True C X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F hF
  exact ⟨h1, fun hash => ⟨(h2 hash).1, (h2 hash).2, fun _ => ⟨trivial, (h2 hash).2⟩⟩⟩
theorem GoodQ.toGood {s : MachineState} {N C : Nat} {Q : Prop} {A : Nat} {X : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) : Good s N C X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F hF
  exact ⟨h1, fun hash => ⟨(h2 hash).1, (h2 hash).2.1⟩⟩
theorem GoodQ.mono {s : MachineState} {N C A N' C' A' : Nat} {Q Q' : Prop} {X : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) (hN : N ≤ N') (hC : C ≤ C') (hQ : Q → Q' ∧ A ≤ A') :
    GoodQ s N' C' Q' A' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  refine ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs => ?_⟩⟩
  obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs
  exact ⟨(hQ hq).1, by have := (hQ hq).2; omega⟩
theorem GoodQ.congr {s : MachineState} {N C A : Nat} {Q : Prop} {X Y : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) (hXY : X = Y) : GoodQ s N C Q A Y := hXY ▸ h
theorem GoodQ.steps {s t : MachineState} {k c N C A : Nat} {Q : Prop} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : GoodQ t N C Q A X) : GoodQ s (N + k) (C + c) Q (A + c) X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h (F - k) (by omega)
  have hF' : F = (F - k) + k := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hst.execute_le (by omega : k ≤ F), Functor.map_map]
    simp only [obs_charge]
    exact h1
  · rw [hF', hst.evalWith hash (F - k)]
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs
    exact ⟨hq, by omega⟩
theorem GoodQ.steps' {s t : MachineState} {k c N C A N' C' A' : Nat} {Q Q' : Prop}
    {X : OracleComp HashSpec Obs} (hst : Steps image s k c t) (h : GoodQ t N C Q A X)
    (hN : N + k ≤ N') (hC : C + c ≤ C') (hQ : Q → Q' ∧ A + c ≤ A') : GoodQ s N' C' Q' A' X :=
  (h.steps hst).mono hN hC hQ
theorem GoodQ.query {s : MachineState} {N C A : Nat} {Q : Prop} {q : Query}
    {K : BitVec 256 → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = q)
    (h : ∀ a, GoodQ (writeHash s a) N C Q A (K a)) :
    GoodQ s (N + 1) (C + 8 * q.blocks) Q (A + 8 * q.blocks)
      (cc (liftM (HashSpec.query q) : OracleComp HashSpec _) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_query, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2, h3⟩ := (h (hash q) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨h1, by omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := h3 hs
    exact ⟨hq, by omega⟩
theorem GoodQ.publicHash_bind {β : Type} {s : MachineState} {N C A : Nat} {Q : Prop}
    {input : List UInt8} {f : HashOutput → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a, GoodQ (writeHash s a) N C Q A (ccM (f a) K)) :
    GoodQ s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) Q (A + 8 * (toQ (pad64 input)).blocks)
      (ccM (publicHash input >>= f) K) := by
  have := GoodQ.query (K := fun a => ccM (f a) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_publicHash_bind]
theorem GoodQ.shortHash_bind {β : Type} {s : MachineState} {N C A : Nat} {Q : Prop}
    {input : List UInt8} {f : Digest → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, GoodQ (writeHash s a) N C Q A (ccM (f (a.extractLsb' 0 128)) K)) :
    GoodQ s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) Q (A + 8 * (toQ (pad64 input)).blocks)
      (ccM (shortHash input >>= f) K) := by
  have := GoodQ.query (K := fun a => ccM (f (a.extractLsb' 0 128)) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_shortHash_bind]
theorem GoodQ.halt {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (hQ : s.getReg .x10 = 0 → Q ∧ 1 ≤ A) :
    GoodQ s 1 1 Q A (pure (decide (s.getReg .x10 = 0), 0)) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_halt (F - 1) hf h5, map_pure]
    by_cases hx : s.getReg .x10 = 0
    · simp only [obs, hx, if_true]
    · simp only [obs, hx, if_false]; rfl
  · rw [hF', evalWith_halt hash (F - 1) hf h5]
    by_cases hx : s.getReg .x10 = 0
    · simp only [hx, if_true]
      exact ⟨by decide, le_refl _, fun _ => hQ hx⟩
    · simp only [hx, if_false]
      exact ⟨by decide, le_refl _, fun h => absurd h (by decide)⟩
theorem GoodQ.reject {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) : GoodQ s 1 1 Q A (pure (false, 0)) := by
  have := GoodQ.halt (Q := Q) (A := A) hf h5 (fun h => absurd (h10.symm.trans h) (by decide))
  rwa [h10] at this
theorem GoodQ.accept {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 0) (hQ : Q) (hA : 1 ≤ A) :
    GoodQ s 1 1 Q A (pure (true, 0)) := by
  have := GoodQ.halt (Q := Q) (A := A) hf h5 (fun _ => ⟨hQ, hA⟩)
  rwa [h10] at this
end SigGolfCandidate.T3M.Verify
