import SigGolfCandidate.W9Machine.WctLayout

namespace W9Machine
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M publicHash shortHash pad64 HashOutput Digest)
variable {im : Image}
theorem GoodQFor.mono {s : MachineState} {N C A N' C' A' : Nat} {Q Q' : Prop} {X : OracleComp HashSpec Obs}
    (h : GoodQFor im s N C Q A X) (hN : N ≤ N') (hC : C ≤ C') (hQ : Q → Q' ∧ A ≤ A') :
    GoodQFor im s N' C' Q' A' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  refine ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs => ?_⟩⟩
  obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs
  exact ⟨(hQ hq).1, by have := (hQ hq).2; omega⟩
theorem GoodQFor.congr {s : MachineState} {N C A : Nat} {Q : Prop} {X Y : OracleComp HashSpec Obs}
    (h : GoodQFor im s N C Q A X) (hXY : X = Y) : GoodQFor im s N C Q A Y := hXY ▸ h
theorem GoodQFor.steps {s t : MachineState} {k c N C A : Nat} {Q : Prop} {X : OracleComp HashSpec Obs}
    (hst : Steps im s k c t) (h : GoodQFor im t N C Q A X) : GoodQFor im s (N + k) (C + c) Q (A + c) X := by
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
theorem GoodQFor.steps' {s t : MachineState} {k c N C A N' C' A' : Nat} {Q Q' : Prop}
    {X : OracleComp HashSpec Obs} (hst : Steps im s k c t) (h : GoodQFor im t N C Q A X)
    (hN : N + k ≤ N') (hC : C + c ≤ C') (hQ : Q → Q' ∧ A + c ≤ A') : GoodQFor im s N' C' Q' A' X :=
  (h.steps hst).mono hN hC hQ
theorem GoodQFor.query {s : MachineState} {N C A : Nat} {Q : Prop} {q : Query}
    {K : BitVec 256 → OracleComp HashSpec Obs}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = q)
    (h : ∀ a, GoodQFor im (writeHash s a) N C Q A (K a)) :
    GoodQFor im s (N + 1) (C + 8 * q.blocks) Q (A + 8 * q.blocks)
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
theorem GoodQFor.publicHash_bind {β : Type} {s : MachineState} {N C A : Nat} {Q : Prop}
    {input : List UInt8} {f : HashOutput → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a, GoodQFor im (writeHash s a) N C Q A (ccM (f a) K)) :
    GoodQFor im s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) Q (A + 8 * (toQ (pad64 input)).blocks)
      (ccM (publicHash input >>= f) K) := by
  have := GoodQFor.query (K := fun a => ccM (f a) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_publicHash_bind]
theorem GoodQFor.shortHash_bind {β : Type} {s : MachineState} {N C A : Nat} {Q : Prop}
    {input : List UInt8} {f : Digest → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, GoodQFor im (writeHash s a) N C Q A (ccM (f (a.extractLsb' 0 128)) K)) :
    GoodQFor im s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) Q (A + 8 * (toQ (pad64 input)).blocks)
      (ccM (shortHash input >>= f) K) := by
  have := GoodQFor.query (K := fun a => ccM (f (a.extractLsb' 0 128)) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_shortHash_bind]
theorem GoodQFor.halt {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch im s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (hQ : s.getReg .x10 = 0 → Q ∧ 1 ≤ A) :
    GoodQFor im s 1 1 Q A (pure (decide (s.getReg .x10 = 0), 0)) := by
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
theorem GoodQFor.reject {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch im s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) : GoodQFor im s 1 1 Q A (pure (false, 0)) := by
  have := GoodQFor.halt (Q := Q) (A := A) hf h5 (fun h => absurd (h10.symm.trans h) (by decide))
  rwa [h10] at this
theorem GoodQFor.accept {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch im s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 0) (hQ : Q) (hA : 1 ≤ A) :
    GoodQFor im s 1 1 Q A (pure (true, 0)) := by
  have := GoodQFor.halt (Q := Q) (A := A) hf h5 (fun _ => ⟨hQ, hA⟩)
  rwa [h10] at this
end W9Machine
