import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.T3M.Mem

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range' 0 n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
section tb
variable {image : Image} {sk : BitVec 256}
theorem tb_shortHash_bind' {β : Type} {s : MachineState} {input : List UInt8} {W : Nat}
    {f : T3.Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this
theorem tb_map {α β : Type} {s : MachineState} {W : Nat} {p : T3.M α} (f : α → β) {Q : β → MachineState → Prop}
    (h : TBSim image sk s W p (fun a t => Q (f a) t)) : TBSim image sk s W (f <$> p) Q := by
  rw [map_eq_bind_pure_comp]
  exact (TBSim.bind (W₂ := 0) h (fun a t ht => TBSim.pure ht)).mono (by omega) (fun _ _ h => h)
theorem tb_mapM_idx {γ δ : Type} (f : γ → T3.M δ) (idx : γ → Nat) (W : Nat) (Inv : List δ → MachineState → Prop) :
    ∀ (xs : List γ) (pre : List δ) {s : MachineState}, xs.map idx = List.range' pre.length xs.length →
    (∀ x ∈ xs, ∀ (pre' : List δ) t, pre'.length = idx x → Inv pre' t →
      TBSim image sk t W (f x) (fun d u => Inv (pre' ++ [d]) u)) →
    Inv pre s → TBSim image sk s (xs.length * W) (xs.mapM f) (fun ds u => ds.length = xs.length ∧ Inv (pre ++ ds) u)
  | [], pre, s, _, _, h0 => by
    simpa using TBSim.pure (image := image) (sk := sk) (Q := fun ds u => ds.length = 0 ∧ Inv (pre ++ ds) u)
      (a := []) (by simpa using h0)
  | x :: xs, pre, s, hidx, hb, h0 => by
    rw [List.mapM_cons]
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
    have h1 := hb x (by simp) pre s hidx.1.symm h0
    have key : ∀ d t, Inv (pre ++ [d]) t → TBSim image sk t (xs.length * W)
        (do let ds ← xs.mapM f; Pure.pure (d :: ds)) (fun ds u => ds.length = xs.length + 1 ∧ Inv (pre ++ ds) u) := by
      intro d t ht
      have h2 := tb_mapM_idx f idx W Inv xs (pre ++ [d]) (by simpa using hidx.2) (fun y hy => hb y (by simp [hy])) ht
      exact (TBSim.bind (W₂ := 0) h2 (f := fun ds => Pure.pure (d :: ds))
        (fun ds u hu => TBSim.pure ⟨by simp [hu.1], by simpa using hu.2⟩)).mono (by omega) (fun _ _ h => h)
    exact (TBSim.bind h1 key).mono (by rw [List.length_cons, Nat.succ_mul]; omega) (fun _ _ h => h)
theorem tb_mapM_finRange {δ : Type} (n : Nat) (f : Fin n → T3.M δ) (W : Nat) (Inv : List δ → MachineState → Prop)
    (hbody : ∀ (i : Fin n) (pre : List δ) t, pre.length = i.val → Inv pre t →
      TBSim image sk t W (f i) (fun d u => Inv (pre ++ [d]) u)) {s : MachineState} (h0 : Inv [] s) :
    TBSim image sk s (n * W) ((List.finRange n).mapM f) (fun ds u => ds.length = n ∧ Inv ds u) := by
  have := tb_mapM_idx f Fin.val W Inv (List.finRange n) [] (by rw [finRange_map_val]; simp)
    (fun x _ pre' t h1 h2 => hbody x pre' t h1 h2) h0
  simpa using this
theorem tb_foldlM_finRange {γ : Type} (n : Nat) (f : γ → Fin n → T3.M γ) (init : γ) (W : Nat)
    (Inv : Nat → γ → MachineState → Prop)
    (hbody : ∀ (i : Fin n) acc t, Inv i.val acc t → TBSim image sk t W (f acc i) (Inv (i.val + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    TBSim image sk s (n * W) ((List.finRange n).foldlM f init) (Inv n) := by
  have gen : ∀ (xs : List (Fin n)) (k : Nat) (acc : γ) (t : MachineState), xs.map Fin.val = List.range' k xs.length →
      Inv k acc t → TBSim image sk t (xs.length * W) (xs.foldlM f acc) (Inv (k + xs.length)) := by
    intro xs
    induction xs with
    | nil => intro k acc t _ ht; simpa using TBSim.pure (image := image) (sk := sk) ht
    | cons x xs ih =>
      intro k acc t hidx ht
      simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
      rw [List.foldlM_cons]
      have h1 := hbody x acc t (by rw [hidx.1]; exact ht)
      rw [hidx.1] at h1
      refine (TBSim.bind (W₂ := xs.length * W) h1 (fun acc' t' ht' => ?_)).mono
        (by rw [List.length_cons, Nat.succ_mul]; omega) (fun _ _ h => by
        simpa [Nat.add_assoc, Nat.add_comm 1] using h)
      have := ih (k + 1) acc' t' (by simpa using hidx.2) ht'
      rwa [show k + 1 + xs.length = k + (xs.length + 1) by omega] at this
  have := gen (List.finRange n) 0 init s (by rw [finRange_map_val]; simp) h0
  simpa using this
end tb
end SigGolfCandidate.T3M.Expand
