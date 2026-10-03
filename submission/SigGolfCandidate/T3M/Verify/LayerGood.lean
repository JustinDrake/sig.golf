import SigGolfCandidate.T3M.Verify.Nonbinary.LayerTop

/-! All four layers compose the checked lower and mixed-radix top verifiers. -/
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 shortHash leafHash)

/-- **One layer** (`layer_good`): `layerHead` from `LayerIn` to `LeafOut`, fuel `layerFuel lay`, at most
`layerCost lay 0` cycles on every path. -/
theorem layer_good (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (M : T3.LayerMessage)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCost lay.val 0)
      (ccM (layerHead w index lay M R) K) := by
  by_cases h0 : lay = 0
  · subst h0
    exact layer_good_top w pk index M s hs R K hK0 N C A Q hR
  · exact layer_good_low w pk index lay h0 M s hs R K hK0 N C A Q hR

/-- **W's layer loop, the top layer** (`layersP w index 1 M`): the continuation from `LeafOut` = the leaf pk,
`merkleP` (to the root) and the compare. -/
theorem layersP_good_top (w : WBytes) (pk : Digest) (index : Nat) (M : T3.LayerMessage) (s : MachineState)
    (hs : LayerIn w pk index 0 M s) (K : Option Digest → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0))
    (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index (Fin.ofNat 4 0) ends u →
      GoodQ u N C Q A (ccM (leafHash (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 (route index (Fin.ofNat 4 0)).1
        ends >>= merkleP w index (Fin.ofNat 4 0) >>= fun v => layersP w index 0 (v, 0, 0)) K)) :
    GoodQ s (N + layerFuel 0) (C + layerCost 0 0) Q (A + layerCost 0 0) (ccM (layersP w index (0 + 1) M) K) := by
  rw [layersP_succ_top]
  exact layer_good w pk index (Fin.ofNat 4 0) M s hs _ K hK0 N C A Q hR

/-- **W's layer loop, a lower layer** (`layersP w index (n + 1) M`, `0 < n < 4`): the continuation from `LeafOut` =
the leaf pk, `merklePairP` (E8: the root's children) and the layers below. -/
theorem layersP_good_low (w : WBytes) (pk : Digest) (index n : Nat) (hn : n < 4) (hn0 : n ≠ 0) (M : T3.LayerMessage)
    (s : MachineState) (hs : LayerIn w pk index n M s) (K : Option Digest → OracleComp HashSpec Obs)
    (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index (Fin.ofNat 4 n) ends u →
      GoodQ u N C Q A (ccM (leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
        ends >>= merklePairP w index (Fin.ofNat 4 n) >>= layersP w index n) K)) :
    GoodQ s (N + layerFuel n) (C + layerCost n 0) Q (A + layerCost n 0) (ccM (layersP w index (n + 1) M) K) := by
  have hv : (Fin.ofNat 4 n : Layer).val = n := by simp [Fin.val_ofNat, Nat.mod_eq_of_lt hn]
  rw [layersP_succ_low w index n hn0]
  have := layer_good w pk index (Fin.ofNat 4 n) M s (by rw [hv]; exact hs) _ K hK0 N C A Q hR
  rwa [hv] at this

end SigGolfCandidate.T3M
