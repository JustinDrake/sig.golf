import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildDefs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Routine
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

section

namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
theorem leafBytes_canon (k index j : Nat) (ends : List Digest) (h : ends.length = 7) :
    leafBytes (leafFields k index j ends) =
      bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (ClaudeWCT.WCT9.wctHeader 6 k index 0 j) ++
        (ends.drop 1).flatMap (bytesLE 16) := by
  match ends, h with
  | [e0, e1, e2, e3, e4, e5, e6], _ =>
    simp only [leafBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.flatMap_cons,
      List.flatMap_nil, leafFields, List.drop_succ_cons, List.drop_zero, List.append_nil, List.append_assoc]
    rfl
theorem childCanon (k index j : Nat) (ends : List Digest) (sibs : Nat → Digest) (h : ends.length = 7) :
    childProgC k index j (leafFields k index j ends) sibs =
      (ClaudeWCT.WCT9.leafHash index k j ends >>= sixLevels k index j sibs >>= fun top =>
        pure (pairOf j top (sibs 6))) := by
  unfold childProgC ClaudeWCT.WCT9.leafHash sixLevels
  rw [leafBytes_canon k index j ends h, bind_assoc]
  rfl
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
theorem sixFolds (k index j : Nat) (path : Fin 7 → Digest) (root : Digest) :
    (List.finRange 6).foldlM (fun value (level : Fin 6) => do
      let other := path level.castSucc
      let pair := if j / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
      ClaudeWCT.WCT9.wctNodeHash k index (2 ^ (6 - level.val) + j / 2 ^ (level.val + 1)) pair.1 pair.2) root =
    sixLevels k index j (finPath path) root := by
  let F : Digest → Nat → M Digest := fun value l =>
    let other := finPath path l
    let pair := if j / 2 ^ l % 2 = 0 then (value, other) else (other, value)
    ClaudeWCT.WCT9.wctNodeHash k index (2 ^ (6 - l) + j / 2 ^ (l + 1)) pair.1 pair.2
  have hf : (fun value (level : Fin 6) ↦ do
      let other := path level.castSucc
      let pair := if j / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
      ClaudeWCT.WCT9.wctNodeHash k index (2 ^ (6 - level.val) + j / 2 ^ (level.val + 1)) pair.1 pair.2 :
        Digest → Fin 6 → M Digest) = fun value level => F value level.val := by
    funext value level
    simp only [F, finPath, dif_pos (show level.val < 7 by omega)]
    rfl
  rw [hf, show List.foldlM (fun value (level : Fin 6) => F value level.val) root (List.finRange 6) =
      List.foldlM F root ((List.finRange 6).map Fin.val) by rw [List.foldlM_map], finRange_map_val]
  rfl
end ClaudeWCT.W9.Machine.Merkle
end

section



set_option maxRecDepth 4000
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
theorem codewordL_eq (r : Fin 728) (i : Fin 7) : WCT9.digit r i = (codewordL r.val).getD i.val 0 := by
  unfold WCT9.digit WCT9.codeword codewordL
  rw [List.getD_eq_getElem (l := WCT9.compositions 4 7 6) (d := []) (by rw [WCT9.codebook_card]; exact r.isLt)]
theorem mapM_finRange_eq {β : Type} (f : Fin 7 → M β) (g : Nat → M β) (h : ∀ i : Fin 7, f i = g i.val) :
    (List.finRange 7).mapM f = (List.range' 0 7).mapM g := by
  have : f = g ∘ Fin.val := funext h
  rw [this, ← List.mapM_map, Merkle.finRange_map_val, List.range_eq_range']
theorem recoverCoordinate_split (sig : WCT9.Signature) (index : Nat) (N : HashOutput) (k : WCT9.Coord) :
    WCT9.recoverCoordinate sig index N k =
      (chainsFrom index k.val (WCT9.child N k).val (codewordL (WCT9.rank N k).val)
          (fun t => if h : t < 7 then (sig.openings k).values ⟨t, h⟩ else 0) 0 >>= fun ends =>
        (WCT9.leafHash index k.val (WCT9.child N k).val ends >>=
          Merkle.sixLevels k.val index (WCT9.child N k).val (Merkle.finPath (sig.openings k).path)) >>= fun top =>
        pure (Merkle.pairOf (WCT9.child N k).val top ((sig.openings k).path 6))) := by
  unfold WCT9.recoverCoordinate
  simp only
  have hm := mapM_finRange_eq (fun i => WCT9.chain index k.val (WCT9.child N k).val i.val
      (3 - WCT9.digit (WCT9.rank N k) i) (WCT9.digit (WCT9.rank N k) i) ((sig.openings k).values i))
    (fun i => WCT9.chain index k.val (WCT9.child N k).val i (3 - (codewordL (WCT9.rank N k).val).getD i 0)
      ((codewordL (WCT9.rank N k).val).getD i 0) (if h : i < 7 then (sig.openings k).values ⟨i, h⟩ else 0))
    (fun i => by simp only [codewordL_eq, dif_pos i.isLt])
  unfold chainsFrom
  rw [show 7 - 0 = 7 from rfl, ← hm]
  refine bind_congr fun ends => ?_
  rw [bind_assoc]
  refine bind_congr fun root => ?_
  rw [Merkle.sixFolds]
  rfl
end ClaudeWCT.W9.Machine.Expand
end
