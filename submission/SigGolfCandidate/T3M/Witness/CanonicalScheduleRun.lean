import SigGolfCandidate.T3M.Witness.Skeleton
import SigGolfCandidate.T3M.Witness.CanonicalAdapterGeneral

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalSchedule
open OracleComp OracleSpec SigGolfCandidate.T3

def segmentDigestP (w : WBytes) (index coord ptr A E : Nat) (node : Digest) (pend : Pending) : M Digest := do
  let n ← pendingHash w index coord node pend
  let r ← foldsP w index coord ptr A n E
  pure r.1

theorem stop_fixed (w : WBytes) (index coord : Nat) (stack : List (Digest × Nat))
    (pending : Pending) (E ptr A : Nat) (node : Digest)
    (h : HdrOk (wbyte w ptr).toNat A 0 E) :
    segLoop w index coord stack pending E ptr node =
      (fun v => some (v,E/2^A,segNext ptr A,stack)) <$>
        segmentDigestP w index coord ptr A E node pending := by
  rw [segLoop_stop w index coord stack pending E ptr A node h]
  simp only [segmentDigestP,map_bind,map_pure]
  apply bind_congr
  intro n
  apply bind_congr_of_forall_mem_support
  intro p hp
  rw [foldsP_support w index coord ptr A n E p hp]

theorem merge_fixed (w : WBytes) (index coord : Nat) (pnode : Digest) (Q : Nat)
    (rest : List (Digest × Nat)) (pending : Pending) (E ptr A : Nat) (node : Digest)
    (h : HdrOk (wbyte w ptr).toNat A 1 E) (hQ : Q=E/2^A) :
    segLoop w index coord ((pnode,Q)::rest) pending E ptr node =
      (segmentDigestP w index coord ptr A E node pending >>= fun v =>
        segLoop w index coord rest (.merge (E/2^A/2) pnode) (E/2^A/2) (segNext ptr A) v) := by
  rw [segLoop_merge w index coord pnode Q rest pending E ptr A node h]
  simp only [segmentDigestP,bind_assoc,pure_bind]
  apply bind_congr
  intro n
  apply bind_congr_of_forall_mem_support
  intro p hp
  rw [foldsP_support w index coord ptr A n E p hp,if_neg (by omega)]

def coordProgram (w : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat) : M (Digest × Nat) := do
  let g0 := selLeaf sel 0
  let g1 := selLeaf sel 1
  let g2 := selLeaf sel 2
  let x := lcaLevel g0 g1
  let y := lcaLevel g1 g2
  let p1 := segNext ptr (x-1)
  if x<y then
    let p2 := segNext p1 (x-1)
    let p3 := segNext p2 (y-1-x)
    let p4 := segNext p3 (y-1)
    let n0 ← segmentDigestP w index coord ptr (x-1) (2048+g0) 0 (.leaf (3*coord) g0)
    let n1 ← segmentDigestP w index coord p1 (x-1) (2048+g1) n0 (.leaf (3*coord+1) g1)
    let n2 ← segmentDigestP w index coord p2 (y-1-x) ((2048+g1)/2^x) n1
      (.merge ((2048+g1)/2^x) n0)
    let n3 ← segmentDigestP w index coord p3 (y-1) (2048+g2) n2 (.leaf (3*coord+2) g2)
    let n4 ← segmentDigestP w index coord p4 (11-y) ((2048+g2)/2^y) n3
      (.merge ((2048+g2)/2^y) n2)
    pure (n4,segNext p4 (11-y))
  else
    let p2 := segNext p1 (y-1)
    let p3 := segNext p2 (y-1)
    let p4 := segNext p3 (x-1-y)
    let n0 ← segmentDigestP w index coord ptr (x-1) (2048+g0) 0 (.leaf (3*coord) g0)
    let n1 ← segmentDigestP w index coord p1 (y-1) (2048+g1) n0 (.leaf (3*coord+1) g1)
    let n2 ← segmentDigestP w index coord p2 (y-1) (2048+g2) n1 (.leaf (3*coord+2) g2)
    let n3 ← segmentDigestP w index coord p3 (x-1-y) ((2048+g2)/2^y) n2
      (.merge ((2048+g2)/2^y) n1)
    let n4 ← segmentDigestP w index coord p4 (11-x) ((2048+g2)/2^x) n3
      (.merge ((2048+g2)/2^x) n0)
    pure (n4,segNext p4 (11-x))

def HeadersMatch (w : WBytes) : Nat → List Segment → Prop
  | _,[] => True
  | ptr,s::rest => s.Matches (wbyte w ptr).toNat ∧ HeadersMatch w (segNext ptr s.a) rest

theorem coord_program_exact (w : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat)
    (hb : sel.bucket<16) (h2 : sel.leaves.getD 2 0<128)
    (h01 : sel.leaves.getD 0 0<sel.leaves.getD 1 0)
    (h12 : sel.leaves.getD 1 0<sel.leaves.getD 2 0)
    (hok : HeadersMatch w ptr (coordSchedule coord sel)) :
    ftsCoordP w index coord sel ptr=some <$> coordProgram w index coord sel ptr := by
  unfold ftsCoordP coordProgram
  unfold coordSchedule at hok
  dsimp only at hok ⊢
  have g01 : selLeaf sel 0<selLeaf sel 1 := by unfold selLeaf; omega
  have g12 : selLeaf sel 1<selLeaf sel 2 := by unfold selLeaf; omega
  have g2l : selLeaf sel 2<2048 := by unfold selLeaf; omega
  have bk0 := bucket_div_eight (b:=sel.bucket) (x:=sel.leaves.getD 0 0) (by omega)
  have bk1 := bucket_div_eight (b:=sel.bucket) (x:=sel.leaves.getD 1 0) (by omega)
  have bk2 := bucket_div_eight (b:=sel.bucket) (x:=sel.leaves.getD 2 0) (by omega)
  change selLeaf sel 0/2^7=sel.bucket at bk0
  change selLeaf sel 1/2^7=sel.bucket at bk1
  change selLeaf sel 2/2^7=sel.bucket at bk2
  generalize selLeaf sel 0=g0 at *
  generalize selLeaf sel 1=g1 at *
  generalize selLeaf sel 2=g2 at *
  have px := lcaLevel_pos g0 g1
  have py := lcaLevel_pos g1 g2
  have lx : lcaLevel g0 g1 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk0,bk1])
  have ly : lcaLevel g1 g2 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk1,bk2])
  have l02 := lca_outer g01 g12
  have hne := lca_ne g01 g12
  generalize hd01 : lcaLevel g0 g1=x at *
  generalize hd12 : lcaLevel g1 g2=y at *
  by_cases hA : x<y
  · simp only [if_pos hA,HeadersMatch] at hok
    obtain ⟨m0,m1,m2,m3,m4,-⟩ := hok
    have H0 := hdrOk_of_matches m0 (by dsimp only; omega)
    have H1 := hdrOk_of_matches m1 (by dsimp only; omega)
    have H2 := hdrOk_of_matches m2 (by dsimp only; omega)
    have H3 := hdrOk_of_matches m3 (by dsimp only; omega)
    have H4 := hdrOk_of_matches m4 (by dsimp only; omega)
    simp only [Bool.false_eq_true,if_false,if_true] at H0 H1 H2 H3 H4
    simp only [Nat.pow_zero,Nat.div_one,Nat.add_zero] at H0 H1 H3
    rw [if_pos hA,stop_fixed w index coord [] _ _ _ _ _ H0]
    simp only [map_bind,bind_map_left,bind_assoc]
    congr 1; funext n0
    have hq1 : ((2048+g0)/2^(x-1)) ^^^ 1=(2048+g1)/2^(x-1) :=
      heap_sib (by omega) (by omega) (by omega)
    rw [merge_fixed w index coord n0 _ [] _ _ _ _ _ H1 hq1]
    simp only [bind_assoc]
    congr 1; funext n1
    have hx : (2048+g1)/2^(x-1)/2=(2048+g1)/2^x := by
      rw [Nat.div_div_eq_div_mul,← pow_succ]; congr 2; omega
    rw [hx,stop_fixed w index coord [] _ _ _ _ _ H2]
    simp only [map_bind,bind_map_left,bind_assoc]
    congr 1; funext n2
    have hyx : (2048+g1)/2^x/2^(y-1-x)=(2048+g1)/2^(y-1) := by
      rw [Nat.div_div_eq_div_mul,← pow_add]; congr 2; omega
    have hq3 : ((2048+g1)/2^x/2^(y-1-x)) ^^^ 1=(2048+g2)/2^(y-1) := by
      rw [hyx]; exact heap_sib (by omega) (by omega) (by omega)
    rw [merge_fixed w index coord n2 _ [] _ _ _ _ _ H3 hq3]
    simp only [bind_assoc]
    congr 1; funext n3
    have hy : (2048+g2)/2^(y-1)/2=(2048+g2)/2^y := by
      rw [Nat.div_div_eq_div_mul,← pow_succ]; congr 2; omega
    rw [hy,stop_fixed w index coord [] _ _ _ _ _ H4]
    simp only [map_bind,bind_map_left,bind_assoc]
    congr 1; funext n4
    have hr : (2048+g2)/2^y/2^(11-y)=1 := by
      rw [Nat.div_div_eq_div_mul,← pow_add,show y+(11-y)=11 by omega]; omega
    simp [hr]
  · simp only [if_neg hA,HeadersMatch] at hok
    obtain ⟨m0,m1,m2,m3,m4,-⟩ := hok
    have H0 := hdrOk_of_matches m0 (by dsimp only; omega)
    have H1 := hdrOk_of_matches m1 (by dsimp only; omega)
    have H2 := hdrOk_of_matches m2 (by dsimp only; omega)
    have H3 := hdrOk_of_matches m3 (by dsimp only; omega)
    have H4 := hdrOk_of_matches m4 (by dsimp only; omega)
    simp only [Bool.false_eq_true,if_false,if_true] at H0 H1 H2 H3 H4
    simp only [Nat.pow_zero,Nat.div_one,Nat.add_zero] at H0 H1 H2
    rw [if_neg hA,stop_fixed w index coord [] _ _ _ _ _ H0]
    simp only [map_bind,bind_map_left,bind_assoc]
    congr 1; funext n0
    rw [stop_fixed w index coord _ _ _ _ _ _ H1]
    simp only [map_bind,bind_map_left,bind_assoc]
    congr 1; funext n1
    have hq2 : ((2048+g1)/2^(y-1)) ^^^ 1=(2048+g2)/2^(y-1) :=
      heap_sib (by omega) (by omega) (by omega)
    rw [merge_fixed w index coord n1 _ _ _ _ _ _ _ H2 hq2]
    simp only [bind_assoc]
    congr 1; funext n2
    have hy : (2048+g2)/2^(y-1)/2=(2048+g2)/2^y := by
      rw [Nat.div_div_eq_div_mul,← pow_succ]; congr 2; omega
    rw [hy]
    have hyx : (2048+g2)/2^y/2^(x-1-y)=(2048+g2)/2^(x-1) := by
      rw [Nat.div_div_eq_div_mul,← pow_add]; congr 2; omega
    have hq3 : ((2048+g0)/2^(x-1)) ^^^ 1=(2048+g2)/2^y/2^(x-1-y) := by
      rw [hyx]; exact heap_sib (by omega) (by omega) (by rw [l02]; omega)
    rw [merge_fixed w index coord n0 _ [] _ _ _ _ _ H3 hq3]
    simp only [bind_assoc]
    congr 1; funext n3
    have hx : (2048+g2)/2^y/2^(x-1-y)/2=(2048+g2)/2^x := by
      rw [hyx,Nat.div_div_eq_div_mul,← pow_succ]; congr 2; omega
    rw [hx,stop_fixed w index coord [] _ _ _ _ _ H4]
    simp only [map_bind,bind_map_left,bind_assoc]
    congr 1; funext n4
    have hr : (2048+g2)/2^x/2^(11-x)=1 := by
      rw [Nat.div_div_eq_div_mul,← pow_add,show x+(11-x)=11 by omega]; omega
    simp [hr]

#print axioms coord_program_exact
end SigGolfCandidate.T3M.CanonicalSchedule
