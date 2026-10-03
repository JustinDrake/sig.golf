import Mathlib.Tactic

namespace SigGolfResearch.NonbinaryTop.Codec
set_option maxHeartbeats 1000000
abbrev Triple5 := Fin 3 → Fin 5
abbrev Triple4 := Fin 3 → Fin 4
def rank5 (d : Triple5) : Fin 125 :=
  ⟨(d 0).val + 5 * (d 1).val + 25 * (d 2).val, by
    have := (d 0).isLt; have := (d 1).isLt; have := (d 2).isLt; omega⟩
def digits5 (r : Fin 125) : Triple5 := fun i =>
  if i=0 then ⟨r.val % 5, Nat.mod_lt _ (by decide)⟩
  else if i=1 then ⟨r.val / 5 % 5, Nat.mod_lt _ (by decide)⟩
  else ⟨r.val / 25, by have := r.isLt; omega⟩
theorem digits5_rank5 (d : Triple5) : digits5 (rank5 d)=d := by
  funext i; apply Fin.ext
  have h0 := (d 0).isLt; have h1 := (d 1).isLt; have h2 := (d 2).isLt
  fin_cases i <;> simp [digits5,rank5] <;> omega
theorem rank5_digits5 (r : Fin 125) : rank5 (digits5 r)=r := by
  apply Fin.ext
  have := r.isLt
  simp [rank5,digits5]
  omega
def triple5Equiv : Triple5 ≃ Fin 125 where
  toFun := rank5
  invFun := digits5
  left_inv := digits5_rank5
  right_inv := rank5_digits5
def rank4 (d : Triple4) : Fin 64 :=
  ⟨(d 0).val + 4 * (d 1).val + 16 * (d 2).val, by
    have := (d 0).isLt; have := (d 1).isLt; have := (d 2).isLt; omega⟩
def digits4 (r : Fin 64) : Triple4 := fun i =>
  if i=0 then ⟨r.val % 4, Nat.mod_lt _ (by decide)⟩
  else if i=1 then ⟨r.val / 4 % 4, Nat.mod_lt _ (by decide)⟩
  else ⟨r.val / 16, by have := r.isLt; omega⟩
theorem digits4_rank4 (d : Triple4) : digits4 (rank4 d)=d := by
  funext i; apply Fin.ext
  have h0 := (d 0).isLt; have h1 := (d 1).isLt; have h2 := (d 2).isLt
  fin_cases i <;> simp [digits4,rank4] <;> omega
theorem rank4_digits4 (r : Fin 64) : rank4 (digits4 r)=r := by
  apply Fin.ext
  have := r.isLt
  simp [rank4,digits4]
  omega
def triple4Equiv : Triple4 ≃ Fin 64 where
  toFun := rank4
  invFun := digits4
  left_inv := digits4_rank4
  right_inv := rank4_digits4
def pack : List Nat → Nat → Nat
  | [], tail => tail
  | d::ds, tail => d+128*pack ds tail
def unpack : Nat → Nat → List Nat × Nat
  | 0,x => ([],x)
  | n+1,x => let p := unpack n (x/128); (x%128::p.1,p.2)
theorem unpack_pack (ds : List Nat) (tail : Nat) (h : ∀ d∈ds,d<128) :
    unpack ds.length (pack ds tail)=(ds,tail) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd := h d (by simp)
    have hr : ∀ z∈ds,z<128 := fun z hz => h z (by simp [hz])
    simp only [pack,List.length_cons,unpack,Nat.add_mul_div_left _ _ (by decide : 0<128),
      Nat.div_eq_of_lt hd,Nat.zero_add,ih hr,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hd]
theorem pack_lt (ds : List Nat) (tail bound : Nat) (ht : tail<bound)
    (h : ∀ d∈ds,d<128) : pack ds tail<bound*128^ds.length := by
  induction ds with
  | nil => simpa [pack] using ht
  | cons d ds ih =>
    have hd := h d (by simp)
    have hr : ∀ z∈ds,z<128 := fun z hz => h z (by simp [hz])
    have hi := ih hr
    simp only [pack,List.length_cons,pow_succ]
    nlinarith
abbrev Word := (Fin 17 → Triple5) × Triple4
def ranks (w : Word) : List Nat := List.ofFn (fun i => (rank5 (w.1 i)).val)
def encode (w : Word) : Nat := pack (ranks w) (rank4 w.2).val
theorem ranks_lt (w : Word) : ∀ d∈ranks w,d<128 := by
  intro d hd
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hd
  rw [←hi]
  exact lt_trans (rank5 (w.1 i)).isLt (by decide)
theorem decode_encode (w : Word) :
    unpack 17 (encode w)=(ranks w,(rank4 w.2).val) := by
  simpa [ranks,encode] using unpack_pack (ranks w) (rank4 w.2).val (ranks_lt w)
theorem encode_bound (w : Word) : encode w<2^125 := by
  have h := pack_lt (ranks w) (rank4 w.2).val 64 (rank4 w.2).isLt (ranks_lt w)
  simpa [encode,ranks] using h
theorem encode_injective : Function.Injective encode := by
  intro a b hab
  have h := congrArg (unpack 17) hab
  rw [decode_encode,decode_encode] at h
  have ht : a.1=b.1 := by
    have hlist := congrArg Prod.fst h
    have hf : (fun i => (rank5 (a.1 i)).val)=(fun i => (rank5 (b.1 i)).val) :=
      List.ofFn_injective hlist
    funext i
    exact triple5Equiv.injective (Fin.ext (congrFun hf i))
  have hq : a.2=b.2 := triple4Equiv.injective (Fin.ext (congrArg Prod.snd h))
  exact Prod.ext ht hq
theorem constant_sum_antichain {ι : Type} [Fintype ι] (a b : ι → Nat)
    (h : ∀ i,a i≤b i) (hs : ∑ i,a i=∑ i,b i) : a=b := by
  funext i
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => h j)).mp hs i (Finset.mem_univ i)
theorem constant_sum_backward_witness {ι : Type} [Fintype ι] (a b : ι → Nat)
    (hs : ∑ i,a i=∑ i,b i) (hne : a≠b) : ∃ i,b i<a i := by
  by_contra hn
  push_neg at hn
  exact hne (constant_sum_antichain a b hn hs)
end SigGolfResearch.NonbinaryTop.Codec
#print axioms SigGolfResearch.NonbinaryTop.Codec.digits5_rank5
#print axioms SigGolfResearch.NonbinaryTop.Codec.rank5_digits5
#print axioms SigGolfResearch.NonbinaryTop.Codec.decode_encode
#print axioms SigGolfResearch.NonbinaryTop.Codec.encode_bound
#print axioms SigGolfResearch.NonbinaryTop.Codec.encode_injective
#print axioms SigGolfResearch.NonbinaryTop.Codec.constant_sum_antichain
#print axioms SigGolfResearch.NonbinaryTop.Codec.constant_sum_backward_witness
