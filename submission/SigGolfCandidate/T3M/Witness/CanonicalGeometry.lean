import SigGolfCandidate.T3M.Witness.SideCost

/-! Address arithmetic for the digest-derived FTS dispatch. These are pure
preconditions for the native refinement, not a machine certificate. -/
namespace SigGolfCandidate.T3M.CanonicalGeometry

/-- XOR of two fields with an identical aligned prefix cancels the prefix. -/
theorem xor_shared_prefix (k stem x y : Nat) (hx : x<2^k) (hy : y<2^k) :
    (2^k*stem+x) ^^^ (2^k*stem+y) = x ^^^ y := by
  have hpos : 0<2^k := Nat.two_pow_pos k
  have hxdiv : (2^k*stem+x)/2^k=stem := by
    rw [Nat.add_comm, Nat.mul_comm (2^k) stem,
      Nat.add_mul_div_right x stem hpos, Nat.div_eq_of_lt hx, Nat.zero_add]
  have hydiv : (2^k*stem+y)/2^k=stem := by
    rw [Nat.add_comm, Nat.mul_comm (2^k) stem,
      Nat.add_mul_div_right y stem hpos, Nat.div_eq_of_lt hy, Nat.zero_add]
  have hxmod : (2^k*stem+x)%2^k=x := by simp [Nat.mul_comm, Nat.add_comm, Nat.mod_eq_of_lt hx]
  have hymod : (2^k*stem+y)%2^k=y := by simp [Nat.mul_comm, Nat.add_comm, Nat.mod_eq_of_lt hy]
  have hsplit := Nat.div_add_mod ((2^k*stem+x) ^^^ (2^k*stem+y)) (2^k)
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow, hxdiv, hydiv, hxmod, hymod,
    Nat.xor_self, Nat.mul_zero, Nat.zero_add] at hsplit
  exact hsplit.symm

/-- Multiplying by the eight-byte table stride shifts XOR by three bits. -/
theorem xor_stride (x y : Nat) : (8*x) ^^^ (8*y) = 8*(x ^^^ y) := by
  have hsplit := Nat.div_add_mod ((8*x) ^^^ (8*y)) (2^3)
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow] at hsplit
  norm_num at hsplit
  exact hsplit.symm

def pointer (bucket leaf : Nat) : Nat := 16709632+8*(128*bucket+leaf)

/-- The existing header-table pointers already contain the required alignment:
one XOR gives the metadata byte offset without a shift or mask. -/
theorem pointer_xor (bucket x y : Nat) (hx : x<128) (hy : y<128) :
    pointer bucket x ^^^ pointer bucket y = 8*(x ^^^ y) := by
  have h1 : pointer bucket x = 2^10*(16318+bucket)+8*x := by unfold pointer; norm_num; ring
  have h2 : pointer bucket y = 2^10*(16318+bucket)+8*y := by unfold pointer; norm_num; ring
  rw [h1,h2,xor_shared_prefix 10 (16318+bucket) (8*x) (8*y) (by omega) (by omega),xor_stride]

/-- Global leaves in a common 128-leaf bucket have the same XOR as their local
indices. Thus the metadata height is exactly the source LCA height. -/
theorem global_leaf_xor (bucket x y : Nat) (hx : x<128) (hy : y<128) :
    (128*bucket+x) ^^^ (128*bucket+y) = x ^^^ y := by
  simpa using xor_shared_prefix 7 bucket x y hx hy

theorem global_lca (bucket x y : Nat) (hx : x<128) (hy : y<128) :
    lcaLevel (128*bucket+x) (128*bucket+y) = lcaLevel x y := by
  unfold lcaLevel
  rw [global_leaf_xor bucket x y hx hy]

theorem pointer_xor_bound (bucket x y : Nat) (hx : x<128) (hy : y<128) :
    pointer bucket x ^^^ pointer bucket y < 1024 := by
  rw [pointer_xor bucket x y hx hy]
  have h := Nat.xor_lt_two_pow (n:=7) hx hy
  omega

end SigGolfCandidate.T3M.CanonicalGeometry
