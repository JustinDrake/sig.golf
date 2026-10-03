import SigGolfCandidate.T3.Rev
import SigGolfCandidate.Rv.Expr
import SigGolfCandidate.T3M.Images.Verify

namespace SigGolfCandidate.T3M.RevNet
open SigGolfCandidate.Rv SigGolfCandidate.T3.Rev
theorem tabRev_eq : ∀ n v, Images.tabRev n v = revBits n v
  | 0, _ => rfl
  | n + 1, v => by simp only [Images.tabRev, revBits, tabRev_eq n (v / 2)]
theorem verifyTabWord_eq (j : Nat) : Images.verifyTabWord j = revBits 64 (2048 + j) := tabRev_eq 64 _
def bvA (x : BitVec 64) : BitVec 64 :=
  BinOp.eval .or (BinOp.eval .srl x 8#64) (BinOp.eval .sll (BinOp.eval .and x 255#64) 8#64)
def bvS (k M x : BitVec 64) : BitVec 64 :=
  BinOp.eval .or (BinOp.eval .and (BinOp.eval .srl x k) M) (BinOp.eval .sll (BinOp.eval .and x M) k)
def revNetBV (x : BitVec 64) : BitVec 64 :=
  BinOp.eval .sll (bvS 1#64 21845#64 (bvS 2#64 13107#64 (bvS 4#64 3855#64 (bvA x)))) 48#64
@[irreducible] def ok1 (v : Nat) : Bool := revNetBV (BitVec.ofNat 64 v) == BitVec.ofNat 64 (revBits 64 v)
def chk (b : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => ok1 (b + n) && chk b n
theorem ok1_sound {v : Nat} (h : ok1 v = true) : revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v) := by
  unfold ok1 at h; exact beq_iff_eq.mp h
theorem chk_succ (b n : Nat) : chk b (n + 1) = (ok1 (b + n) && chk b n) := by rw [chk]
theorem chk_sound (b : Nat) : ∀ n, chk b n = true → ∀ v, b ≤ v → v < b + n →
    revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v)
  | 0, _, v, _, h2 => absurd h2 (by omega)
  | n + 1, h, v, h1, h2 => by
    rw [chk_succ, Bool.and_eq_true] at h
    by_cases hv : v = b + n
    · subst hv; exact ok1_sound h.1
    · exact chk_sound b n h.2 v h1 (by omega)
theorem chk0 : chk 0 1024 = true := by decide +kernel
theorem chk1 : chk 1024 1024 = true := by decide +kernel
theorem chk2 : chk 2048 1024 = true := by decide +kernel
theorem chk3 : chk 3072 1024 = true := by decide +kernel
theorem revNetBV_eq (v : Nat) (hv : v < 2 ^ 12) :
    revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v) := by
  rcases (show v < 1024 ∨ (1024 ≤ v ∧ v < 2048) ∨ (2048 ≤ v ∧ v < 3072) ∨ (3072 ≤ v ∧ v < 4096) by omega) with
    h | h | h | h
  · exact chk_sound 0 1024 chk0 v (by omega) (by omega)
  · exact chk_sound 1024 1024 chk1 v h.1 (by omega)
  · exact chk_sound 2048 1024 chk2 v h.1 (by omega)
  · exact chk_sound 3072 1024 chk3 v h.1 (by omega)
end SigGolfCandidate.T3M.RevNet
