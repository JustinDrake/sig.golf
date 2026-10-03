import SigGolfCandidate.T3M.Sign.Basic
import SigGolfCandidate.T3M.Search.TopTables

/-!
# Sign: the base invariant (owned by instance F; shared)

`Base sk cache t` : the facts every phase after the nonce relies on and preserves: `t0 = 0`, the private
prefix `S0 | . | S1 | 0^16` at `PRIV`, the cache region at `REGION` (doublewords of `cache`), and the zero
doublewords that sign never writes (`NeverW`); `Base.frame` transports it along any frame avoiding `BaseA`.
`Base.region_words` : the region as Core's `List.ofFn (cacheDec cache).region`.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## The base invariant -/

/-- Doublewords that sign never writes and that later phases read as zero. -/
def NeverW (A : Nat) : Prop :=
  A = FLEAF ∨ A = FLEAF + 8 ∨ A = FLEAF + 48 ∨ A = FLEAF + 56 ∨ A = NODE + 32 ∨ A = NODE + 40 ∨
    A = CHAIN ∨ A = CHAIN + 8 ∨ A = CHAIN + 32 ∨ A = CHAIN + 40 ∨ A = LEAFPK + 880 ∨ A = LEAFPK + 888 ∨
    (ZDIG ≤ A ∧ A < ZDIG + 64) ∨ A = ENC + 40 ∨ A = ENC + 48 ∨ A = ENC + 56 ∨ A = NBUF + 32

/-- The doublewords `Base` is about. -/
def BaseA (A : Nat) : Prop :=
  A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨ A = PRIV + 56 ∨
    (REGION ≤ A ∧ A < REGION + 131040) ∨ NeverW A ∨
      (Search.TOP_DATA ≤ A ∧ A < Search.TOP_DATA + 632)

/-- Facts every phase after the nonce relies on and preserves. -/
structure Base (sk : SecretKey) (cache : Bytes 131072) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  p0 : t.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  region : ∀ k < 16380, t.getMem (BitVec.ofNat 64 (REGION + 8 * k)) = cache.extractLsb' (64 * (k + 4)) 64
  zero : ∀ A < 2 ^ 64, NeverW A → t.getMem (BitVec.ofNat 64 A) = 0
  table : Search.TableOK t

theorem Base.frame {sk : SecretKey} {cache : Bytes 131072} {t u : MachineState} {W : Nat → Prop}
    {l : List Reg} (h : Base sk cache t) (hf : Frame t u W) (hr : RegsExcept t u l) (h5 : .x5 ∉ l)
    (hW : ∀ A, A < 2 ^ 64 → BaseA A → ¬ W A) : Base sk cache u := by
  have g : ∀ A, A < 2 ^ 64 → BaseA A → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hb => hf.get hA (hW A hA hb)
  refine ⟨by rw [hr.get h5, h.x5], ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun A hA hn => ?_, ?_⟩
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p0]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p8]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p32]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p40]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p48]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p56]
  · rw [g _ (by sg_omega) (by unfold BaseA; right; right; right; right; right; right; left; sg_omega),
      h.region k hk]
  · rw [g _ hA (by unfold BaseA; right; right; right; right; right; right; right; left; exact hn), h.zero A hA hn]
  · exact h.table.frame hf (fun i hi => hW _ (by unfold Search.TOP_DATA; omega) (by
      unfold BaseA
      right; right; right; right; right; right; right; right
      unfold Search.TOP_DATA; omega))

/-! ## The cache region as Core's region -/

theorem readWords_eq_map (t : MachineState) (A : Nat) :
    ∀ n, A + 8 * n < 2 ^ 64 →
      t.readWords (BitVec.ofNat 64 A) n = (List.range n).map fun j => t.getMem (BitVec.ofNat 64 (A + 8 * j))
  | 0, _ => rfl
  | n + 1, h => by
    rw [readWords_add, readWords_eq_map t A n (by omega), readWords_one, List.range_succ, List.map_append]
    rfl

theorem readLE_region (cache : Bytes 131072) :
    T3.readLE (List.ofFn (cacheDec cache).region) = cache.toNat / 2 ^ 256 := by
  have e : List.ofFn (cacheDec cache).region =
      List.ofFn fun i : Fin 131040 => UInt8.ofNat (cache.toNat / 256 ^ 32 / 256 ^ i.val % 256) := by
    exact congrArg List.ofFn (funext fun i => by
      show UInt8.ofNat (cache.toNat / 256 ^ (32 + i.val) % 256) = _
      rw [pow_add, Nat.div_div_eq_div_mul])
  rw [e, readLE_ofFn_digits, show (256 : Nat) ^ 32 = 2 ^ 256 by norm_num]
  apply Nat.mod_eq_of_lt
  have h1 : cache.toNat < 2 ^ (256 + 8 * 131040) :=
    lt_of_lt_of_eq cache.isLt (congrArg (2 ^ ·) (by norm_num : 8 * 131072 = 256 + 8 * 131040))
  have h2 : (256 : Nat) ^ 131040 = 2 ^ (8 * 131040) :=
    (congrArg (· ^ 131040) (by norm_num : (256 : Nat) = 2 ^ 8)).trans (pow_mul 2 8 131040).symm
  rw [h2]
  rw [pow_add] at h1
  exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (lt_of_lt_of_eq h1 (Nat.mul_comm _ _))

theorem wordsOf_region (cache : Bytes 131072) :
    wordsOf (List.ofFn (cacheDec cache).region) =
      (List.range 16380).map fun k => cache.extractLsb' (64 * (k + 4)) 64 := by
  rw [wordsOf_eq_range 16380 _ (by rw [List.length_ofFn]), readLE_region]
  apply List.map_congr_left
  intro k _
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]
  congr 3; ring

theorem Base.region_words {sk : SecretKey} {cache : Bytes 131072} {t : MachineState} (h : Base sk cache t) :
    t.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn (cacheDec cache).region) := by
  rw [readWords_eq_map t REGION 16380 (by sg_omega), wordsOf_region]
  exact List.map_congr_left (fun k hk => h.region k (List.mem_range.mp hk))

/-! ## The layer-phase base invariant (E8)

`build_tree` writes the root's right child to `ENC + 48`: the layers keep `Base` without those two doublewords. -/

/-- `NeverW` without `ENC + 48`, `ENC + 56`. -/
def NeverWL (A : Nat) : Prop :=
  A = FLEAF ∨ A = FLEAF + 8 ∨ A = FLEAF + 48 ∨ A = FLEAF + 56 ∨ A = NODE + 32 ∨ A = NODE + 40 ∨
    A = CHAIN ∨ A = CHAIN + 8 ∨ A = CHAIN + 32 ∨ A = CHAIN + 40 ∨ A = LEAFPK + 880 ∨ A = LEAFPK + 888 ∨
    (ZDIG ≤ A ∧ A < ZDIG + 64) ∨ A = ENC + 40 ∨ A = NBUF + 32

/-- The doublewords `BaseL` is about. -/
def BaseAL (A : Nat) : Prop :=
  A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨ A = PRIV + 56 ∨
    (REGION ≤ A ∧ A < REGION + 131040) ∨ NeverWL A ∨
      (Search.TOP_DATA ≤ A ∧ A < Search.TOP_DATA + 632)

/-- `Base` of the layer phase. -/
structure BaseL (sk : SecretKey) (cache : Bytes 131072) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  p0 : t.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  region : ∀ k < 16380, t.getMem (BitVec.ofNat 64 (REGION + 8 * k)) = cache.extractLsb' (64 * (k + 4)) 64
  zero : ∀ A < 2 ^ 64, NeverWL A → t.getMem (BitVec.ofNat 64 A) = 0
  table : Search.TableOK t

theorem Base.toBaseL {sk : SecretKey} {cache : Bytes 131072} {t : MachineState} (h : Base sk cache t) :
    BaseL sk cache t :=
  ⟨h.x5, h.p0, h.p8, h.p32, h.p40, h.p48, h.p56, h.region, fun A hA hn => h.zero A hA (by
    unfold NeverWL at hn; unfold NeverW; tauto), h.table⟩

theorem BaseL.frame {sk : SecretKey} {cache : Bytes 131072} {t u : MachineState} {W : Nat → Prop}
    {l : List Reg} (h : BaseL sk cache t) (hf : Frame t u W) (hr : RegsExcept t u l) (h5 : .x5 ∉ l)
    (hW : ∀ A, A < 2 ^ 64 → BaseAL A → ¬ W A) : BaseL sk cache u := by
  have g : ∀ A, A < 2 ^ 64 → BaseAL A → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hb => hf.get hA (hW A hA hb)
  refine ⟨by rw [hr.get h5, h.x5], ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun A hA hn => ?_, ?_⟩
  · rw [g _ (by sg_omega) (by unfold BaseAL; simp), h.p0]
  · rw [g _ (by sg_omega) (by unfold BaseAL; simp), h.p8]
  · rw [g _ (by sg_omega) (by unfold BaseAL; simp), h.p32]
  · rw [g _ (by sg_omega) (by unfold BaseAL; simp), h.p40]
  · rw [g _ (by sg_omega) (by unfold BaseAL; simp), h.p48]
  · rw [g _ (by sg_omega) (by unfold BaseAL; simp), h.p56]
  · rw [g _ (by sg_omega) (by unfold BaseAL; right; right; right; right; right; right; left; sg_omega),
      h.region k hk]
  · rw [g _ hA (by unfold BaseAL; right; right; right; right; right; right; right; left; exact hn), h.zero A hA hn]
  · exact h.table.frame hf (fun i hi => hW _ (by unfold Search.TOP_DATA; omega) (by
      unfold BaseAL
      right; right; right; right; right; right; right; right
      unfold Search.TOP_DATA; omega))

theorem BaseL.region_words {sk : SecretKey} {cache : Bytes 131072} {t : MachineState} (h : BaseL sk cache t) :
    t.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn (cacheDec cache).region) := by
  rw [readWords_eq_map t REGION 16380 (by sg_omega), wordsOf_region]
  exact List.map_congr_left (fun k hk => h.region k (List.mem_range.mp hk))

end SigGolfCandidate.T3M.Sign
