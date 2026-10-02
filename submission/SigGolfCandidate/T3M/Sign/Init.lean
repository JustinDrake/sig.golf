import SigGolfCandidate.T3M.Sign.Basic

/-!
# The sign initial state

`sinit sk cache m` is the loaded state (zero registers and memory, the secret key at `SK = 0x80`,
the cache at `CACHE = 0x9000`, the message at `MSG = 0x40`, `sp = 2^24`; `initialState_sign` is in `Sign/InitState`).
Doubleword views: `sinit_sk`, `sinit_msg`, `sinit_cache`, `sinit_zero`; the cache as Core's
`cacheBytes (cacheDec cache)`: `sinit_tag` (the tag doublewords) and `sinit_region` (the region
doublewords at `REGION`).
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Cache Region cacheBytes readLE)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## Reading doublewords -/

theorem readWords_of_get (t : MachineState) (A : Nat) :
    ∀ (m : Nat) (l : List Word), l.length = m →
      (∀ j < m, t.getMem (BitVec.ofNat 64 (A + 8 * j)) = l.getD j 0) → t.readWords (BitVec.ofNat 64 A) m = l
  | 0, l, hl, _ => by rw [List.length_eq_zero_iff] at hl; subst hl; rfl
  | m + 1, l, hl, h => by
    obtain ⟨l', d, rfl⟩ : ∃ l' d, l = l' ++ [d] := ⟨l.dropLast, l.getLast (by
      intro he; subst he; simp at hl), (List.dropLast_append_getLast _).symm⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    rw [readWords_add, readWords_of_get t A m l' hl (fun j hj => by
      rw [h j (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hl ▸ hj)]),
      readWords_one, h m (by omega)]
    simp [List.getD_eq_getElem?_getD, hl]

/-- Doubleword `j` of a little-endian byte list read as a number. -/
theorem extractLsb'_ofNat_readLE (m : Nat) (l : List UInt8) (hl : l.length = 8 * m) (j : Nat) (hj : j < m) :
    (BitVec.ofNat (8 * (8 * m)) (readLE l)).extractLsb' (64 * j) 64 = (wordsOf l).getD j 0 := by
  rw [wordsOf_eq_range m l hl]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  have hlt := readLE_lt l
  rw [hl, ← two_pow_eight_mul] at hlt
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]

/-! ## The loaded state -/

/-- The sign initial state: zero registers and memory, the secret key at `SK`, the cache at `CACHE`,
the message at `MSG`, `sp = 2^24`. -/
def sinit (sk : SecretKey) (cache : Bytes 32768) (m : Message) : MachineState :=
  (((({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 0x80) (bytes sk)).writeBytesAsWords (BitVec.ofNat 64 0x9000) (bytes cache)).writeBytesAsWords
    (BitVec.ofNat 64 0x40) (bytes m)).setReg .x2 (BitVec.ofNat 64 (2 ^ 24))

theorem sinit_pc (sk : SecretKey) (cache : Bytes 32768) (m : Message) : (sinit sk cache m).pc = pcOf 0 := by
  unfold sinit
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords]
  rfl

theorem bytes_length' {n : Nat} (x : Bytes n) : (bytes x).length = n := by simp [bytes]

theorem sinit_getMem (sk : SecretKey) (cache : Bytes 32768) (m : Message) (A : Nat) (hA : A < 2 ^ 64) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 A) =
      if 0x40 ≤ A ∧ A < 0x60 ∧ (A - 0x40) % 8 = 0 then bytesToWordLE (((bytes m).drop (A - 0x40)).take 8)
      else if 0x9000 ≤ A ∧ A < 0x11000 ∧ (A - 0x9000) % 8 = 0 then
        bytesToWordLE (((bytes cache).drop (A - 0x9000)).take 8)
      else if 0x80 ≤ A ∧ A < 0xA0 ∧ (A - 0x80) % 8 = 0 then bytesToWordLE (((bytes sk).drop (A - 0x80)).take 8)
      else 0 := by
  unfold sinit
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x40 A (by rw [bytes_length']; decide) hA,
    getMem_writeBytesAsWords _ _ 0x9000 A (by rw [bytes_length']; decide) hA,
    getMem_writeBytesAsWords _ _ 0x80 A (by rw [bytes_length']; decide) hA, bytes_length', bytes_length',
    bytes_length']
  rfl

theorem sinit_sk (sk : SecretKey) (cache : Bytes 32768) (m : Message) (j : Nat) (hj : j < 4) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (SK + 8 * j)) = sk.extractLsb' (64 * j) 64 := by
  rw [sinit_getMem _ _ _ _ (by sg_omega), if_neg (by sg_omega), if_neg (by sg_omega), if_pos (by sg_omega),
    show SK + 8 * j - 0x80 = 8 * j by sg_omega, bytesToWordLE_bytes sk j (by omega)]

theorem sinit_msg (sk : SecretKey) (cache : Bytes 32768) (m : Message) (j : Nat) (hj : j < 4) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (MSG + 8 * j)) = m.extractLsb' (64 * j) 64 := by
  rw [sinit_getMem _ _ _ _ (by sg_omega), if_pos (by sg_omega), show MSG + 8 * j - 0x40 = 8 * j by sg_omega,
    bytesToWordLE_bytes m j (by omega)]

theorem sinit_cache (sk : SecretKey) (cache : Bytes 32768) (m : Message) (j : Nat) (hj : j < 4096) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (CACHE + 8 * j)) = cache.extractLsb' (64 * j) 64 := by
  rw [sinit_getMem _ _ _ _ (by sg_omega), if_neg (by sg_omega), if_pos (by sg_omega),
    show CACHE + 8 * j - 0x9000 = 8 * j by sg_omega, bytesToWordLE_bytes cache j (by omega)]

theorem sinit_zero (sk : SecretKey) (cache : Bytes 32768) (m : Message) (A : Nat) (hA : A < 2 ^ 64)
    (h : A < 0x40 ∨ (0x60 ≤ A ∧ A < 0x80) ∨ (0xA0 ≤ A ∧ A < 0x9000) ∨ 0x11000 ≤ A) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 A) = 0 := by
  rw [sinit_getMem _ _ _ _ hA, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ## The cache as Core's `cacheBytes (cacheDec cache)` -/

theorem sinit_cacheWords (sk : SecretKey) (cache : Bytes 32768) (m : Message) (j : Nat) (hj : j < 4096) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (CACHE + 8 * j)) =
      (wordsOf (cacheBytes (cacheDec cache))).getD j 0 := by
  rw [sinit_cache _ _ _ j hj]
  conv_lhs => rw [← cacheB_cacheDec cache]
  exact extractLsb'_ofNat_readLE 4096 _ (cacheBytes_length _) j hj

theorem wordsOf_cacheBytes (c : Cache) :
    wordsOf (cacheBytes c) = [c.tag.extractLsb' 0 64, c.tag.extractLsb' 64 64, c.tag.extractLsb' 128 64,
      c.tag.extractLsb' 192 64] ++ wordsOf (List.ofFn c.region) := by
  rw [cacheBytes, wordsOf_append (bytesLE 32 c.tag) (List.ofFn c.region) (by rw [bytesLE_length]),
    wordsOf_bytesLE32]

theorem length_wordsOf_region (r : Region) : (wordsOf (List.ofFn r)).length = 4092 := by
  rw [wordsOf_eq_range 4092 _ (by rw [List.length_ofFn]), List.length_map, List.length_range]

/-- The tag doublewords of the loaded cache. -/
theorem sinit_tag (sk : SecretKey) (cache : Bytes 32768) (m : Message) (k : Nat) (hk : k < 4) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (CACHE + 8 * k)) = (cacheDec cache).tag.extractLsb' (64 * k) 64 := by
  rw [sinit_cacheWords _ _ _ k (by omega), wordsOf_cacheBytes]
  interval_cases k <;> rfl

/-- The region doublewords of the loaded cache. -/
theorem sinit_region (sk : SecretKey) (cache : Bytes 32768) (m : Message) :
    (sinit sk cache m).readWords (BitVec.ofNat 64 REGION) 4092 = wordsOf (List.ofFn (cacheDec cache).region) := by
  refine readWords_of_get _ _ _ _ (length_wordsOf_region _) (fun j hj => ?_)
  rw [show REGION + 8 * j = CACHE + 8 * (4 + j) by sg_omega, sinit_cacheWords _ _ _ _ (by omega),
    wordsOf_cacheBytes, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (show [(cacheDec cache).tag.extractLsb' 0 64, (cacheDec cache).tag.extractLsb' 64 64,
      (cacheDec cache).tag.extractLsb' 128 64, (cacheDec cache).tag.extractLsb' 192 64].length ≤ 4 + j by
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_singleton]; omega)]
  rw [List.length_cons, List.length_cons, List.length_cons, List.length_singleton, Nat.add_sub_cancel_left]

end SigGolfCandidate.T3M.Sign
