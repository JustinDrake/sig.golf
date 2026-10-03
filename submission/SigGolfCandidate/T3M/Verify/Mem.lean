import SigGolfCandidate.T3M.Verify.Words
import Mathlib.Data.Nat.Bitwise
import SigGolfCandidate.T3M.Search.TopTables
import SigGolfCandidate.T3M.Verify.Nonbinary.PairTables
import SigGolfCandidate.T3.Rev

/-!
# Verify memory: global invariant, witness predicates, checked writes (T3M)

The T3 verifier hashes the witness **in place**: it writes the header slot `T` of every leaf, fold, chain and
Merkle block it hashes and the current-node slot the previous hash output lands in (MACH-PLAN §3.1). So there is
no phase-independent "witness unchanged" invariant (W2 pattern, WC2 `Mem`); what is common to all phases:

* `Glob gk w pk s` : the phase's constant registers `gk` (always `t0 = 0`, `s2 = 4095` = `baseK`), the witness
  header `[0, 64)` (rho, dc, counters; never written: `WitHdr`), the public key, the zero words `0x128..0x140`
  of the encoding block (`PZero`) and the zero high half of its counter word `0x120` (written by `sw`, `PHalf`);
* `WitAll w s` : the whole witness region **and the zero memory after it** (up to `WX = 2^17` bytes above `WIT`)
  holds `wword w j` (= the witness doublewords, **zero past W**: `wword_zero`); `Orig w P s` : the same for the
  offsets satisfying `P` (the per-phase frontier invariants are built from it).

Every checked run (`Spec.specB`) writes only (a) constant addresses that are safe low-memory words (`safeAddr`), the
counter word by a low-half `sw`, or explicitly allowed witness words (`allow`, `≥ WLO = WIT + 64`), or
(b) **pointer-relative** addresses `r + off` (`r ∈ rel`, `off < 4096`; the FTS stream pointer `a4`), with
`RelOK rel s` (the pointer is `≥ WLO` and `< 2^23`) supplied by the caller. The caller accounts for the
witness writes through the run's exact memory (`SpecRes.mem`, `Orig_toState`).

T3K: the verify image embeds twelve doublewords at `DATA = 2^24 - 96` (`DataOK`, part of `Glob`). Every checked
write (allowed witness words `< 2^23`, pointer-relative writes below `2^23 + 4096`) and every hash destination
(`safeDest`: `d + 32 ≤ 2^23`) stays below them, so `Glob` keeps them (`memOKA_data`).
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)

/-! ## Layout -/

/-- The witness base. -/
def WIT : Nat := 0x800
/-- The witness size in bytes (`T3M.wsize`). -/
def WSZ : Nat := 24264
/-- The extent (bytes above `WIT`) of the witness predicates: the fold stream of an adversarial witness may run
past `W` (at most 35 segments of 11 folds: `< 32,232` bytes) before the pointer cap rejects; memory there is zero. -/
def WX : Nat := 2 ^ 17
/-- Allowed witness writes start here: the witness header `[0, 64)` is never written. -/
def WLO : Nat := WIT + 64

/-! ## Addresses -/

theorem ofNat_eq_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a = BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h; rw [h]

theorem ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun h' => h ((ofNat_eq_iff ha hb).mp h')

theorem ofNat_toNat_lt (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## `writeHash` -/

theorem getMem_setMem (s : MachineState) (a v A : Word) :
    (s.setMem a v).getMem A = if A = a then v else s.getMem A := by
  simp [MachineState.setMem, MachineState.getMem]

theorem writeHash_getMem (s : MachineState) (ans : BitVec 256) (A : Word) :
    (writeHash s ans).getMem A =
      if A = s.getReg .x12 + 8 + 8 + 8 then ans.extractLsb' 192 64
      else if A = s.getReg .x12 + 8 + 8 then ans.extractLsb' 128 64
      else if A = s.getReg .x12 + 8 then ans.extractLsb' 64 64
      else if A = s.getReg .x12 then ans.extractLsb' 0 64
      else s.getMem A := by
  simp only [writeHash, MachineState.writeWords]
  show ((((s.setMem _ _).setMem _ _).setMem _ _).setMem _ _).getMem A = _
  simp only [getMem_setMem]

/-- `writeHash` at a constant destination `d`. -/
theorem writeHash_getMem_ofNat (s : MachineState) (ans : BitVec 256) (d A : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hA : A < 2 ^ 64) (hd' : d + 24 < 2 ^ 64) :
    (writeHash s ans).getMem (BitVec.ofNat 64 A) =
      if A = d + 24 then ans.extractLsb' 192 64
      else if A = d + 16 then ans.extractLsb' 128 64
      else if A = d + 8 then ans.extractLsb' 64 64
      else if A = d then ans.extractLsb' 0 64
      else s.getMem (BitVec.ofNat 64 A) := by
  rw [writeHash_getMem, hd]
  simp only [show (8 : Word) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat,
    ofNat_eq_iff hA (by omega : d + 8 + 8 + 8 < 2 ^ 64), ofNat_eq_iff hA (by omega : d + 8 + 8 < 2 ^ 64),
    ofNat_eq_iff hA (by omega : d + 8 < 2 ^ 64), ofNat_eq_iff hA (by omega : d < 2 ^ 64)]

theorem writeWords_regs : ∀ (ws : List Word) (s : MachineState) (base : Word),
    (s.writeWords base ws).regs = s.regs ∧ (s.writeWords base ws).pc = s.pc
  | [], _, _ => ⟨rfl, rfl⟩
  | w :: ws, s, base => by
    simp only [MachineState.writeWords]
    obtain ⟨h1, h2⟩ := writeWords_regs ws (s.setMem base w) (base + 8)
    exact ⟨h1.trans rfl, h2.trans rfl⟩

theorem writeHash_getReg (s : MachineState) (ans : BitVec 256) (r : Reg) :
    (writeHash s ans).getReg r = s.getReg r := getReg_writeHash s ans r

theorem writeHash_pc (s : MachineState) (ans : BitVec 256) :
    (writeHash s ans).pc = s.pc + 4 := pc_writeHash s ans

theorem writeHash_frame (t : MachineState) (ans : BitVec 256) (d A : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hA : A < 2 ^ 64) (hd' : d + 24 < 2 ^ 64)
    (h : A + 8 ≤ d ∨ d + 32 ≤ A) :
    (writeHash t ans).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
  rw [writeHash_getMem_ofNat t ans d A hd hA hd', if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

theorem writeHash_at0 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 d) = ans.extractLsb' 0 64 := by
  rw [writeHash_getMem_ofNat t ans d d hd (by omega) hd', if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

theorem writeHash_at8 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 (d + 8)) = ans.extractLsb' 64 64 := by
  rw [writeHash_getMem_ofNat t ans d _ hd (by omega) hd', if_neg (by omega), if_neg (by omega),
    if_pos rfl]

theorem writeHash_at16 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 (d + 16)) = ans.extractLsb' 128 64 := by
  rw [writeHash_getMem_ofNat t ans d _ hd (by omega) hd', if_neg (by omega), if_pos rfl]

theorem writeHash_at24 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 (d + 24)) = ans.extractLsb' 192 64 := by
  rw [writeHash_getMem_ofNat t ans d _ hd (by omega) hd', if_pos rfl]

/-- The digest answer (low 16 bytes) written at `d` (`DigAt` of M0). -/
theorem writeHash_lo (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 d) = dlo (ans.extractLsb' 0 128) ∧
      (writeHash t ans).getMem (BitVec.ofNat 64 (d + 8)) = dhi (ans.extractLsb' 0 128) :=
  DigAt.writeHash_lo t ans d hd hd'

/-! ## Sub-word stores -/

theorem land_split (n M w s : Nat) (hws : w ≤ s) :
    n &&& (2 ^ s * M + (2 ^ w - 1)) = 2 ^ s * ((n / 2 ^ s) &&& M) + n % 2 ^ w := by
  have hw : 2 ^ w - 1 < 2 ^ s := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hws
    have : 0 < 2 ^ w := Nat.two_pow_pos _
    omega
  have hm : n % 2 ^ w < 2 ^ s := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) hws)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hw, Nat.testBit_two_pow_mul_add _ hm]
  split
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    cases n.testBit j <;> simp
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

theorem replaceWord32_0_toNat (w : BitVec 64) (v : BitVec 32) :
    (replaceWord32 w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat := by
  unfold replaceWord32
  have hm : (~~~(0xFFFFFFFF#64 <<< (0 * 32)) : BitVec 64) =
      BitVec.ofNat 64 (2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1)) := by decide
  rw [hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, Nat.zero_mul,
    Nat.shiftLeft_zero]
  have hv := v.isLt
  have hw := w.isLt
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1) < 2 ^ 64 by norm_num),
    land_split _ _ 0 32 (by decide), Nat.and_two_pow_sub_one_eq_mod, Nat.pow_zero, Nat.mod_one, Nat.add_zero,
    ← Nat.two_pow_add_eq_or_of_lt hv]
  ring

/-- `sw v, a` (low half): the high half of the word is kept. -/
theorem merge_w0_toNat (w v : BitVec 64) :
    (StoreKind.merge .w w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat % 2 ^ 32 := by
  simp only [StoreKind.merge, show (0 : Nat) / 4 = 0 from rfl]
  rw [replaceWord32_0_toNat]
  simp [BitVec.toNat_setWidth]

theorem merge_w0_high (w v : BitVec 64) :
    (StoreKind.merge .w w 0 v).toNat / 2 ^ 32 = w.toNat / 2 ^ 32 % 2 ^ 32 := by
  rw [merge_w0_toNat]; omega

/-! ## The global invariant -/

/-- Registers constant in every phase after the prologue: `t0 = 0` (HASH selector), `s2 = 4095` (the witness base
of the short-offset accesses, `WIT + off - 2047`; also the SWAR modulus of the layers). -/
def baseK : List (Reg × Word) := [(.x5, 0), (.x18, 0xFFF)]

/-- The zero words of the encoding block `[M | T | LE32 c | 0^28]` at `0x100` that no instruction writes. -/
def pSlots : List Nat := [0x128, 0x130, 0x138]

/-- The counter word of the encoding block: its high half (`0x124 .. 0x128`) is never written. -/
def CTRW : Nat := 0x120

def PkOK (pk : Digest) (s : MachineState) : Prop :=
  s.getMem 0xA0 = dlo pk ∧ s.getMem 0xA8 = dhi pk

def PZero (s : MachineState) : Prop := ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0

/-- The high half of the counter word is zero. -/
def PHalf (s : MachineState) : Prop := (s.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0

/-- The witness header words `[0, 64)` (rho, dc, the four counters, zero), never written by the verifier. -/
def WitHdr (w : WBytes) (s : MachineState) : Prop :=
  ∀ j, j < 8 → s.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = wword w j

/-- The verify image's embedded doublewords (`Images.verifyData`, little endian): the layer-3 constants `2^40`,
`M2c`, `M1c`, `0x30401`, `0x3fe00`, the FTS setup constants `A4_0`, `A4_LIMIT`, `0xa01`, `0x901`, `tbN`, `tbL`, a zero
pad. -/
def dataWords : List Nat :=
  [2 ^ 40, 17311559823019733055, 8198552921648689607, 0x30401, 0x3fe00, 2256, 11736, 0xa01, 0x901, 7072, 15264, 0]

/-- The data section's base: `dataBase` of the verify image (`16 ⌊(2^24 - 96) / 16⌋`). -/
def DATA : Nat := 16777120

/-- n3-99: the FTS header table's base = `dataBase` of the verify image (BIG1: `2^24 - 67584`); the table (2048
doublewords) is followed by the WOTS header table at `HDATA = TAB + 16384`, 2048 zero bytes, then the base data at
`Nonbinary.PAIR_DATA = TAB + 34816`. -/
def TAB : Nat := 16709632

/-- T3X: the WOTS header table (16384 bytes, 4 banks of 64 chains x 8 digits) right after the FTS table; the 2048
zero bytes after it make the bank midpoints 4096-aligned (T3Y). -/
def HDATA : Nat := 16726016

/-- T3X: the midpoint of layer `lay`'s 4096-byte header bank, shifted by the chain-index offset `koff`. -/
def headerBank (lay koff : Nat) : Nat := HDATA + 4096 * lay + 2048 + 64 * koff

/-- Both the embedded constants and the checksum lookup bytes are in place, (n3-99) the FTS header table:
doubleword `j < 2048` at `TAB` is `revBits 64 (2048 + j)`, word 1 of the tag-9 header of leaf `j`, and (T3X) the
WOTS header table. -/
structure DataOK (s : MachineState) : Prop where
  constants : ∀ k, k < 12 → s.getMem (BitVec.ofNat 64 (DATA + 8 * k)) = BitVec.ofNat 64 (dataWords.getD k 0)
  sum : Search.SumTableOK s
  packed : Nonbinary.PackedTables s
  tab : ∀ j, j < 2048 → s.getMem (BitVec.ofNat 64 (TAB + 8 * j)) = BitVec.ofNat 64 (T3.Rev.revBits 64 (2048 + j))
  /-- T3X: the header doubleword of layer `lay`, chain `i`, initial digit `d`. -/
  header : ∀ lay i d, lay < 4 → i < 64 → d < 8 →
    s.getMem (BitVec.ofNat 64 (HDATA + 4096 * lay + 64 * i + 8 * d)) =
      BitVec.ofNat 64 (0x101 + 65536 * lay + 2 ^ 40 * i + 2 ^ 32 * d)

instance {s : MachineState} : CoeFun (DataOK s) (fun _ => ∀ k, k < 12 →
    s.getMem (BitVec.ofNat 64 (DATA + 8 * k)) = BitVec.ofNat 64 (dataWords.getD k 0)) := ⟨DataOK.constants⟩

/-- The complete data invariant is preserved when all image-data doublewords stay unchanged. -/
theorem DataOK.congr {s t : MachineState} (h : DataOK s)
    (hm : ∀ A, TAB ≤ A → A + 8 ≤ 2 ^ 24 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : DataOK t := by
  constructor
  · intro k hk
    rw [hm _ (by unfold DATA TAB; omega) (by unfold DATA; omega)]
    exact h.constants k hk
  · intro i hi
    rw [T3M.getByte_eq_word _ _ (by unfold Search.TOP_DATA; omega),
      hm _ (by unfold Search.TOP_DATA TAB; omega) (by unfold Search.TOP_DATA; omega),
      ← T3M.getByte_eq_word _ _ (by unfold Search.TOP_DATA; omega)]
    exact h.sum i hi
  · exact h.packed.congr (fun A hA hB => hm A (by unfold Nonbinary.PAIR_DATA at hA; unfold TAB; omega) hB)
  · intro j hj
    rw [hm _ (by unfold TAB; omega) (by unfold TAB; omega)]
    exact h.tab j hj
  · intro lay i d hl hi hd
    rw [hm _ (by unfold HDATA TAB; omega) (by unfold HDATA; omega)]
    exact h.header lay i d hl hi hd

def Glob (gk : List (Reg × Word)) (w : WBytes) (pk : Digest) (s : MachineState) : Prop :=
  (∀ p ∈ gk, s.getReg p.1 = p.2) ∧ WitHdr w s ∧ PkOK pk s ∧ PZero s ∧ PHalf s ∧ DataOK s

/-! ## Witness predicates (reads past the witness see zero memory) -/

/-- The witness region and the memory after it (up to `WX`) hold the witness doublewords (zero past `W`). -/
def WitAll (w : WBytes) (s : MachineState) : Prop :=
  ∀ j, 8 * j < WX → s.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = wword w j

/-- The witness doublewords at (word-aligned) offsets `o < WX` with `P o` are original. -/
def Orig (w : WBytes) (P : Nat → Prop) (s : MachineState) : Prop :=
  ∀ j, 8 * j < WX → P (8 * j) → s.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = wword w j

theorem WitAll.orig {w : WBytes} {s : MachineState} (h : WitAll w s) (P : Nat → Prop) : Orig w P s :=
  fun j hj _ => h j hj

theorem WitAll.hdr {w : WBytes} {s : MachineState} (h : WitAll w s) : WitHdr w s :=
  fun j hj => h j (by unfold WX; omega)

theorem Orig.mono {w : WBytes} {s : MachineState} {P P' : Nat → Prop} (h : Orig w P s)
    (hP : ∀ o, P' o → P o) : Orig w P' s :=
  fun j h1 h2 => h j h1 (hP _ h2)

theorem Orig.frame {w : WBytes} {s t : MachineState} {P : Nat → Prop} (h : Orig w P s)
    (hf : ∀ j, 8 * j < WX → P (8 * j) →
      t.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = s.getMem (BitVec.ofNat 64 (WIT + 8 * j))) :
    Orig w P t :=
  fun j h1 h2 => (hf j h1 h2).trans (h j h1 h2)

/-- A doubleword at witness offset `off` (`8 ∣ off`, `off < WX`, `P off`). -/
theorem Orig.word {w : WBytes} {s : MachineState} {P : Nat → Prop} (hO : Orig w P s) (off : Nat)
    (h8 : off % 8 = 0) (hoff : off < WX) (hp : P off) :
    s.getMem (BitVec.ofNat 64 (WIT + off)) = wword w (off / 8) := by
  have := hO (off / 8) (by omega) (by rwa [show 8 * (off / 8) = off by omega])
  rwa [show 8 * (off / 8) = off by omega] at this

/-- The two doublewords of the witness digest at offset `off` (`wdig w off`). -/
theorem Orig.dig {w : WBytes} {s : MachineState} {P : Nat → Prop} (hO : Orig w P s) (off : Nat)
    (h8 : off % 8 = 0) (hoff : off + 8 < WX) (hp0 : P off) (hp1 : P (off + 8)) :
    s.getMem (BitVec.ofNat 64 (WIT + off)) = dlo (wdig w off) ∧
      s.getMem (BitVec.ofNat 64 (WIT + off + 8)) = dhi (wdig w off) := by
  obtain ⟨j, rfl⟩ : ∃ j, off = 8 * j := ⟨off / 8, by omega⟩
  refine ⟨?_, ?_⟩
  · rw [hO.word (8 * j) h8 (by omega) hp0, wdig_lo]; congr 1; omega
  · rw [show WIT + 8 * j + 8 = WIT + (8 * j + 8) by ring, hO.word (8 * j + 8) (by omega) hoff hp1, wdig_hi]
    congr 1; omega

/-! ## Checked memory writes -/

/-- A doubleword address below the witness that no protected word occupies. -/
def safeAddr (n : Nat) : Bool :=
  decide (n + 8 ≤ WIT) && !(pSlots.contains n) && n != 0xA0 && n != 0xA8 && n != CTRW

/-- A `sw` into the low half of the word at `a`. -/
def isLowW (a : Nat) : E → Bool
  | .bin (.st .w 0) (.ld (.c k)) _ => k.toNat == a
  | _ => false

/-- A write relative to a pointer register of `rel` with a small offset. -/
def relOK (rel : List Reg) (a : Addr) : Bool :=
  match a.base with
  | some (.reg r) => rel.any (fun x => Reg.beqN x r) && decide (a.off.toNat < 4096)
  | _ => false

/-- Every write is (a) at a constant address that is safe, or the counter word by a low-half `sw`, or in `allow`
(a witness address `≥ WLO`), or (b) relative to a pointer register of `rel` (offset `< 4096`). -/
def memOKA (allow : List Nat) (rel : List Reg) (ws : SymMem) : Bool :=
  ws.all fun p => relOK rel p.1 || (p.1.base.isNone &&
    (safeAddr p.1.off.toNat || (p.1.off.toNat == CTRW && isLowW CTRW p.2) ||
      (allow.contains p.1.off.toNat && decide (WLO ≤ p.1.off.toNat ∧ p.1.off.toNat < 2 ^ 23))))

/-- No witness write at all. -/
def memOK (ws : SymMem) : Bool := memOKA [] [] ws

def regsOK (gk : List (Reg × Word)) (rf : RegFile) : Bool := gk.all fun p => E.beq (rf.get p.1) (.c p.2)

/-- The pointer registers of relative writes point into the witness area (`≥ WLO`) and are small. -/
def RelOK (rel : List Reg) (s : MachineState) : Prop :=
  ∀ r ∈ rel, WLO ≤ (s.getReg r).toNat ∧ (s.getReg r).toNat < 2 ^ 23

theorem RelOK.nil (s : MachineState) : RelOK [] s := fun _ h => by simp at h

/-- The words a run never writes: the low protected words and the witness header. -/
def Prot (A : Nat) : Prop := A ∈ pSlots ∨ A = 0xA0 ∨ A = 0xA8 ∨ (WIT ≤ A ∧ A < WLO)

theorem safeAddr_spec {n : Nat} (h : safeAddr n = true) :
    n + 8 ≤ WIT ∧ n ∉ pSlots ∧ n ≠ 0xA0 ∧ n ≠ 0xA8 ∧ n ≠ CTRW := by
  unfold safeAddr at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun hm => ?_, h3, h4, h5⟩
  rw [List.contains_iff_mem.mpr hm] at h2; cases h2

theorem relOK_spec {rel : List Reg} : ∀ {a : Addr}, relOK rel a = true →
    ∃ r ∈ rel, a.base = some (.reg r) ∧ a.off.toNat < 4096
  | ⟨some (.reg r), off⟩, h => by
    simp only [relOK, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨x, hx, hxr⟩, hoff⟩ := h
    obtain rfl := Reg.beqN_eq hxr
    exact ⟨x, hx, rfl, hoff⟩
  | ⟨none, _⟩, h => by simp [relOK] at h
  | ⟨some (.c _), _⟩, h => by simp [relOK] at h
  | ⟨some (.ld _), _⟩, h => by simp [relOK] at h
  | ⟨some (.un _ _), _⟩, h => by simp [relOK] at h
  | ⟨some (.bin _ _ _), _⟩, h => by simp [relOK] at h
  | ⟨some (.ite _ _ _ _ _), _⟩, h => by simp [relOK] at h

/-- The shapes a `memOKA allow rel` write can have. -/
theorem memOKA_cases {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    {p : Addr × E} (hp : p ∈ ws) :
    (∃ r ∈ rel, p.1.base = some (.reg r) ∧ p.1.off.toNat < 4096) ∨
    (p.1.base = none ∧
      (safeAddr p.1.off.toNat = true ∨ (p.1.off.toNat = CTRW ∧ isLowW CTRW p.2 = true) ∨
        (p.1.off.toNat ∈ allow ∧ WLO ≤ p.1.off.toNat ∧ p.1.off.toNat < 2 ^ 23))) := by
  have := List.all_eq_true.mp h p hp
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Option.isNone_iff_eq_none] at this
  rcases this with hr | ⟨hb, hc⟩
  · exact Or.inl (relOK_spec hr)
  · right
    refine ⟨hb, ?_⟩
    rcases hc with (h1 | h2) | ⟨h3, h4⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨List.contains_iff_mem.mp h3, h4⟩)

/-- A relative write lands at `≥ WLO`. -/
theorem relWrite_ge {rel : List Reg} {s : MachineState} (hrel : RelOK rel s) {a : Addr} {r : Reg}
    (hr : r ∈ rel) (hb : a.base = some (.reg r)) (hoff : a.off.toNat < 4096) :
    (a.eval s).toNat = (s.getReg r).toNat + a.off.toNat ∧ WLO ≤ (a.eval s).toNat := by
  obtain ⟨h1, h2⟩ := hrel r hr
  obtain ⟨b, off⟩ := a
  simp only at hb hoff ⊢
  subst hb
  simp only [Addr.eval, E.eval, BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact ⟨rfl, by omega⟩

/-- A `memOKA` write list leaves every protected word alone. -/
theorem memOKA_prot {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    (s : MachineState) (hrel : RelOK rel s) (A : Nat) (hA : A < 2 ^ 64) (hp : Prot A) :
    ∀ p ∈ ws, BitVec.ofNat 64 A ≠ p.1.eval s := by
  intro p hp'
  have hps : ∀ a ∈ pSlots, a < WIT := by decide
  rcases memOKA_cases h hp' with ⟨r, hr, hb, hoff⟩ | ⟨hb, hc⟩
  · obtain ⟨_, hge⟩ := relWrite_ge hrel hr hb hoff
    intro heq
    have : (p.1.eval s).toNat = A := by rw [← heq, ofNat_toNat_lt _ hA]
    rcases hp with h1 | h1 | h1 | ⟨_, h1⟩
    · have := hps A h1; unfold WLO at hge; omega
    · unfold WLO WIT at hge; omega
    · unfold WLO WIT at hge; omega
    · omega
  · obtain ⟨⟨b, off⟩, v⟩ := p
    simp only at hb; subst hb
    simp only [Addr.eval]
    intro heq
    have hoff : off.toNat = A := by rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
    simp only [hoff] at hc
    rcases hc with h1 | ⟨h2, -⟩ | ⟨-, h4⟩
    · obtain ⟨s1, s2, s3, s4, -⟩ := safeAddr_spec h1
      rcases hp with h | h | h | ⟨h, -⟩
      · exact s2 h
      · exact s3 h
      · exact s4 h
      · omega
    · rcases hp with h | h | h | ⟨h, -⟩
      · rw [h2] at h; unfold CTRW at h; simp [pSlots] at h
      · unfold CTRW at h2; omega
      · unfold CTRW at h2; omega
      · unfold CTRW WIT at *; omega
    · rcases hp with h | h | h | ⟨-, h'⟩
      · have := hps A h; unfold WLO WIT at *; omega
      · unfold WLO WIT at h4; omega
      · unfold WLO WIT at h4; omega
      · omega

/-- The counter word after a `memOKA` write list: untouched or written by a low-half `sw`. -/
theorem memOKA_ctr {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    (s : MachineState) (hrel : RelOK rel s) :
    (memEval s ws (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = (s.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 := by
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    have hp := memOKA_cases h (List.mem_cons_self ..)
    have hws : memOKA allow rel ws = true := by
      simp only [memOKA, List.all_cons, Bool.and_eq_true] at h; simpa [memOKA] using h.2
    have ih' := ih hws
    rw [memEval_cons]
    by_cases he : BitVec.ofNat 64 CTRW = p.1.eval s
    · rw [if_pos he]
      rcases hp with ⟨r, hr, hb, hoff⟩ | ⟨hb, hc⟩
      · obtain ⟨_, hge⟩ := relWrite_ge hrel hr hb hoff
        rw [← he, ofNat_toNat_lt _ (by unfold CTRW; omega)] at hge
        unfold CTRW WLO WIT at hge; omega
      · obtain ⟨⟨b, off⟩, v⟩ := p
        simp only at hb; subst hb
        have hoff : off.toNat = CTRW := by
          simp only [Addr.eval] at he; rw [← he, BitVec.toNat_ofNat]; rfl
        simp only [hoff] at hc
        rcases hc with h1 | ⟨-, h2⟩ | ⟨-, h3⟩
        · exact absurd rfl (safeAddr_spec h1).2.2.2.2
        · unfold isLowW at h2
          split at h2
          · rename_i k x
            simp only [beq_iff_eq] at h2
            have hk : k = BitVec.ofNat 64 CTRW := by
              apply BitVec.eq_of_toNat_eq; rw [h2, BitVec.toNat_ofNat]; rfl
            subst hk
            show (StoreKind.merge .w (s.getMem (BitVec.ofNat 64 CTRW)) 0 (x.eval s)).toNat / 2 ^ 32 = _
            rw [merge_w0_high]
            have := (s.getMem (BitVec.ofNat 64 CTRW)).isLt
            omega
          · cases h2
        · unfold WLO WIT CTRW at h3; omega
    · rw [if_neg he]; exact ih'

/-- A `memOKA` write list leaves every word at or above `2^23 + 4096` alone (the embedded data). -/
theorem memOKA_data {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    (s : MachineState) (hrel : RelOK rel s) (A : Nat) (hA : 2 ^ 23 + 4096 ≤ A) (hA' : A < 2 ^ 64) :
    ∀ p ∈ ws, BitVec.ofNat 64 A ≠ p.1.eval s := by
  intro p hp'
  rcases memOKA_cases h hp' with ⟨r, hr, hb, hoff⟩ | ⟨hb, hc⟩
  · obtain ⟨hev, -⟩ := relWrite_ge hrel hr hb hoff
    have h2 := (hrel r hr).2
    intro heq
    have : (p.1.eval s).toNat = A := by rw [← heq, ofNat_toNat_lt _ hA']
    omega
  · obtain ⟨⟨b, off⟩, v⟩ := p
    simp only at hb; subst hb
    simp only [Addr.eval]
    intro heq
    have hoff : off.toNat = A := by rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA']
    simp only [hoff] at hc
    rcases hc with h1 | ⟨h2, -⟩ | ⟨-, h4⟩
    · have := (safeAddr_spec h1).1; unfold WIT at this; omega
    · unfold CTRW at h2; omega
    · omega

theorem DATA_ge (k : Nat) (hk : k < 12) : 2 ^ 23 + 4096 ≤ DATA + 8 * k ∧ DATA + 8 * k + 8 ≤ 2 ^ 24 := by
  unfold DATA; omega

/-- One embedded doubleword, at a given address with a given value. -/
theorem DataOK.word {s : MachineState} (h : DataOK s) (k : Nat) (hk : k < 12) (v : Nat)
    (hv : dataWords.getD k 0 = v) (a : Nat) (ha : a = DATA + 8 * k) :
    s.getMem (BitVec.ofNat 64 a) = BitVec.ofNat 64 v := by
  subst hv ha; exact h k hk

theorem Glob_toState_allow {gk0 gk : List (Reg × Word)} {w : WBytes} {pk : Digest} {s : MachineState}
    {allow : List Nat} {rel : List Reg}
    (hG : Glob gk0 w pk s) (σ : SymState) (pc : Word) (hm : memOKA allow rel σ.mem = true)
    (hrel : RelOK rel s) (hr : regsOK gk σ.regs = true) : Glob gk w pk (σ.toState s pc) := by
  obtain ⟨-, h0, h2, h3, h4, h5⟩ := hG
  have fr : ∀ A, A < 2 ^ 64 → Prot A →
      (σ.toState s pc).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hp
    rw [SymState.toState_getMem]
    exact memEval_frame s _ _ (memOKA_prot hm s hrel A hA hp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have := List.all_eq_true.mp hr p hp
    rw [SymState.toState_getReg, E.beq_eq this]; rfl
  · intro j hj
    rw [fr _ (by unfold WIT; omega) (Or.inr (Or.inr (Or.inr ⟨by unfold WIT; omega, by unfold WLO WIT; omega⟩)))]
    exact h0 j hj
  · exact ⟨(fr 0xA0 (by omega) (by simp [Prot])).trans h2.1, (fr 0xA8 (by omega) (by simp [Prot])).trans h2.2⟩
  · intro a ha
    have : a < 2 ^ 64 := by simp [pSlots] at ha; omega
    rw [fr a this (Or.inl ha)]; exact h3 a ha
  · show (memEval s σ.mem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
    rw [memOKA_ctr hm s hrel]; exact h4
  · apply h5.congr
    intro A hA hAend
    rw [SymState.toState_getMem, memEval_frame s _ _
      (memOKA_data hm s hrel _ (by unfold TAB at hA; omega) (by omega))]

theorem Glob_toState {gk0 gk : List (Reg × Word)} {w : WBytes} {pk : Digest} {s : MachineState}
    (hG : Glob gk0 w pk s) (σ : SymState) (pc : Word) (hm : memOK σ.mem = true)
    (hr : regsOK gk σ.regs = true) : Glob gk w pk (σ.toState s pc) :=
  Glob_toState_allow hG σ pc hm (RelOK.nil s) hr

/-- **General witness frame**: the witness words a run does not write stay original. -/
theorem Orig_toState {w : WBytes} {s : MachineState} {P P' : Nat → Prop} (hO : Orig w P s)
    (σ : SymState) (pc : Word)
    (hfr : ∀ o, o < WX → P' o → P o ∧ ∀ p ∈ σ.mem, BitVec.ofNat 64 (WIT + o) ≠ p.1.eval s) :
    Orig w P' (σ.toState s pc) := by
  intro j h1 h2
  obtain ⟨hp, hne⟩ := hfr (8 * j) h1 h2
  rw [SymState.toState_getMem, memEval_frame s _ _ hne]
  exact hO j h1 hp

/-- A run with constant writes only: the witness words outside `allow` stay original. -/
theorem Orig_toState_const {w : WBytes} {s : MachineState} {P : Nat → Prop} {allow : List Nat}
    (hO : Orig w P s) (σ : SymState) (pc : Word) (hm : memOKA allow [] σ.mem = true) :
    Orig w (fun o => P o ∧ WIT + o ∉ allow) (σ.toState s pc) := by
  refine Orig_toState hO σ pc (fun o ho ⟨hp, hna⟩ => ⟨hp, fun p hp' heq => ?_⟩)
  rcases memOKA_cases hm hp' with ⟨r, hr, -⟩ | ⟨hb, hc⟩
  · simp at hr
  · obtain ⟨⟨b, off⟩, v⟩ := p
    simp only at hb; subst hb
    simp only [Addr.eval] at heq
    have hoff : off.toNat = WIT + o := by
      rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold WIT WX at *; omega)]
    simp only [hoff] at hc
    rcases hc with h1 | ⟨h2, -⟩ | ⟨h3, -⟩
    · have := (safeAddr_spec h1).1; omega
    · unfold CTRW WIT at h2; omega
    · exact hna h3

/-- A run without witness writes keeps the whole witness. -/
theorem WitAll_toState {w : WBytes} {s : MachineState} (hW : WitAll w s) (σ : SymState)
    (pc : Word) (hm : memOK σ.mem = true) : WitAll w (σ.toState s pc) := by
  have := Orig_toState_const (hW.orig (fun _ => True)) σ pc hm
  intro j hj
  exact this j hj ⟨trivial, by simp⟩

theorem Orig_writeHash {w : WBytes} {s : MachineState} {P : Nat → Prop} (hO : Orig w P s)
    (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    Orig w (fun o => P o ∧ (WIT + o + 8 ≤ d ∨ d + 32 ≤ WIT + o)) (writeHash s ans) := by
  intro j h1 ⟨h2, h3⟩
  rw [writeHash_frame s ans d _ hd (by unfold WIT WX at *; omega) (by omega) h3]
  exact hO j h1 h2

theorem WitAll_writeHash {w : WBytes} {s : MachineState} (hW : WitAll w s)
    (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d)
    (hlow : d + 32 ≤ WIT) : WitAll w (writeHash s ans) := by
  intro j hj
  rw [writeHash_frame s ans d _ hd (by unfold WIT WX at *; omega) (by unfold WIT at hlow; omega)
    (Or.inr (by unfold WIT at *; omega))]
  exact hW j hj

/-- A hash destination (32 bytes) that no protected word occupies. -/
def safeDest (d : Nat) : Bool :=
  decide (d % 8 = 0) && decide (d + 32 ≤ 2 ^ 23) &&
    (pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j)).all
      (fun q => decide (q + 8 ≤ d ∨ d + 32 ≤ q))

/-- Every aligned destination in the witness area past the header is safe. -/
theorem safeDest_hi (d : Nat) (h : WLO ≤ d) (h8 : d % 8 = 0) (hm : d + 32 ≤ 2 ^ 23) :
    safeDest d = true := by
  simp only [safeDest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, MEMORY_BYTES]
  refine ⟨⟨by simpa using h8, by simpa using hm⟩, fun q hq => Or.inl ?_⟩
  simp only [List.mem_append, List.mem_map, List.mem_range, pSlots, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  unfold WLO WIT CTRW at *
  rcases hq with ((h1 | h1 | h1) | h1 | h1 | h1) | ⟨j, hj, rfl⟩ <;> omega

theorem Glob_writeHash {gk : List (Reg × Word)} {w : WBytes} {pk : Digest} {s : MachineState}
    (hG : Glob gk w pk s) (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d)
    (hsafe : safeDest d = true) : Glob gk w pk (writeHash s ans) := by
  obtain ⟨h1, h0, h2, h3, h4, h5⟩ := hG
  simp only [safeDest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsafe
  obtain ⟨⟨-, hd1⟩, hd2⟩ := hsafe
  have hd1' : d + 32 ≤ 2 ^ 24 := by omega
  have fr : ∀ A, A < 2 ^ 64 → (A + 8 ≤ d ∨ d + 32 ≤ A) →
      (writeHash s ans).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hp
    rw [writeHash_getMem_ofNat s ans d A hd hA (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hps : ∀ a ∈ pSlots, a < WIT := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp; rw [writeHash_getReg]; exact h1 p hp
  · intro j hj
    have hm : WIT + 8 * j ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j) :=
      List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    rw [fr (WIT + 8 * j) (by unfold WIT; omega) (hd2 _ hm)]
    exact h0 j hj
  · have m0 : (0xA0 : Nat) ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j) := by
      simp
    have m8 : (0xA8 : Nat) ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j) := by
      simp
    exact ⟨(fr 0xA0 (by omega) (hd2 _ m0)).trans h2.1, (fr 0xA8 (by omega) (hd2 _ m8)).trans h2.2⟩
  · intro a ha
    have hm : a ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j) :=
      List.mem_append_left _ (List.mem_append_left _ ha)
    have := hps a ha
    rw [fr a (by unfold WIT at this; omega) (hd2 _ hm)]; exact h3 a ha
  · have mc : CTRW ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j) := by simp
    show ((writeHash s ans).getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
    rw [fr CTRW (by unfold CTRW; omega) (hd2 _ mc)]; exact h4
  · apply h5.congr
    intro A hA hAend
    exact fr A (by omega) (Or.inr (by unfold TAB at hA; omega))

theorem Known_writeHash {known : List (Reg × Word)} {s : MachineState}
    (h : ∀ p ∈ known, s.getReg p.1 = p.2) (a : BitVec 256) : ∀ p ∈ known, (writeHash s a).getReg p.1 = p.2 := by
  intro p hp; rw [writeHash_getReg]; exact h p hp

end SigGolfCandidate.T3M.Verify
