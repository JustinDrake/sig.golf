import SigGolfCandidate.T3M.Sign.Blocks
import SigGolfCandidate.T3M.Keygen.Init

/-!
# Sign: scratch map, bounded hash combinators, word lemmas

* the sign scratch buffers of `ske/skeasm.py` (the shared ones `PRIV .. REGION` are K's);
* `TBSim` (bounded refinement) versions of the one-`ECALL` combinators (`publicHash`, `shortHash`,
  private coordinates, `privateMac`, `privateNonce`, `privatePair`, `mask`), `TBSim.pure_steps`, `TBSim.of_eq`;
* `Failed t` : the `fail` stub reached `HALT(1)`; `fail_spec`;
* doubleword views: `bv256_eq_iff`, `bytesToWordLE_bytes` (the loader's doublewords of any input buffer).
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Spec publicHash shortHash privateHash privatePair privateMac privateNonce mask
  privateInput header pad64 Coordinate HashOutput Digest Region)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## The sign scratch map (`ske/skeasm.py`) -/

/-- The message. -/
abbrev MSG : Nat := 0x40
/-- The secret key. -/
abbrev SK : Nat := 0x80
/-- The signature output (5,824 bytes). -/
abbrev SIG : Nat := 0x7000
/-- The cache input (`tag | region`). -/
abbrev CACHE : Nat := 0x9000
/-- `S0 | T7 | S1 | 0^16 | m | 0^32`: the nonce block. -/
abbrev NONCE : Nat := 0x20080
/-- The nonce output (rho = low 16 bytes). -/
abbrev RHOOUT : Nat := 0x20100
/-- `rho | T12(counter) | m`: the digest block. -/
abbrev DIG : Nat := 0x20120
/-- The digest output `N` (+8 readable zero bytes). -/
abbrev NBUF : Nat := 0x20160
/-- `M | T4 | LE32 counter | 0^28`: the encoding block. -/
abbrev ENC : Nat := 0x20260
/-- The encoding output. -/
abbrev EOUT : Nat := 0x202A0
/-- `0^16 | T9 | secret | 0^16`: the FTS leaf block. -/
abbrev FLEAF : Nat := 0x202C0
/-- The FTS leaf output. -/
abbrev LFOUT : Nat := 0x20300
/-- `root0 | T11 | root1 .. root6`: the forest block. -/
abbrev FOREST : Nat := 0x20320
/-- The forest pk output. -/
abbrev FOUT : Nat := 0x203A0
/-- The recomputed MAC tag. -/
abbrev MACOUT : Nat := 0x203E0
/-- The saved cache tag. -/
abbrev TAG : Nat := 0x20400
/-- The digits of the selected leaf (bytes). -/
abbrev DIGITS : Nat := 0x20420
/-- The selection rows: 7 x 3 doublewords `bucket * 256 + x_j`. -/
abbrev SEL : Nat := 0x204A0
/-- The hypertree index `N mod 2^31`. -/
abbrev IDXV : Nat := 0x20550
/-- The lower WOTS tree arena (node `k` at `LOW + 16 k`). -/
abbrev LOW : Nat := 0x21000
/-- One FTS coordinate tree arena (node `k` at `FTS + 16 k`). -/
abbrev FTS : Nat := 0x30000
/-- The FTS secrets (leaf `s` at `SEC + 16 s`). -/
abbrev SEC : Nat := 0x40000

/-- `omega` after unfolding every scratch and buffer address. -/
macro "sg_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP, MACBLK,
    REGION, MSG, SK, SIG, CACHE, NONCE, RHOOUT, DIG, NBUF, ENC, EOUT, FLEAF, LFOUT, FOREST, FOUT, MACOUT, TAG,
    DIGITS, SEL, IDXV, LOW, FTS, SEC] at *); omega))

/-! ## Bounded combinators -/

section tb
variable {α β : Type} {image : Image} {sk : BitVec 256}

theorem TBSim.pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : TBSim image sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ

theorem TBSim.of_eq {s : MachineState} {W W' : Nat} {p q : M α} {Q : α → MachineState → Prop}
    (h : TBSim image sk s W p Q) (he : p = q) (hW : W = W') : TBSim image sk s W' q Q := by
  subst he hW; exact h

theorem TBSim.post_steps {s : MachineState} {W k c : Nat} {p : M α} {Q Q' : α → MachineState → Prop}
    (h : TBSim image sk s W p Q) (hs : ∀ a t, Q a t → ∃ u, Steps image t k c u ∧ Q' a u) :
    TBSim image sk s (W + c) p Q' :=
  TBSim.of_eq (TBSim.bind (f := fun a => (Pure.pure a : M α)) h
    (fun a t ht => by obtain ⟨u, hu, hq⟩ := hs a t ht; exact TBSim.pure_steps hu hq)) (bind_pure p) rfl

/-- One HASH `ECALL` answering a public query `publicHash input`. -/
theorem TBSim.publicHash_bind {s : MachineState} {input : List UInt8} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (pad64 input)).blocks + W) (publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h

/-- One HASH `ECALL` answering `shortHash input` (the low 16 bytes). -/
theorem TBSim.shortHash_bind {s : MachineState} {input : List UInt8} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * (toQ (pad64 input)).blocks + W) (shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this

/-- One HASH `ECALL` answering a private coordinate. -/
theorem TBSim.privateHash_bind {s : MachineState} {co : Coordinate} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk co))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (privateInput sk co)).blocks + W) (privateHash co >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_privateHash]
  exact Sim.query_bind hf ht0 hv hq h

/-- One HASH `ECALL` answering the 513-block MAC. -/
theorem TBSim.privateMac_bind {s : MachineState} {region : Region} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk (.inr (.inr region))))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * 513 + W) (privateMac region >>= f) Q := by
  have hb : (toQ (privateInput sk (.inr (.inr region)))).blocks = 513 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_mac_length]
  exact TBSim.of_eq (TBSim.privateHash_bind hf ht0 hv hq h) rfl (by rw [hb])

/-- One HASH `ECALL` answering the nonce (`privateNonce`, the low 16 bytes; two blocks). -/
theorem TBSim.privateNonce_bind {s : MachineState} {m : T3.Message} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk (.inr (.inl m))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * 2 + W) (privateNonce m >>= f) Q := by
  have hb : (toQ (privateInput sk (.inr (.inl m)))).blocks = 2 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_nonce_eq]
    simp [bytesLE_length, SigGolfCandidate.T3.zero16]
  have : privateNonce m >>= f = privateHash (.inr (.inl m)) >>= fun a => f (a.extractLsb' 0 128) := by
    unfold privateNonce; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.of_eq (TBSim.privateHash_bind hf ht0 hv hq h) rfl (by rw [hb])

/-- One HASH `ECALL` answering `privatePair` (both halves; one block). -/
theorem TBSim.privatePair_bind {s : MachineState} {tag lay tree position index : Nat} {W : Nat}
    {f : Digest × Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header tag lay tree position index))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W
      (f (a.extractLsb' 0 128, a.extractLsb' 128 128)) Q) :
    TBSim image sk s (8 + W) (privatePair tag lay tree position index >>= f) Q := by
  have hb : (toQ (privateInput sk (.inl (header tag lay tree position index)))).blocks = 1 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_tweak_length]
  have : privatePair tag lay tree position index >>= f =
      privateHash (.inl (header tag lay tree position index)) >>= fun a =>
        f (a.extractLsb' 0 128, a.extractLsb' 128 128) := by
    unfold privatePair; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.of_eq (TBSim.privateHash_bind hf ht0 hv hq h) rfl (by rw [hb])

/-- One HASH `ECALL` answering `mask level index` (the low half of a tag-13 pair). -/
theorem TBSim.mask_bind {s : MachineState} {level index : Nat} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header 13 0 0 level index))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 + W) (mask level index >>= f) Q := by
  have : mask level index >>= f = privatePair 13 0 0 level index >>= fun x => f x.1 := by
    unfold mask; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.privatePair_bind hf ht0 hv hq h

end tb

/-! ## The `fail` stub -/

/-- `HALT(1)` reached at the `fail` stub's `ECALL` (word 545). -/
structure Failed (t : MachineState) : Prop where
  pc : t.pc = pcOf 545
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1

theorem fetch_545 (s : MachineState) (hpc : s.pc = pcOf 545) : fetch image s = some (.base .ECALL) :=
  (codeAt_545.fetch s hpc).trans rfl

/-- `fail` (word 543): `t0 := 1`, `a0 := 1`, then the `HALT` `ECALL`. -/
theorem fail_spec (s : MachineState) (hpc : s.pc = pcOf 543) :
    ∃ t, Steps image s 2 2 t ∧ Failed t ∧ RegsExcept s t [.x5, .x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_543 codeAt_543 s hpc (by simp [blk_543.res, rv_simp]), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [blk_543.res, E.eval]
  · simp [blk_543.res, rv_simp]
  · simp [blk_543.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_543.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_543.res, rv_simp]

/-! ## Doubleword views -/

/-- Two 256-bit values are equal iff their four doublewords are. -/
theorem bv256_eq_iff (x y : BitVec 256) :
    x = y ↔ (x.extractLsb' 0 64 = y.extractLsb' 0 64 ∧ x.extractLsb' 64 64 = y.extractLsb' 64 64 ∧
      x.extractLsb' 128 64 = y.extractLsb' 128 64 ∧ x.extractLsb' 192 64 = y.extractLsb' 192 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    apply BitVec.eq_of_toNat_eq
    have e0 := congrArg BitVec.toNat h0; have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2; have e3 := congrArg BitVec.toNat h3
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at e0 e1 e2 e3
    have hx := x.isLt; have hy := y.isLt
    simp only [Nat.reducePow] at e0 e1 e2 e3 hx hy
    omega

/-- Doubleword `j` of a loaded input buffer (`writeBytesAsWords` of `bytes x`). -/
theorem bytesToWordLE_bytes {n : Nat} (x : Bytes n) (j : Nat) (hj : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  apply Keygen.word_ext_bytes
  intro i hi
  rw [Keygen.extractByte_bytesToWordLE _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [Keygen.extractByte_toNat']
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show 8 * j + i < n by omega), if_pos hi, Option.map_some,
    Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (8 * j + i) = 64 * j + 8 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (64 * j) = y
  interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.div_one] <;> omega

end SigGolfCandidate.T3M.Sign
