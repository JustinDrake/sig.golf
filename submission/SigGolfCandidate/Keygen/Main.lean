import SigGolfCandidate.Keygen.Mask
import SigGolfCandidate.Keygen.Output

/-!
# `keygen` refines `keygenRef`

`keygen_run` : for every secret key `sk`,
`submission.run .keygen sk = (fun o => ⟨some o, true, 31022558, 653312, 673792⟩) <$> keygenRef sk`:
the machine makes exactly the oracle queries of `keygenRef sk` (in order), outputs its public key
and cache, and always takes 31022558 cycles, 653312 calls and 673792 compressions.
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Mem OracleComp

/-- The initial state of `keygen`. -/
def kInit (sk : SecretKey) : MachineState :=
  let blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  ((blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase image)) image.data).writeBytesAsWords
    (BitVec.ofNat 64 0x80) (bytes sk)).setReg .x2 (BitVec.ofNat 64 (dataBase image))

theorem kInit_eq (sk : SecretKey) : initialState submission .keygen sk = some (kInit sk) := by
  unfold initialState
  rw [if_pos (submission_admissible.2 .keygen)]
  rfl

theorem kInit_pc (sk : SecretKey) : (kInit sk).pc = pcOf 0 := by
  rw [initialState_pc _ _ _ _ (kInit_eq sk)]; rfl

theorem kInit_x5 (sk : SecretKey) : (kInit sk).getReg .x5 = 0 := by
  simp only [kInit, getReg_setReg', MachineState.getReg_writeBytesAsWords]
  rfl

theorem kInit_mem (sk : SecretKey) (A : Nat) (hA : A < 2 ^ 64) :
    (kInit sk).getMem (BitVec.ofNat 64 A) =
      if 128 ≤ A ∧ A < 160 ∧ (A - 128) % 8 = 0 then
        BitVec.ofNat 64 (leNat (((bytes sk).drop (A - 128)).take 8))
      else 0 := by
  have hl : (bytes sk).length = 32 := by simp [SigGolfCandidate.Legacy.bytes]
  unfold kInit
  simp only [MachineState.getMem_setReg]
  rw [getMem_writeBytesAsWords _ _ _ _ (by rw [hl]; norm_num) hA, hl, bytesToWordLE_eq]
  simp only [show image.data = [] from rfl, MachineState.writeBytesAsWords_nil]
  rfl

/-- The secret-key doublewords of the initial state. -/
def kW (sk : SecretKey) : List Word :=
  [(kInit sk).getMem (BitVec.ofNat 64 128), (kInit sk).getMem (BitVec.ofNat 64 136),
    (kInit sk).getMem (BitVec.ofNat 64 144), (kInit sk).getMem (BitVec.ofNat 64 152)]

theorem leNat_take_drop8 (l : List Byte) (h : 8 ≤ l.length) :
    leNat l = leNat (l.take 8) + 2 ^ 64 * leNat (l.drop 8) := by
  conv_lhs => rw [← List.take_append_drop 8 l]
  rw [leNat_append, List.length_take, Nat.min_eq_left h]

theorem leNat_take8_lt (l : List Byte) : leNat (l.take 8) < 2 ^ 64 := by
  have := leNat_lt (l.take 8)
  have h2 : (l.take 8).length ≤ 8 := by simp
  calc leNat (l.take 8) < 256 ^ (l.take 8).length := this
    _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) h2
    _ = 2 ^ 64 := by norm_num

theorem kW_skOk (sk : SecretKey) : SkOk (kW sk) (toList sk) := by
  have hl : (toList sk).length = 32 := length_toList sk
  refine ⟨hl, ?_⟩
  simp only [kW, List.getD_cons_zero, List.getD_cons_succ]
  rw [kInit_mem sk 128 (by norm_num), if_pos (by decide), kInit_mem sk 136 (by norm_num),
    if_pos (by decide), kInit_mem sk 144 (by norm_num), if_pos (by decide),
    kInit_mem sk 152 (by norm_num), if_pos (by decide)]
  simp only [Nat.reduceSub]
  have e := fun (k : Nat) => toNat_ofNat_lt (leNat_take8_lt ((bytes sk).drop k))
  rw [e, e, e, e]
  simp only [List.drop_zero]
  have s1 := leNat_take_drop8 (toList sk) (by omega)
  have s2 := leNat_take_drop8 ((toList sk).drop 8) (by simp [hl])
  have s3 := leNat_take_drop8 ((toList sk).drop 16) (by simp [hl])
  have s4 : ((toList sk).drop 24).take 8 = (toList sk).drop 24 := List.take_of_length_le (by simp [hl])
  simp only [List.drop_drop, Nat.reduceAdd] at s2 s3
  rw [s1, s2, s3, ← s4]
  rfl

theorem leaves_xsim (sk : SecretKey) :
    XSim image (kInit sk) (38 + sumTo (fun _ => 10976) (2 ^ 11)) (38 + sumTo (fun _ => 14150) (2 ^ 11))
      (sumTo (fun _ => 316) (2 ^ 11)) (sumTo (fun _ => 326) (2 ^ 11))
      (buildLeaves (toList sk) 0 0 11 0 [])
      (fun p u => LCtx (kW sk) (2 ^ 11) p.1 u ∧ u.pc = if 2 ^ 11 < 2048 then pcOf 25 else pcOf 76) := by
  obtain ⟨t, hst, tpc, t8, t30, t9, t19, t17, t20, t5, t26, t1728, t1736, t1744, t1752, t1696, t192,
    t832, t224, t232, tfr⟩ := spec_0 (kInit sk) (kInit_pc sk) (by rw [kInit_mem sk 1696 (by norm_num)]; rfl)
      (by rw [kInit_mem sk 192 (by norm_num)]; rfl)
  have zi : ∀ A < 2 ^ 64, (A < 128 ∨ 160 ≤ A) → (kInit sk).getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA h; rw [kInit_mem sk A hA, if_neg (by omega)]
  have hb : Base (kW sk) t := by
    refine ⟨by rw [t5, kInit_x5], t8, t30, t9, t26, ?_, ?_, ?_, t832, ?_⟩
    · intro k hk
      interval_cases k
      · exact t1728
      · exact t1736
      · exact t1744
      · exact t1752
    · intro k hk
      rw [tfr _ (by omega) (by simp; omega)]
      interval_cases k <;> rfl
    · intro A hA
      simp [zeroKeys] at hA
      by_cases h224 : A = 224
      · subst h224; exact t224
      by_cases h232 : A = 232
      · subst h232; exact t232
      rw [tfr A (by omega) (by simp; omega), zi A (by omega) (by omega)]
    · intro A h1 h2
      rw [tfr A (by omega) (by simp; omega), zi A (by omega) (by omega)]
  have h0 : LCtx (kW sk) 0 [] t := ⟨hb, t1696, t192, t17, t19, t20, rfl, Vals.nil t REGION⟩
  unfold buildLeaves
  refine XSim.steps hst (XSim.foldlM_range (2 ^ 11) _ ([], [])
    (fun e acc u => LCtx (kW sk) e acc.1 u ∧ u.pc = if e < 2048 then pcOf 25 else pcOf 76)
    (fun _ => 10976) (fun _ => 14150) (fun _ => 316) (fun _ => 326)
    (fun e he acc u hu => leaf_xsim (kW sk) (toList sk) (kW_skOk sk) e (by norm_num at he; omega)
      acc u hu.1 (by rw [hu.2, if_pos (by norm_num at he; omega)])) ⟨h0, by rw [tpc]; rfl⟩)

/-- The tree levels `1 .. 11`, from the leaves in the region. -/
theorem levels_xsim (W : List Word) (leaves : List Val) (u : MachineState)
    (h : LCtx W 2048 leaves u) (hpc : u.pc = pcOf 76) :
    XSim image u (1 + sumTo (fun k => 14 + 2 ^ (10 - k) * 23) 11)
      (1 + sumTo (fun k => 14 + 2 ^ (10 - k) * 30) 11) (sumTo (fun k => 2 ^ (10 - k)) 11)
      (sumTo (fun k => 2 ^ (10 - k)) 11)
      (buildAllLevels (nodeInput 0 0) 11 leaves)
      (fun levels w => VCtx W 11 levels w ∧ w.pc = pcOf 107) := by
  obtain ⟨v, vst, vpc, v15, vun, vfr⟩ := spec_76 u hpc
  have h0 : VCtx W 0 [leaves] v := by
    refine ⟨h.base.frame (fun r hr => vun r (by rcases hr with h | h | h | h | h <;> simp [h])) vfr
      (by simp), v15, ?_, ?_, ⟨rfl, fun i hi => ?_, fun L hL x hx => ?_⟩, ?_⟩
    · rw [vun _ (by simp), h.r17]; rfl
    · rw [vun _ (by simp), h.r19]; rfl
    · rw [show i = 0 by omega]; simp [h.len]
    · simp at hL; subst hL; exact h.lv.1 x hx
    · rw [List.flatten_singleton]
      exact ⟨h.lv.1, fun i hi => (h.lv.2 i hi).frame vfr (by rw [h.len] at hi; unfold REGION; omega)
        (by simp)⟩
  unfold buildAllLevels
  refine (XSim.steps vst (XSim.foldlM_range' 1 11 _ [leaves]
      (fun k levels w => VCtx W k levels w ∧ w.pc = if k < 11 then pcOf 77 else pcOf 107)
      (fun k => 14 + 2 ^ (10 - k) * 23) (fun k => 14 + 2 ^ (10 - k) * 30) (fun k => 2 ^ (10 - k))
      (fun k => 2 ^ (10 - k))
      (fun k hk levels w hw => level_xsim W k hk levels w hw.1 (by rw [hw.2, if_pos hk]))
      ⟨h0, by rw [vpc]; rfl⟩)).mono (fun levels w hw => ⟨hw.1, by rw [hw.2]; rfl⟩)

/-- MAC round context: `i` key answers used, the tag words `0 .. 2 i - 1` stored. -/
structure MCtx (W : List Word) (root : Val) (masked : List Val) (i : Nat) (tag : List Nat)
    (t : MachineState) : Prop where
  r5 : t.getReg .x5 = 0
  r18 : t.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1)
  r19 : t.getReg .x19 = BitVec.ofNat 64 0x14B00
  r21 : t.getReg .x21 = BitVec.ofNat 64 i
  r25 : t.getReg .x25 = BitVec.ofNat 64 (0x14B00 + 16 * i)
  tw : t.getMem (BitVec.ofNat 64 1696) = BitVec.ofNat 64 3585
  pz0 : t.getMem (BitVec.ofNat 64 1712) = 0
  pz1 : t.getMem (BitVec.ofNat 64 1720) = 0
  sk : ∀ k < 4, t.getMem (BitVec.ofNat 64 (1728 + 8 * k)) = W.getD k 0
  pk : ValAt t 160 root
  reg : Vals t REGION masked
  head : ∀ k < 4, t.getMem (BitVec.ofNat 64 (0x4B00 + 8 * k)) = 0
  tlen : tag.length = 2 * i
  tagw : ∀ j < 2 * i, t.getMem (BitVec.ofNat 64 (0x14B00 + 8 * j)) = BitVec.ofNat 64 (tag.getD j 0)
  tail : ∀ A, 0x14B00 + 16 * i ≤ A → A < 0x24B00 → A % 8 = 0 → t.getMem (BitVec.ofNat 64 A) = 0

/-- One MAC round: key query `i`, a pass per half of the answer, both tag words stored. -/
theorem round_xsim (W : List Word) (S : List Byte) (hS : SkOk W S) (root : Val) (masked : List Val)
    (hml : masked.length = 4094) (i : Nat) (hi : i < 3) (tag : List Nat) (t : MachineState)
    (h : MCtx W root masked i tag t) (hpc : t.pc = pcOf 227) :
    XSim image t (5 + (1 + 425812)) (5 + (8 * 1 + 622324)) 1 1 (H (macKeyInput S i))
      (fun a u => MCtx W root masked (i + 1) (tag ++ macWords a (chunks32 masked.flatten)) u ∧
        u.pc = if i + 1 < 3 then pcOf 227 else pcOf 321) := by
  have hfl : masked.flatten.length = 65504 := by rw [length_flatten16 _ h.reg.1, hml]
  obtain ⟨u, hst, upc, u10, u11, u12, uun, u1704, ufr⟩ := spec_227 t hpc i hi h.r21
  have um : ∀ A < 2 ^ 64, A ≠ 1704 → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hne => ufr A hA (by simpa using hne)
  have hx : (macKeyInput S i).length = 64 := by simp [macKeyInput, thInput, hS.1]
  have hq : hashInput u = pad64 (macKeyInput S i) := by
    refine hashInput_eq_pad64 u 0 1696 _ (by rw [u11]) (by norm_num) u10
      (by norm_num) (by norm_num) (by omega) (by omega) ?_
    rw [readWords8]
    simp only [wordsToNat]
    simp only [Nat.reduceAdd]
    rw [um 1696 (by norm_num) (by norm_num), h.tw, u1704, um 1712 (by norm_num) (by norm_num), h.pz0,
      um 1720 (by norm_num) (by norm_num), h.pz1, um 1728 (by norm_num) (by norm_num),
      um 1736 (by norm_num) (by norm_num), um 1744 (by norm_num) (by norm_num),
      um 1752 (by norm_num) (by norm_num), h.sk 0 (by norm_num), h.sk 1 (by norm_num),
      h.sk 2 (by norm_num), h.sk 3 (by norm_num)]
    have hW := hS.2
    simp only [macKeyInput, thInput, leNat_append, List.length_append, length_tweak,
      P, leNat_zeros, length_zeros, leNat_tweak0 14 0 _ _ (by norm_num) (by norm_num)]
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.reducePow, Nat.reduceMul,
      Nat.reduceAdd] at hW ⊢
    omega
  have hblk : (addrFmt (macKeyInput S i)).blocks = 1 := by
    rw [addrFmt_macKeyInput, blocks_fmt (macKeyInput S i) (not_digest_thInput 14 0 0 0 i _ (by decide))
      (not_padChain_thInput 14 0 0 0 i _ (by decide))]
    simp [Query.blocks, pad64, padBlocks, hx]
  have hq' : hashInput u = addrFmt (macKeyInput S i) :=
    hq.trans (addrFmt_thInput 14 0 0 0 i S (by decide)).symm
  have hv : hashArgumentsValid u = true :=
    hashArgs_const u 1696 64 320 u10 u11 u12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  refine (XSim.steps hst (XSim.bind (k₂ := 425812) (c₂ := 622324) (n₂ := 0) (b₂ := 0)
    (XSim.query ((codeAt_232.fetch u upc).trans rfl)
      (by rw [uun _ (by simp) (by simp) (by simp) (by simp)]; exact h.r5) hv hq')
    (fun a w hw => ?_))).of_eq (by simp only [H, bind_pure]; rfl) (by rfl) (by rw [hblk]) (by rfl)
    (by rw [hblk])
  subst hw
  have wpc : (writeHash u a).pc = BitVec.ofNat 64 (0x1000 + 4 * 233) := by rw [pc_writeHash, upc]; rfl
  have wm : ∀ A < 2 ^ 64, (writeHash u a).getMem (BitVec.ofNat 64 A) =
      if A = 320 then a.extractLsb' 0 64 else if A = 320 + 8 then a.extractLsb' 64 64
      else if A = 320 + 16 then a.extractLsb' 128 64 else if A = 320 + 24 then a.extractLsb' 192 64
      else u.getMem (BitVec.ofNat 64 A) :=
    fun A hA => getMem_writeHash u a 320 A u12 (by norm_num) hA
  obtain ⟨v, vst, vpc, v22, vun, vfr⟩ := spec_233 (writeHash u a) wpc
  have vm : ∀ A < 2 ^ 64, v.getMem (BitVec.ofNat 64 A) = (writeHash u a).getMem (BitVec.ofNat 64 A) :=
    fun A hA => vfr A hA (by simp)
  have vr : ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x22 → v.getReg r = t.getReg r :=
    fun r h3 h10 h11 h12 h22 => by rw [vun r h22, getReg_writeHash, uun r h3 h10 h11 h12]
  have vmt : ∀ A < 2 ^ 64, A ≠ 1704 → (A + 8 ≤ 320 ∨ 352 ≤ A) →
      v.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2
    rw [vm A hA, wm A hA, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      um A hA h1]
  have hregv : Vals v REGION masked :=
    ⟨h.reg.1, fun k hk => ⟨by
      rw [vmt _ (by rw [hml] at hk; unfold REGION; omega) (by unfold REGION; omega) (by unfold REGION; omega)]
      exact (h.reg.2 k hk).1, by
      rw [vmt _ (by rw [hml] at hk; unfold REGION; omega) (by unfold REGION; omega) (by unfold REGION; omega)]
      exact (h.reg.2 k hk).2⟩⟩
  have hwv : wordsToNat (v.readWords (BitVec.ofNat 64 0x4B20) 8188) = leNat masked.flatten := by
    have := wordsToNat_vals v REGION masked hregv.1 hregv.2
    rwa [hml] at this
  -- first half
  obtain ⟨p1, pst1, ppc1, p14, pun1, pm1⟩ := MacPass.mac_pass_region codeAt_234 v vpc 320 masked.flatten v22
    (by norm_num) (by norm_num)
    (by rw [vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r18)
    (by rw [vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r19) hfl hwv
  rw [vm 320 (by norm_num), wm 320 (by norm_num), if_pos rfl, vm (320 + 8) (by norm_num),
    wm (320 + 8) (by norm_num), if_neg (by norm_num), if_pos rfl, MacPass.tagWord0] at p14
  set T := 0x14B00 + 16 * i with hT
  obtain ⟨q, qst, qpc, q22, qun, qT, qfr⟩ := spec_274 p1 (by rw [ppc1]; rfl) T (by omega) (by omega)
    (by rw [pun1 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r25)
    (by rw [pun1 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact v22)
  have qm : ∀ A < 2 ^ 64, A ≠ T → q.getMem (BitVec.ofNat 64 A) = v.getMem (BitVec.ofNat 64 A) :=
    fun A hA hne => by rw [qfr A hA (by simpa using hne), pm1]
  have qr : ∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x23 → r ≠ .x24 → r ≠ .x22 →
      q.getReg r = v.getReg r :=
    fun r h13 h14 h15 h16 h17 h23 h24 h22 => by rw [qun r h22, pun1 r h13 h14 h15 h16 h17 h23 h24]
  have hregq : Vals q REGION masked :=
    ⟨h.reg.1, fun k hk => ⟨by
      rw [qm _ (by rw [hml] at hk; unfold REGION; omega) (by rw [hml] at hk; unfold REGION; omega)]
      exact (hregv.2 k hk).1, by
      rw [qm _ (by rw [hml] at hk; unfold REGION; omega) (by rw [hml] at hk; unfold REGION; omega)]
      exact (hregv.2 k hk).2⟩⟩
  have hwq : wordsToNat (q.readWords (BitVec.ofNat 64 0x4B20) 8188) = leNat masked.flatten := by
    have := wordsToNat_vals q REGION masked hregq.1 hregq.2
    rwa [hml] at this
  -- second half
  obtain ⟨p2, pst2, ppc2, r14, pun2, pm2⟩ := MacPass.mac_pass_region codeAt_276 q qpc 336 masked.flatten q22
    (by norm_num) (by norm_num)
    (by rw [qr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r18)
    (by rw [qr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r19) hfl hwq
  rw [qm 336 (by norm_num) (by omega), vm 336 (by norm_num), wm 336 (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num), if_pos rfl, qm (336 + 8) (by norm_num) (by omega), vm (336 + 8) (by norm_num),
    wm (336 + 8) (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_pos rfl, MacPass.tagWord1] at r14
  obtain ⟨z, zst, zpc, z25, z21, zun, zT, zfr⟩ := spec_316 p2 (by rw [ppc2]; rfl) T i (by omega) (by omega) hi
    (by rw [pun2 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      qr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r25)
    (by rw [pun2 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      qr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r21)
  have zr : ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 →
      r ≠ .x17 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 → r ≠ .x25 → z.getReg r = t.getReg r := by
    intro r h3 h10 h11 h12 h13 h14 h15 h16 h17 h21 h22 h23 h24 h25
    rw [zun r h25 h21 h3, pun2 r h13 h14 h15 h16 h17 h23 h24, qr r h13 h14 h15 h16 h17 h23 h24 h22,
      vr r h3 h10 h11 h12 h22]
  have zq : ∀ A < 2 ^ 64, A ≠ T + 8 → z.getMem (BitVec.ofNat 64 A) = q.getMem (BitVec.ofNat 64 A) :=
    fun A hA hne => by rw [zfr A hA (by simpa using hne), pm2]
  have zm : ∀ A < 2 ^ 64, A ≠ 1704 → (A + 8 ≤ 320 ∨ 352 ≤ A) → A ≠ T → A ≠ T + 8 →
      z.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [zq A hA h4, qm A hA h3, vmt A hA h1 h2]
  have hcs : (macWords a (chunks32 masked.flatten)).length = 2 := rfl
  refine XSim.pure_steps ((vst.trans (pst1.trans (qst.trans (pst2.trans zst)))).of_eq (by norm_num)
    (by norm_num)) ⟨⟨?_, ?_, ?_, z21, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [zr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r5
  · rw [zr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r18
  · rw [zr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r19
  · rw [z25]; congr 1
  · rw [zm 1696 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)]; exact h.tw
  · rw [zm 1712 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)]; exact h.pz0
  · rw [zm 1720 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)]; exact h.pz1
  · intro k hk
    rw [zm _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.sk k hk
  · exact ⟨by rw [zm 160 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)]; exact h.pk.1,
      by rw [zm (160 + 8) (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)]; exact h.pk.2⟩
  · exact ⟨h.reg.1, fun k hk => ⟨by
      rw [zm _ (by rw [hml] at hk; unfold REGION; omega) (by unfold REGION; omega) (by unfold REGION; omega)
        (by rw [hml] at hk; unfold REGION; omega) (by rw [hml] at hk; unfold REGION; omega)]
      exact (h.reg.2 k hk).1, by
      rw [zm _ (by rw [hml] at hk; unfold REGION; omega) (by unfold REGION; omega) (by unfold REGION; omega)
        (by rw [hml] at hk; unfold REGION; omega) (by rw [hml] at hk; unfold REGION; omega)]
      exact (h.reg.2 k hk).2⟩⟩
  · intro k hk
    rw [zm _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.head k hk
  · rw [List.length_append, h.tlen, hcs]; ring
  · intro j hj
    by_cases h1 : j < 2 * i
    · rw [zm _ (by omega) (by omega) (by omega) (by omega) (by omega), h.tagw j h1,
        List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [h.tlen]; exact h1)]
    · by_cases h2 : j = 2 * i
      · subst h2
        rw [show 0x14B00 + 8 * (2 * i) = T by omega, zq T (by omega) (by omega), qT, p14,
          List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [h.tlen]), h.tlen, Nat.sub_self]
      · have h3 : j = 2 * i + 1 := by omega
        subst h3
        rw [show 0x14B00 + 8 * (2 * i + 1) = T + 8 by omega, zT, r14,
          List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [h.tlen]; omega), h.tlen,
          show 2 * i + 1 - 2 * i = 1 by omega]
  · intro A h1 h2 h8
    rw [zm A (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact h.tail A (by omega) h2 h8
  · rw [zpc]
    by_cases h3 : i + 1 = 3
    · rw [if_pos h3, if_neg (by omega)]
    · rw [if_neg h3, if_pos (by omega)]

/-- The MAC and the final HALT, from instruction 147. -/
theorem mac_xsim (W : List Word) (S : List Byte) (hS : SkOk W S) (levels : List (List Val))
    (root : Val) (masked : List Val) (t : MachineState) (h : OCtx W levels root 11 masked t)
    (hpc : t.pc = pcOf 147) :
    XSim image t 1277466 1867023 3 3
      (H (macKeyInput S 0) >>= fun a0 => H (macKeyInput S 1) >>= fun a1 => H (macKeyInput S 2) >>= fun a2 =>
        pure (a0, a1, a2))
      (fun a w => fetch image w = some (.base .ECALL) ∧ w.getReg .x5 = 1 ∧ w.getReg .x10 = 0 ∧
        ValAt w 160 root ∧ Vals w REGION masked ∧
        (∀ k < 4, w.getMem (BitVec.ofNat 64 (0x4B00 + 8 * k)) = 0) ∧
        (∀ j < 6, w.getMem (BitVec.ofNat 64 (0x14B00 + 8 * j)) =
          BitVec.ofNat 64 (leNat (macTag a.1 a.2.1 a.2.2 masked.flatten) / 2 ^ (64 * j))) ∧
        ∀ A, 0x14B30 ≤ A → A < 0x24B00 → A % 8 = 0 → w.getMem (BitVec.ofNat 64 A) = 0) := by
  have hml : masked.length = 4094 := by rw [h.mlen, lvOff_11]
  have hs := h.shape
  have hvm : Vals t REGION masked := by
    have := h.lv
    rw [lvOff_11, List.drop_eq_nil_of_le (by rw [nodes_length levels hs]), List.append_nil] at this
    exact this
  obtain ⟨u, ust, upc, uun, ufr⟩ := spec_147 t hpc
  obtain ⟨v, vst, vpc, v18, v19, v25, v21, vun, v1696, vfr⟩ := spec_218 u upc
  have vm : ∀ A < 2 ^ 64, A ≠ 1696 → v.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hne => by rw [vfr A hA (by simpa using hne), ufr A hA (by simp)]
  have h0 : MCtx W root masked 0 [] v := by
    refine ⟨?_, v18, v19, v21, v25, v1696, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun j hj => absurd hj (by omega), ?_⟩
    · rw [vun _ (by simp) (by simp) (by simp) (by simp) (by simp), uun]; exact h.base.r5
    · rw [vm 1712 (by norm_num) (by norm_num)]; exact h.base.zero 1712 (by simp [zeroKeys])
    · rw [vm 1720 (by norm_num) (by norm_num)]; exact h.base.zero 1720 (by simp [zeroKeys])
    · intro k hk
      rw [vm _ (by omega) (by omega)]; exact h.base.sk k hk
    · exact ⟨by rw [vm 160 (by norm_num) (by norm_num)]; exact h.out.pk.1,
        by rw [vm (160 + 8) (by norm_num) (by norm_num)]; exact h.out.pk.2⟩
    · exact ⟨hvm.1, fun k hk => ⟨by
        rw [vm _ (by rw [hml] at hk; unfold REGION; omega) (by unfold REGION; omega)]
        exact (hvm.2 k hk).1, by
        rw [vm _ (by rw [hml] at hk; unfold REGION; omega) (by unfold REGION; omega)]
        exact (hvm.2 k hk).2⟩⟩
    · intro k hk
      rw [vm _ (by omega) (by omega)]
      exact h.base.zero _ (by interval_cases k <;> simp [zeroKeys])
    · intro A h1 h2 h8
      rw [vm A (by omega) (by omega)]
      by_cases hA : A < 0x14B20
      · have : A = 0x14B00 ∨ A = 0x14B08 ∨ A = 0x14B10 ∨ A = 0x14B18 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> exact h.out.z _ (by simp)
      · exact h.base.tail A (by omega) h2
  refine (XSim.steps (ust.trans vst) (XSim.bind
    (round_xsim W S hS root masked hml 0 (by norm_num) [] v h0 (by rw [vpc])) (fun a0 w0 hw0 =>
    XSim.bind (round_xsim W S hS root masked hml 1 (by norm_num) _ w0 hw0.1 (by rw [hw0.2]; rfl))
      (fun a1 w1 hw1 =>
    XSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0)
      (round_xsim W S hS root masked hml 2 (by norm_num) _ w1 hw1.1 (by rw [hw1.2]; rfl))
      (fun a2 w2 hw2 => ?_))))).of_eq rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hc, wpc⟩ := hw2
  obtain ⟨x, xst, xpc, x5, x10, xfr⟩ := spec_321 w2 (by rw [wpc]; rfl)
  have xm : ∀ A < 2 ^ 64, x.getMem (BitVec.ofNat 64 A) = w2.getMem (BitVec.ofNat 64 A) :=
    fun A hA => xfr A hA (by simp)
  refine XSim.pure_steps xst ⟨(codeAt_323.fetch x xpc).trans rfl, x5, x10, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [xm _ (by norm_num)]; exact hc.pk.1, by rw [xm _ (by norm_num)]; exact hc.pk.2⟩
  · exact ⟨hc.reg.1, fun k hk => ⟨by
      rw [xm _ (by rw [hml] at hk; unfold REGION; omega)]; exact (hc.reg.2 k hk).1, by
      rw [xm _ (by rw [hml] at hk; unfold REGION; omega)]; exact (hc.reg.2 k hk).2⟩⟩
  · intro k hk
    rw [xm _ (by omega)]; exact hc.head k hk
  · intro j hj
    have ht := hc.tagw j (by omega)
    rw [List.nil_append] at ht
    rw [xm _ (by omega), ht, ← MacPass.macTag_word a0 a1 a2 masked.flatten j hj]
    apply BitVec.eq_of_toNat_eq
    simp
  · intro A h1 h2 h8
    rw [xm A (by omega)]; exact hc.tail A (by omega) h2 h8

/-- The whole of `keygenList`, from the initial state to the final HALT. -/
theorem keygenList_xsim (sk : SecretKey) :
    XSim image (kInit sk) 23889661 31022557 653312 673792 (keygenList (toList sk))
      (fun r t => fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
        ValAt t 160 r.1 ∧ r.1.length = 16 ∧ readBuffer t 0x4B00 CACHE_BYTES = ofList CACHE_BYTES r.2) := by
  have hS := kW_skOk sk
  unfold keygenList
  refine (XSim.bind (k₂ := 47236 + (8 + (86065 + 1277466))) (c₂ := 61565 + (8 + (114723 + 1867023)))
    (n₂ := 2047 + (4094 + 3)) (b₂ := 2047 + (4094 + 3)) (leaves_xsim sk)
    (fun p u hu => ?_)).of_eq rfl (by simp only [sumTo_const]; norm_num)
    (by simp only [sumTo_const]; norm_num) (by simp only [sumTo_const]; norm_num)
    (by simp only [sumTo_const]; norm_num)
  obtain ⟨leaves, c⟩ := p
  obtain ⟨hl, hpc⟩ := hu
  refine (XSim.bind (k₂ := 8 + (86065 + 1277466)) (c₂ := 8 + (114723 + 1867023))
    (n₂ := 4094 + 3) (b₂ := 4094 + 3)
    (levels_xsim (kW sk) leaves u hl (by rw [hpc]; rfl)) (fun levels v hv => ?_)).of_eq rfl
      (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hvc, vpc⟩ := hv
  have hs := hvc.shape
  have hfl := flatten_length 11 levels hs
  have h19 : v.getReg .x19 = BitVec.ofNat 64 0x14B00 := by rw [hvc.r19, lvOff_11]
  obtain ⟨w, wst, wpc, wun, w160, w168, wz0, wz1, wz2, wz3, wfr⟩ := spec_107 v vpc h19
  set root := (levels.getD 11 []).getD 0 [] with hroot
  have hrv : ValAt v (REGION + 16 * lvOff 11) root := by
    have := hvc.lv.2 (lvOff 11 + 0) (by rw [hfl]; decide)
    rwa [flatten_getD 11 levels hs 11 0 le_rfl (by norm_num)] at this
  have hrl : root.length = 16 := hs.getD_len 11 0 le_rfl (by norm_num)
  have hout : Out root w := by
    refine ⟨⟨?_, ?_⟩, fun A hA => ?_⟩
    · rw [w160, show (0x14B00 : Nat) = REGION + 16 * lvOff 11 by rw [lvOff_11]]; exact hrv.1
    · rw [w168, show (0x14B08 : Nat) = REGION + 16 * lvOff 11 + 8 by rw [lvOff_11]]; exact hrv.2
    · simp at hA; rcases hA with rfl | rfl | rfl | rfl
      · exact wz0
      · exact wz1
      · exact wz2
      · exact wz3
  have hbw : Base (kW sk) w := hvc.base.frame (fun r hr => wun r (by rcases hr with h | h | h | h | h <;> simp [h])
    (by rcases hr with h | h | h | h | h <;> simp [h])) wfr (fun k hk => by
      simp at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BaseSafe, zeroKeys])
  have hnv : Vals w REGION (nodes levels) := by
    have hn := nodes_length levels hs
    refine ⟨fun x hx => hvc.lv.1 x (List.mem_of_mem_take hx), fun i hi => ?_⟩
    have h12 : lvOff (11 + 1) = 4095 := by rw [lvOff_succ, lvOff_11]; rfl
    rw [hn] at hi
    have := hvc.lv.2 i (by rw [hfl, h12]; omega)
    have e : (nodes levels).getD i [] = levels.flatten.getD i [] := by
      simp only [nodes, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
    rw [e]
    exact this.frame wfr (by unfold REGION; omega) (fun k hk => by simp at hk; unfold REGION; omega)
  refine XSim.steps wst ((XSim.bind (k₂ := 1277466) (c₂ := 1867023) (n₂ := 3) (b₂ := 3)
    (masks_xsim (kW sk) (toList sk) hS levels root w hbw hs hnv hout (by rw [wpc]))
    (fun masked x hx => ?_)).of_eq rfl (by decide) (by decide) (by decide) (by decide))
  obtain ⟨hoc, xpc⟩ := hx
  refine (XSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0)
    (f := fun a => pure ((levels.getD topH []).getD 0 [],
      zeros 32 ++ masked.flatten ++ macTag a.1 a.2.1 a.2.2 masked.flatten ++
        zeros (cacheBytes - 32 - regionBytes - 48)))
    (mac_xsim (kW sk) (toList sk) hS levels root masked x hoc xpc)
    (fun a y hy => XSim.pure ?_)).of_eq (by simp only [bind_assoc, pure_bind]) rfl rfl rfl rfl
  obtain ⟨y1, y5, y10, ypk, yreg, yhead, ytag, yz⟩ := hy
  have hml : masked.length = 4094 := by rw [hoc.mlen, lvOff_11]
  exact ⟨y1, y5, y10, ypk, hrl, (readBuffer_cache_eq y _ masked hml (MacPass.length_macTag _ _ _ _) yhead
    yreg ytag yz).symm ▸ rfl⟩

/-- The whole of `keygen`. -/
theorem keygen_xsim (sk : SecretKey) :
    XSim image (kInit sk) 23889661 31022557 653312 673792 (keygenRef sk)
      (fun o t => fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
        readOutput submission.sizes submission.layout .keygen t = o) := by
  unfold keygenRef
  refine (XSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) (keygenList_xsim sk)
    (fun r t ht => ?_)).of_eq rfl rfl rfl rfl rfl
  obtain ⟨root, cache⟩ := r
  obtain ⟨t1, t5, t10, tpk, trl, tc⟩ := ht
  refine XSim.pure ⟨t1, t5, t10, ?_⟩
  show (readBuffer t 160 16, readBuffer t 0x4B00 CACHE_BYTES) = (ofList 16 root, ofList CACHE_BYTES cache)
  rw [readBuffer_val t 160 root trl (by norm_num) (by norm_num) tpk, tc]

/-- **keygen**: for every secret key, one run makes exactly the oracle queries of
`keygenRef sk`, outputs its public key and cache, and always takes 31022558 cycles, 653312 calls
and 673792 compressions. -/
theorem keygen_run (sk : SecretKey) :
    submission.run .keygen sk =
      (fun o => ⟨some o, true, 31022558, 653312, 673792⟩) <$> keygenRef sk :=
  XSim.run_eq submission .keygen sk (kInit_eq sk) (keygen_xsim sk) (by decide) id
    (fun _ _ h => h)

/-- The reference makes exactly 653312 calls and 673792 compressions. -/
theorem keygenRef_counts (sk : SecretKey) :
    countCalls (keygenRef sk) = (fun a => (a, 653312)) <$> keygenRef sk ∧
      countBlocks (keygenRef sk) = (fun a => (a, 673792)) <$> keygenRef sk :=
  (keygen_xsim sk).count_eq

/-- The joint call / compression count of the reference is constant. -/
theorem keygenRef_countBoth (sk : SecretKey) :
    Sign.countBoth (keygenRef sk) = (fun a => (a, 653312, 673792)) <$> keygenRef sk :=
  (keygen_xsim sk).countBoth_eq

/-- Value, calls and compressions of the run = the reference's value with its joint
call / compression count. -/
theorem keygen_run_counts (sk : SecretKey) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .keygen sk =
      (fun p => (some p.1, p.2.1, p.2.2)) <$> Sign.countBoth (keygenRef sk) := by
  rw [keygen_run, keygenRef_countBoth, Functor.map_map, Functor.map_map]; rfl

/-- Fixed-oracle form: finished, exactly 31022558 cycles (`< 2^32`), for every oracle. -/
theorem keygen_runWith (hash : Hash) (sk : SecretKey) :
    submission.runWith hash .keygen sk =
      ⟨some (evalWithAnswerFn hash (keygenRef sk)), true, 31022558, 653312, 673792⟩ := by
  unfold Submission.runWith
  rw [keygen_run, evalWithAnswerFn_map]
  rfl

end SigGolfCandidate.Keygen
