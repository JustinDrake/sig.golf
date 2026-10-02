import SigGolfCandidate.T3M.FullCache.MacKeys

namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open OracleComp OracleSpec
open SphincsSecurity (bytesLE)
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def MacW (sg : Bool) (A : Nat) : Prop :=
  (PRIV ≤ A ∧ A < PRIV+64) ∨ (KEYS ≤ A ∧ A < KEYS+64) ∨ OutW sg A

structure MacDone (sg : Bool) (s : MachineState) (tag : T3.HashOutput) (t : MachineState) : Prop where
  pc : t.pc = pcOf (macBase sg+205)
  x5 : t.getReg .x5 = 0
  words : t.readWords (BitVec.ofNat 64 (macOut sg)) 4 = wordsOf (bytesLE 32 tag)
  frame : Frame s t (MacW sg)

/-- Exact refinement of both deployed four-lane MAC routines, for arbitrary cache bytes. -/
theorem mac_tsim (sg : Bool) (sk : BitVec 256) (region : T3.Region) (s : MachineState)
    (hpc : s.pc = pcOf (macBase sg)) (h5 : s.getReg .x5 = 0) (hsk : SkAt s sk)
    (hreg : s.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn region)) :
    TSim (macImage sg) sk s 1703621 2489875 2 2 (T3.privateMac region) (MacDone sg s) := by
  obtain ⟨u0,st0,pc0,x28,x10,x11,x12,m0,m8,m16,m24,m32,m40,m48,m56,r0,f0⟩ := mac_init sg s hpc
  have p0 : PrivAt u0 sk 0 := by
    intro j; fin_cases j
    · exact m0.trans (hsk 0)
    · exact m8.trans (hsk 1)
    · exact m16
    · exact m24
    · exact m32.trans (hsk 2)
    · exact m40.trans (hsk 3)
    · exact m48
    · exact m56
  have z0 : u0.getReg .x5 = 0 := by rw [r0.get (by decide),h5]
  have v0 : hashArgumentsValid u0 = true := hashArgs_const u0 PRIV 64 KEYS x10 x11 x12
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have q0 := priv_query u0 sk 0 p0 x10 x11
  have fetch0 : fetch (macImage sg) u0 = some (.base .ECALL) := (macAt_23 sg).fetch u0 pc0 |>.trans rfl
  unfold T3.privateMac T3.privateMacKey
  simp only [bind_assoc,pure_bind]
  refine (TSim.steps st0 (TSim.privateTweak_bind (k := 1703597) (c := 2489844) (n := 1) (b := 1) fetch0 z0 v0 q0 (fun a => ?_))).of_eq
    rfl (by decide) (by decide) (by decide) (by decide)
  have pa : (writeHash u0 a).pc = pcOf (macBase sg+24) := by
    rw [pc_writeHash,pc0,pcOf_add4]
  obtain ⟨u1,st1,pc1,y12,n24,r1,f1⟩ := mac_next sg (writeHash u0 a) pa (by simpa using x28)
  have p1 := priv_next p0 x12 f1 n24
  have y10 : u1.getReg .x10 = BitVec.ofNat 64 PRIV := by rw [r1.get (by decide),getReg_writeHash,x10]
  have y11 : u1.getReg .x11 = 64 := by rw [r1.get (by decide),getReg_writeHash,x11]
  have z1 : u1.getReg .x5 = 0 := by rw [r1.get (by decide),getReg_writeHash,z0]
  have v1 : hashArgumentsValid u1 = true := hashArgs_const u1 PRIV 64 (KEYS+32) y10 y11 y12
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have q1 := priv_query u1 sk 1 p1 y10 y11
  have fetch1 : fetch (macImage sg) u1 = some (.base .ECALL) := (macAt_29 sg).fetch u1 pc1 |>.trans rfl
  refine TSim.steps st1 (TSim.privateTweak_bind (k := 1703591) (c := 2489831) (n := 0) (b := 0) fetch1 z1 v1 q1 (fun b => ?_))
  have F0 : Frame s (writeHash u1 b) (MacW sg) := by
    have ha := Frame.writeHash u0 a KEYS x12 (by decide)
    have hb := Frame.writeHash u1 b (KEYS+32) y12 (by decide)
    apply (((f0.trans ha).trans f1).trans hb).mono
    intro A hA h
    unfold MacW
    rcases h with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · left; subst A; simp [PRIV]
    · exact Or.inr (Or.inl (by omega))
  have preg : (writeHash u1 b).readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn region) := by
    rw [frame_readWords F0 REGION 16380 (by decide) (by
      intro i hi; cases sg <;> simp only [MacW,OutW,macOut,PRIV,KEYS,REGION,Bool.false_eq_true,if_false,if_true] <;> omega)]
    exact hreg
  have pb : (writeHash u1 b).pc = pcOf (macBase sg+30) := by
    rw [pc_writeHash,pc1,pcOf_add4]
  obtain ⟨t,st,pc,tagwords,zt,ft⟩ := mac_pure sg (writeHash u1 b) (List.ofFn region) pb
    (by rw [List.length_ofFn]) (by rw [preg,wordsToNat_wordsOf 16380 _ (by rw [List.length_ofFn])])
  have hk := keys_after a b x12 f1 y12
  refine TSim.pure_steps st ?_
  refine ⟨pc,?_,?_,?_⟩
  · rw [zt,getReg_writeHash,z1]
  · rw [show (4 : Nat) = 2+2 from rfl,readWords_add,readWords_two,readWords_two,wordsOf_bytesLE32]
    have H : ∀ j : Fin 4, t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) =
        (SiggolfT3Mac4.encodeTag (SiggolfT3Mac4.macTag (keyPair a b) (List.ofFn region))).extractLsb' (64*j.val) 64 := by
      intro j
      rw [tagwords j,laneWord_eq_tag _ _ _ _ hk j,encodeTag_word]
    change [t.getMem (BitVec.ofNat 64 (macOut sg+8*(0:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(1:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(2:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(3:Fin 4).val))] = _
    rw [H 0,H 1,H 2,H 3]
    rfl
  · exact (F0.trans ft).mono (fun A hA h => h.elim id (fun h => Or.inr (Or.inr h)))

end SigGolfCandidate.T3M.FullCache
