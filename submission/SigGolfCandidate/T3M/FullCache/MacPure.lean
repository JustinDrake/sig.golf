import SigGolfCandidate.T3M.FullCache.MacLanes

namespace SigGolfCandidate.T3M.FullCache
set_option maxRecDepth 20000
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def OutW (sg : Bool) (A : Nat) : Prop := macOut sg ≤ A ∧ A < macOut sg+32

theorem lane_frame_out {s t : MachineState} {sg : Bool} {j : Fin 4}
    (h : Frame s t (fun A => A = macOut sg+8*j.val)) : Frame s t (OutW sg) :=
  h.mono (fun A _ ha => by subst A; have := j.isLt; unfold OutW; omega)

theorem out_region {s t : MachineState} {sg : Bool} (h : Frame s t (OutW sg)) :
    t.readWords (BitVec.ofNat 64 REGION) 16380 = s.readWords (BitVec.ofNat 64 REGION) 16380 := by
  apply frame_readWords h REGION 16380 (by decide)
  intro i hi
  cases sg <;> simp only [OutW, macOut, REGION, Bool.false_eq_true, if_false, if_true] <;> omega

theorem out_laneWord {s t : MachineState} {sg : Bool} (h : Frame s t (OutW sg))
    (j : Fin 4) (region : List UInt8) : laneWord t j region = laneWord s j region := by
  have hj := j.isLt
  unfold laneWord
  rw [h.get (by simp [KEYS]; omega) (by cases sg <;> simp [OutW,macOut,KEYS] <;> omega),
    h.get (by simp [KEYS]; omega) (by cases sg <;> simp [OutW,macOut,KEYS] <;> omega)]

theorem mac_pure (sg : Bool) (s : MachineState) (region : List UInt8)
    (hpc : s.pc = pcOf (macBase sg+30)) (hlen : region.length = 131040)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 REGION) 16380) = T3.readLE region) :
    ∃ t, Steps (macImage sg) s 1703591 2489831 t ∧ t.pc = pcOf (macBase sg+205) ∧
      (∀ j : Fin 4, t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = laneWord s j region) ∧
      t.getReg .x5 = s.getReg .x5 ∧ Frame s t (OutW sg) := by
  obtain ⟨u0,st0,pc0,m18,m19,m22,m25,r0,f0⟩ := mac_lanes_init sg s hpc
  have F0 : Frame s u0 (OutW sg) := f0.mono (fun _ _ h => h.elim)
  obtain ⟨u1,st1,pc1,word1,next1,r1,f1⟩ := one_lane sg 0 u0 region
    (by simpa using pc0) m18 m19 (by simpa using m22) m25 hlen (by rw [out_region F0]; exact hreg)
  have F1 : Frame s u1 (OutW sg) :=
    (F0.trans (lane_frame_out f1)).mono (fun _ _ h => h.elim id id)
  have W1 : u1.getMem (BitVec.ofNat 64 (macOut sg+8*(0 : Fin 4).val)) = laneWord s 0 region :=
    word1.trans (out_laneWord F0 0 region)
  obtain ⟨u2,st2,pc2,word2,next2,r2,f2⟩ := one_lane sg 1 u1 region
    (by simpa [laneEnd,Nat.add_assoc] using pc1)
    (by rw [r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next1)
    (by rw [r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F1]; exact hreg)
  have F2 : Frame s u2 (OutW sg) :=
    (F1.trans (lane_frame_out f2)).mono (fun _ _ h => h.elim id id)
  have W2 : u2.getMem (BitVec.ofNat 64 (macOut sg+8*(1 : Fin 4).val)) = laneWord s 1 region :=
    word2.trans (out_laneWord F1 1 region)
  obtain ⟨u3,st3,pc3,word3,next3,r3,f3⟩ := one_lane sg 2 u2 region
    (by simpa [laneEnd,Nat.add_assoc] using pc2)
    (by rw [r2.get (by decide : Reg.x18 ∉ laneRegs),r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r2.get (by decide : Reg.x19 ∉ laneRegs),r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next2)
    (by rw [r2.get (by decide : Reg.x25 ∉ laneRegs),r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F2]; exact hreg)
  have F3 : Frame s u3 (OutW sg) :=
    (F2.trans (lane_frame_out f3)).mono (fun _ _ h => h.elim id id)
  have W3 : u3.getMem (BitVec.ofNat 64 (macOut sg+8*(2 : Fin 4).val)) = laneWord s 2 region :=
    word3.trans (out_laneWord F2 2 region)
  obtain ⟨u4,st4,pc4,word4,next4,r4,f4⟩ := one_lane sg 3 u3 region
    (by simpa [laneEnd,Nat.add_assoc] using pc3)
    (by rw [r3.get (by decide : Reg.x18 ∉ laneRegs),r2.get (by decide : Reg.x18 ∉ laneRegs),r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r3.get (by decide : Reg.x19 ∉ laneRegs),r2.get (by decide : Reg.x19 ∉ laneRegs),r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next3)
    (by rw [r3.get (by decide : Reg.x25 ∉ laneRegs),r2.get (by decide : Reg.x25 ∉ laneRegs),r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F3]; exact hreg)
  have F4 : Frame s u4 (OutW sg) :=
    (F3.trans (lane_frame_out f4)).mono (fun _ _ h => h.elim id id)
  have W4 : u4.getMem (BitVec.ofNat 64 (macOut sg+8*(3 : Fin 4).val)) = laneWord s 3 region :=
    word4.trans (out_laneWord F3 3 region)
  refine ⟨u4,(st0.trans (st1.trans (st2.trans (st3.trans st4)))).of_eq (by decide) (by decide),
    ?_,?_,?_,F4⟩
  · simpa [laneEnd] using pc4
  · intro j; fin_cases j
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega),f3.get (by cases sg <;> decide) (by simp <;> omega),f2.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W1
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega),f3.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W2
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W3
    · exact W4
  · rw [r4.get (by decide : Reg.x5 ∉ laneRegs),r3.get (by decide : Reg.x5 ∉ laneRegs),r2.get (by decide : Reg.x5 ∉ laneRegs),r1.get (by decide : Reg.x5 ∉ laneRegs),r0.get (by decide)]

end SigGolfCandidate.T3M.FullCache
