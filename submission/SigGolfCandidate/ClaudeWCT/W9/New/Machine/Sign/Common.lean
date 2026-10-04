import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Defs

section

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def scfg : Config := {}
def cbase (c : Nat) : Nat := fieldIdx.getD c 0
def headLook (n : Nat) : Option (BitVec 32) := if 2074 ≤ n then headCode[n - 2074]? else none
def coordLook (c n : Nat) : Option (BitVec 32) :=
  if cbase c ≤ n then (coordCodes.getD c [])[n - cbase c]? else none
def tailLook (n : Nat) : Option (BitVec 32) := if 10963 ≤ n then tailCode[n - 10963]? else none
def hookLook (n : Nat) : Option (BitVec 32) :=
  if n = 153 then some hook153 else if n = 540 then some hook540 else if n = 545 then some 0x00000073 else none
def run (look : Nat → Option (BitVec 32)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux scfg look (stops.map pcOf) 200 (pcOf n) dirs (σK []) []
theorem headCode_length : headCode.length = 152 := by decide +kernel
theorem coordCode0_length : coordCode0.length = 964 := by decide +kernel
theorem coordCode1_length : coordCode1.length = 971 := by decide +kernel
theorem coordCode2_length : coordCode2.length = 972 := by decide +kernel
theorem coordCode3_length : coordCode3.length = 972 := by decide +kernel
theorem coordCode4_length : coordCode4.length = 971 := by decide +kernel
theorem coordCode5_length : coordCode5.length = 972 := by decide +kernel
theorem coordCode6_length : coordCode6.length = 972 := by decide +kernel
theorem coordCode7_length : coordCode7.length = 971 := by decide +kernel
theorem coordCode8_length : coordCode8.length = 972 := by decide +kernel
theorem tailCode_length : tailCode.length = 40 := by decide +kernel
theorem getElem?_append_off {α : Type} {a l : List α} {n k : Nat} {w : α} (ha : a.length = n)
    (h : l[k]? = some w) : (a ++ l)[n + k]? = some w := by
  rw [List.getElem?_append_right (by omega), ha, Nat.add_sub_cancel_left]; exact h
theorem getElem?_append_pre {α : Type} {a l : List α} {k : Nat} {w : α}
    (h : a[k]? = some w) : (a ++ l)[k]? = some w := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h
theorem signNew_head {k : Nat} {w : BitVec 32} (h : headCode[k]? = some w) : signNew[k]? = some w := by
  unfold signNew; exact getElem?_append_pre h
theorem signNew_tail {k : Nat} {w : BitVec 32} (h : tailCode[k]? = some w) : signNew[8889 + k]? = some w := by
  unfold signNew
  rw [show 8889 + k = 152 + (964 + (971 + (972 + (972 + (971 + (972 + (972 + (971 + (972 + k))))))))) by omega]
  exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length
    (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length
    (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length
    (getElem?_append_off coordCode5_length (getElem?_append_off coordCode6_length
    (getElem?_append_off coordCode7_length (getElem?_append_off coordCode8_length h)))))))))
theorem signNew_coord {c k : Nat} (hc : c < 9) {w : BitVec 32} (h : (coordCodes.getD c [])[k]? = some w) :
    signNew[cbase c - 2074 + k]? = some w := by
  unfold signNew
  interval_cases c
  · rw [show cbase 0 - 2074 + k = 152 + k by simp [cbase, fieldIdx]]
    exact getElem?_append_off headCode_length (getElem?_append_pre h)
  · rw [show cbase 1 - 2074 + k = 152 + (964 + k) by simp [cbase, fieldIdx]; omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_pre h))
  · rw [show cbase 2 - 2074 + k = 152 + (964 + (971 + k)) by simp [cbase, fieldIdx]; omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length
      (getElem?_append_off coordCode1_length (getElem?_append_pre h)))
  · rw [show cbase 3 - 2074 + k = 152 + (964 + (971 + (972 + k))) by simp [cbase, fieldIdx]; omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length
      (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_pre h))))
  · rw [show cbase 4 - 2074 + k = 152 + (964 + (971 + (972 + (972 + k)))) by simp [cbase, fieldIdx]; omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length
      (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length
      (getElem?_append_off coordCode3_length (getElem?_append_pre h)))))
  · rw [show cbase 5 - 2074 + k = 152 + (964 + (971 + (972 + (972 + (971 + k))))) by simp [cbase, fieldIdx]; omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length
      (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length
      (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length (getElem?_append_pre h))))))
  · rw [show cbase 6 - 2074 + k = 152 + (964 + (971 + (972 + (972 + (971 + (972 + k)))))) by
      simp [cbase, fieldIdx]; omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length
      (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length
      (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length
      (getElem?_append_off coordCode5_length (getElem?_append_pre h)))))))
  · rw [show cbase 7 - 2074 + k = 152 + (964 + (971 + (972 + (972 + (971 + (972 + (972 + k))))))) by
      simp [cbase, fieldIdx]; omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length
      (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length
      (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length
      (getElem?_append_off coordCode5_length (getElem?_append_off coordCode6_length (getElem?_append_pre h))))))))
  · rw [show cbase 8 - 2074 + k = 152 + (964 + (971 + (972 + (972 + (971 + (972 + (972 + (971 + k)))))))) by
      simp [cbase, fieldIdx]; omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length
      (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length
      (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length
      (getElem?_append_off coordCode5_length (getElem?_append_off coordCode6_length
      (getElem?_append_off coordCode7_length (getElem?_append_pre h)))))))))
theorem newCode_word {im : Image} (h : NewCodeAt im) {k : Nat} {w : BitVec 32} (hk : signNew[k]? = some w) :
    im.code[2074 + k]? = some w := by
  obtain ⟨rest, hrest⟩ := h
  have hlen : k < signNew.length := (List.getElem?_eq_some_iff.mp hk).1
  have h2 : (im.code.drop 2074)[k]? = some w := by
    rw [← hrest, List.getElem?_append_left hlen]; exact hk
  rwa [List.getElem?_drop] at h2
theorem headLook_ok {im : Image} (h : NewCodeAt im) : LookOK im headLook := by
  intro n w hw
  unfold headLook at hw
  split at hw
  · rename_i hle
    have := newCode_word h (signNew_head hw)
    rwa [Nat.add_sub_cancel' hle] at this
  · cases hw
theorem cbase_ge (c : Nat) (hc : c < 9) : 2074 ≤ cbase c := by
  interval_cases c <;> decide
theorem coordLook_ok {im : Image} (h : NewCodeAt im) {c : Nat} (hc : c < 9) : LookOK im (coordLook c) := by
  intro n w hw
  unfold coordLook at hw
  split at hw
  · rename_i hle
    have := newCode_word h (signNew_coord hc hw)
    have hb := cbase_ge c hc
    rwa [show 2074 + (cbase c - 2074 + (n - cbase c)) = n by omega] at this
  · cases hw
theorem tailLook_ok {im : Image} (h : NewCodeAt im) : LookOK im tailLook := by
  intro n w hw
  unfold tailLook at hw
  split at hw
  · rename_i hle
    have := newCode_word h (signNew_tail hw)
    rwa [show 2074 + (8889 + (n - 10963)) = n by omega] at this
  · cases hw
theorem hookLook_ok {im : Image} (h : HooksAt im) : LookOK im hookLook := by
  intro n w hw
  obtain ⟨h1, h2, h3⟩ := h
  unfold hookLook at hw
  split_ifs at hw with e1 e2 e3
  · subst e1; cases hw; exact h1
  · subst e2; cases hw; exact h2
  · subst e3; cases hw; exact h3
theorem run_sound {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat}
    {n : Nat} {dirs : List Dir} {r : PRes} (h : run look stops n dirs = some r) (s : MachineState)
    (hpc : s.pc = pcOf n) (hobl : ∀ o ∈ r.st.obl, o.holds s) (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps im s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch im (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h hl s hpc (by intro p hp; cases hp) hobl hbr
theorem PRes.toState_getReg' (r : PRes) (s : MachineState) (x : Reg) :
    (r.toState s).getReg x = (r.st.regs.get x).eval s := SymState.toState_getReg _ _ _ _
theorem PRes.toState_getMem' (r : PRes) (s : MachineState) (a : Word) :
    (r.toState s).getMem a = memEval s r.st.mem a := rfl
theorem PRes.toState_pc' (r : PRes) (s : MachineState) (h : r.spc = none) : (r.toState s).pc = r.pc := by
  simp [PRes.toState, PRes.finalPc, h]
end ClaudeWCT.W9.Machine.Sign
end

section

namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Spec publicHash shortHash privateHash privatePair privateInput header pad64 Coordinate
  HashOutput Digest)
section tb
variable {α β : Type} {im : Image} {sk : BitVec 256}
theorem TBSim.pure_steps' {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps im s k c t) (hQ : Q a t) : TBSim im sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ
theorem TBSim.of_eq' {s : MachineState} {W W' : Nat} {p q : M α} {Q : α → MachineState → Prop}
    (h : TBSim im sk s W p Q) (he : p = q) (hW : W = W') : TBSim im sk s W' q Q := by
  subst he hW; exact h
theorem TBSim.publicHash_bind' {s : MachineState} {input : List UInt8} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a, TBSim im sk (writeHash s a) W (f a) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.shortHash_bind' {s : MachineState} {input : List UInt8} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this
theorem TBSim.privateHash_bind' {s : MachineState} {co : Coordinate} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk co))
    (h : ∀ a, TBSim im sk (writeHash s a) W (f a) Q) :
    TBSim im sk s (8 * (toQ (privateInput sk co)).blocks + W) (privateHash co >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_privateHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.privatePair_bind' {s : MachineState} {tag lay tree position index : Nat} {W : Nat}
    {f : Digest × Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header tag lay tree position index))))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W
      (f (a.extractLsb' 0 128, a.extractLsb' 128 128)) Q) :
    TBSim im sk s (8 + W) (privatePair tag lay tree position index >>= f) Q := by
  have hb : (toQ (privateInput sk (.inl (header tag lay tree position index)))).blocks = 1 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_tweak_length]
  have : privatePair tag lay tree position index >>= f =
      privateHash (.inl (header tag lay tree position index)) >>= fun a =>
        f (a.extractLsb' 0 128, a.extractLsb' 128 128) := by
    unfold privatePair; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.of_eq' (TBSim.privateHash_bind' hf ht0 hv hq h) rfl (by rw [hb])
end tb
theorem memEval_frame_ofNat (s : MachineState) (ws : SymMem) (A : Nat) (hA : A < 2 ^ 64)
    (h : ∀ p ∈ ws, p.1.base = none ∧ p.1.off.toNat ≠ A) :
    memEval s ws (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  apply memEval_frame
  intro p hp heq
  obtain ⟨h1, h2⟩ := h p hp
  obtain ⟨⟨b, off⟩, v⟩ := p
  simp only at h1; subst h1
  simp only [Addr.eval] at heq
  apply h2; rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
theorem memEval_cons_ofNat (s : MachineState) (k A : Nat) (v : E) (ws : SymMem) (hA : A < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    memEval s ((⟨none, BitVec.ofNat 64 k⟩, v) :: ws) (BitVec.ofNat 64 A) =
      if A = k then v.eval s else memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_cons]
  have e : Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ = BitVec.ofNat 64 k := rfl
  by_cases h : A = k
  · subst h; rw [if_pos e.symm, if_pos rfl]
  · have hne : BitVec.ofNat 64 A ≠ Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ := by
      rw [e]; intro he; exact h ((ofNat_inj hA hk).mp he)
    rw [if_neg hne, if_neg h]
@[simp] theorem E_eval_c' (s : MachineState) (v : Word) : (E.c v).eval s = v := rfl
@[simp] theorem E_eval_reg' (s : MachineState) (r : Reg) : (E.reg r).eval s = s.getReg r := rfl
end ClaudeWCT.W9.Machine.Sign
end
