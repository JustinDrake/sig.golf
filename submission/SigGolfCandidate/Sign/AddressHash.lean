import SigGolfCandidate.Rv.AddressExpand
import SigGolfCandidate.Rv.AddressAdapter
import SigGolfCandidate.Keygen.XSim

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Ref.AddressFormat
open SigGolfCandidate.Keygen OracleComp OracleSpec

set_option maxHeartbeats 500000
set_option exponentiation.threshold 1024

/-- An exact execution certificate supplies the bounded simulation certificate. -/
theorem xsim_to_sim {α : Type} {image : Image} {s : MachineState} {k c n b : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (h : XSim image s k c n b oa Q) (hk : k ≤ c) : Sim image s c oa Q := by
  obtain ⟨oc, hp, he⟩ := h
  let conv (p : {p : α × MachineState // Q p.1 p.2}) : {o : Out α // o.Good c Q} :=
    ⟨⟨p.1.1, n, b, k, c, p.1.2⟩, hk, le_rfl, p.2⟩
  refine ⟨conv <$> oc, ?_, ?_⟩
  · rw [Functor.map_map]; exact hp
  · intro fuel hf
    have hx := he (fuel - k)
    rw [Nat.sub_add_cancel (by omega : k ≤ fuel)] at hx
    rw [hx, bind_map_left]

/-- The signer and key generator use a checked conversion around the chain HASH. -/
theorem address_query {image : Image} (s : MachineState) (prePc postPc retPc : Word)
    (head : CodeAt image prePc AddressAdapter.headCode)
    (tail : CodeAt image postPc AddressAdapter.tailCode)
    (jp : Steps image s 1 1 {s with pc := prePc})
    (jr : ∀ t, t.pc = retPc → Steps image t 1 1 {t with pc := s.pc + 4})
    (hpost : AddressAdapter.addPc prePc 18 + 4 = postPc)
    (hret : AddressAdapter.addPc postPc 3 = retPc)
    (B lay i mu : Nat) (hl : lay < 7) (hi : i < 42) (hm : mu < 8)
    (hB : B + 80 < 2 ^ 24) (hB8 : B % 8 = 0)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 B)
    (h11 : s.getReg .x11 = 64#64)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + 48))
    (h3 : s.getReg .x3 = BitVec.ofNat 64 (mu + 256 * i))
    (h29 : s.getReg .x29 = BitVec.ofNat 64 mu)
    (h5 : s.getReg .x5 = 0)
    (hw : s.getMem (BitVec.ofNat 64 B) = BitVec.ofNat 64 (oldHeader lay 0 i mu))
    (x : List Byte) (hq : hashInput s = fmt x) (hb : (fmt x).blocks = 1) :
    XSim image s 24 34 1 1 (liftM (HashSpec.query (addrFmt x)))
      (fun a t => t = writeHash s a) := by
  let z := {s with pc := prePc}
  obtain ⟨u, ps, ec, upc, u10, u3, u29, ur, um, ud⟩ :=
    AddressAdapter.pre_spec head z rfl B lay i mu hl hi hm hB hB8 h12 hw
  have u11 : u.getReg .x11 = 64#64 := (ur _ (by decide) (by decide) (by decide)).trans h11
  have u12 : u.getReg .x12 = BitVec.ofNat 64 (B + 48) := (ur _ (by decide) (by decide) (by decide)).trans h12
  have u5 : u.getReg .x5 = 0 := (ur _ (by decide) (by decide) (by decide)).trans h5
  have uq : hashInput u = addrFmt x := by
    rw [AddressAdapter.converted_query z u B lay i mu hl hi hm hB h10 u10 h11 u11 hB8 hw um]
    exact congrArg queryPerm hq
  have uv : hashArgumentsValid u = true :=
    hashArgs_of u10 u11 u12 hB8 (by norm_num) (by omega) (by omega) (by omega) (by norm_num)
  have ub : (addrFmt x).blocks = 1 := by rw [addrFmt_blocks, hb]
  have query := XSim.query ec u5 uv uq
  rw [ub] at query
  refine (XSim.steps jp (XSim.steps ps (XSim.bind (k₂ := 4) (c₂ := 4) (n₂ := 0) (b₂ := 0) query (fun a t ht => ?_)))).of_eq
    (by rfl) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  subst t
  obtain ⟨v, vs, vpc, -, -, -, -, vd⟩ :=
    AddressAdapter.post_spec tail (writeHash u a) (by rw [writeHash_pc, upc, hpost]) B hB hB8
      (by rw [writeHash_getReg, u12])
  have vr : v = {writeHash z a with pc := retPc} := by
    rw [vd, AddressAdapter.restored_state z prePc postPc B lay i mu hl hi hm hB
      h10 h12 h3 h29 hw u ud u3 u10 ur um a, hret]
  have vrpc : v.pc = retPc := by rw [vpc, hret]
  have st := vs.trans (jr v vrpc)
  have fin : {v with pc := s.pc + 4} = writeHash s a := by rw [vr]; rfl
  rw [fin] at st
  exact XSim.pure_steps (a := a) st rfl

theorem expand_address_query {image : Image} (s : MachineState) (prePc postPc retPc : Word)
    (head : CodeAt image prePc AddressExpand.headCode)
    (tail : CodeAt image postPc AddressExpand.tailCode)
    (jp : Steps image s 1 1 {s with pc := prePc})
    (jr : ∀ t, t.pc = retPc → Steps image t 1 1 {t with pc := s.pc + 4})
    (hpost : AddressAdapter.addPc prePc 19 + 4 = postPc)
    (hret : AddressAdapter.addPc postPc 1 = retPc)
    (B lay i mu : Nat) (hl : lay < 7) (hi : i < 42) (hm : mu < 8)
    (hB : B + 80 < 2 ^ 24) (hB8 : B % 8 = 0)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 B)
    (h11 : s.getReg .x11 = 64#64)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + 48))
    (h14 : s.getReg .x14 = BitVec.ofNat 64 (oldHeader lay 0 i mu))
    (h5 : s.getReg .x5 = 0)
    (hw : s.getMem (BitVec.ofNat 64 B) = BitVec.ofNat 64 (oldHeader lay 0 i mu))
    (x : List Byte) (hq : hashInput s = fmt x) (hb : (fmt x).blocks = 1) :
    XSim image s 23 33 1 1 (liftM (HashSpec.query (addrFmt x)))
      (fun a t => t = writeHash s a) := by
  let z := {s with pc := prePc}
  obtain ⟨u, ps, ec, upc, u10, u14, u11, ur, um, ud⟩ :=
    AddressExpand.pre_spec head z rfl B lay i mu hl hi hm hB hB8 h12 hw
  have u12 : u.getReg .x12 = BitVec.ofNat 64 (B + 48) := (ur _ (by decide) (by decide) (by decide)).trans h12
  have u5 : u.getReg .x5 = 0 := (ur _ (by decide) (by decide) (by decide)).trans h5
  have uq : hashInput u = addrFmt x := by
    rw [AddressAdapter.converted_query z u B lay i mu hl hi hm hB h10 u10 h11 u11 hB8 hw um]
    exact congrArg queryPerm hq
  have uv : hashArgumentsValid u = true :=
    hashArgs_of u10 u11 u12 hB8 (by norm_num) (by omega) (by omega) (by omega) (by norm_num)
  have ub : (addrFmt x).blocks = 1 := by rw [addrFmt_blocks, hb]
  have query := XSim.query ec u5 uv uq
  rw [ub] at query
  refine (XSim.steps jp (XSim.steps ps (XSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0) query (fun a t ht => ?_)))).of_eq
    (by rfl) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  subst t
  let v := (AddressExpand.postResult postPc).toState (writeHash u a)
  have vs : Steps image (writeHash u a) 1 1 v :=
    AddressExpand.post_spec tail (writeHash u a) (by rw [writeHash_pc, upc, hpost]) B hB hB8
      (by rw [writeHash_getReg, u12])
  have vpc : v.pc = AddressAdapter.addPc postPc 1 := rfl
  have um' : ∀ A, u.getMem A = if A = BitVec.ofNat 64 B then u.getMem (BitVec.ofNat 64 B) else z.getMem A := by
    intro A; rw [um A, um (BitVec.ofNat 64 B), if_pos rfl]
  have vr : v = {writeHash z a with pc := retPc} := by
    dsimp only [v]
    rw [AddressExpand.restored_state z prePc postPc B hB h10 h11 h12 u ud u10 u11
      (u14.trans hw.symm) (h14.trans hw.symm) ur um' a, hret]
  have vrpc : v.pc = retPc := by rw [vpc, hret]
  have st := vs.trans (jr v vrpc)
  have fin : {v with pc := s.pc + 4} = writeHash s a := by rw [vr]; rfl
  rw [fin] at st
  exact XSim.pure_steps (a := a) st rfl

theorem address_hash16_xbind {β : Type} {image : Image} {s : MachineState} {x : List Byte}
    {k c n b : Nat} {f : Val → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hq : XSim image s 24 34 1 1 (liftM (HashSpec.query (addrFmt x)))
      (fun a t => t = writeHash s a))
    (h : ∀ a, XSim image (writeHash s a) k c n b (f (answerBytes 16 a)) Q) :
    XSim image s (24 + k) (34 + c) (1 + n) (1 + b) (hash16 x >>= f) Q := by
  have e : hash16 x >>= f = (liftM (HashSpec.query (addrFmt x)) : OracleComp HashSpec _) >>=
      fun a => f (answerBytes 16 a) := by simp only [hash16, H, bind_assoc, pure_bind]
  rw [e]
  exact XSim.bind hq (fun a t ht => ht ▸ h a)

theorem address_hash16_bindF {β : Type} {image : Image} {s : MachineState} {x : List Byte}
    {W : Nat} {f : Val → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hq : XSim image s 24 34 1 1 (liftM (HashSpec.query (addrFmt x)))
      (fun a t => t = writeHash s a))
    (h : ∀ a, Sim image (writeHash s a) W (f (answerBytes 16 a)) Q) :
    Sim image s (34 + W) (hash16 x >>= f) Q := by
  have e : hash16 x >>= f = (liftM (HashSpec.query (addrFmt x)) : OracleComp HashSpec _) >>=
      fun a => f (answerBytes 16 a) := by simp only [hash16, H, bind_assoc, pure_bind]
  rw [e]
  exact Sim.bind (xsim_to_sim hq (by norm_num)) (fun a t ht => ht ▸ h a)

theorem expand_address_hash16_bindF {β : Type} {image : Image} {s : MachineState} {x : List Byte}
    {W : Nat} {f : Val → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hq : XSim image s 23 33 1 1 (liftM (HashSpec.query (addrFmt x)))
      (fun a t => t = writeHash s a))
    (h : ∀ a, Sim image (writeHash s a) W (f (answerBytes 16 a)) Q) :
    Sim image s (33 + W) (hash16 x >>= f) Q := by
  have e : hash16 x >>= f = (liftM (HashSpec.query (addrFmt x)) : OracleComp HashSpec _) >>=
      fun a => f (answerBytes 16 a) := by simp only [hash16, H, bind_assoc, pure_bind]
  rw [e]
  exact Sim.bind (xsim_to_sim hq (by norm_num)) (fun a t ht => ht ▸ h a)

end SigGolfCandidate.Sign
