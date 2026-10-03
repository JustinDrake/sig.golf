import SigGolfCandidate.T3M.CanonicalPort.CombinedA

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart29

/-! Exact mixed-radix top-chain code layout and symbolic result specifications. -/
namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def mx (q : Nat) : Nat := if q<17 then 4 else 3
def off (i : Nat) : Word := BitVec.ofNat 64 (64*(53-i))-BitVec.ofNat 64 1664
def slot (i : Nat) : Nat := if i=0 then 512 else 528+16*i

def baseTab : List Nat := [
  82075, 82116, 82155, 82192, 82226, 82258, 82297, 82334, 82369, 82401, 82431, 82468,
  82503, 82536, 82566, 82594, 82628, 82660, 82690, 82717, 82742, 82774, 82804, 82832,
  82857, 82880, 82921, 82960, 82997, 83031, 83063, 83102, 83139, 83174, 83206, 83236,
  83273, 83308, 83341, 83371, 83399, 83433, 83465, 83495, 83522, 83547, 83579, 83609,
  83637, 83662, 83685, 83726, 83765, 83802, 83836, 83868, 83907, 83944, 83979, 84011,
  84041, 84078, 84113, 84146, 84176, 84204, 84238, 84270, 84300, 84327, 84352, 84384,
  84414, 84442, 84467, 84490, 84531, 84570, 84607, 84641, 84673, 84712, 84749, 84784,
  84816, 84846, 84883, 84918, 84951, 84981, 85009, 85043, 85075, 85105, 85132, 85157,
  85189, 85219, 85247, 85272, 85295, 85336, 85375, 85412, 85446, 85478, 85517, 85554,
  85589, 85621, 85651, 85688, 85723, 85756, 85786, 85814, 85848, 85880, 85910, 85937,
  85962, 85994, 86024, 86052, 86077, 86100, 86141, 86180, 86217, 86251, 86283, 86322,
  86359, 86394, 86426, 86456, 86493, 86528, 86561, 86591, 86619, 86653, 86685, 86715,
  86742, 86767, 86799, 86829, 86857, 86882, 86905, 86946, 86985, 87022, 87056, 87088,
  87127, 87164, 87199, 87231, 87261, 87298, 87333, 87366, 87396, 87424, 87458, 87490,
  87520, 87547, 87572, 87604, 87634, 87662, 87687, 87710, 87751, 87790, 87827, 87861,
  87893, 87932, 87969, 88004, 88036, 88066, 88103, 88138, 88171, 88201, 88229, 88263,
  88295, 88325, 88352, 88377, 88409, 88439, 88467, 88492, 88515, 88556, 88595, 88632,
  88666, 88698, 88737, 88774, 88809, 88841, 88871, 88908, 88943, 88976, 89006, 89034,
  89068, 89100, 89130, 89157, 89182, 89214, 89244, 89272, 89297, 89320, 89361, 89400,
  89437, 89471, 89503, 89542, 89579, 89614, 89646, 89676, 89713, 89748, 89781, 89811,
  89839, 89873, 89905, 89935, 89962, 89987, 90019, 90049, 90077, 90102, 90125, 90166,
  90205, 90242, 90276, 90308, 90347, 90384, 90419, 90451, 90481, 90518, 90553, 90586,
  90616, 90644, 90678, 90710, 90740, 90767, 90792, 90824, 90854, 90882, 90907, 90930,
  90971, 91010, 91047, 91081, 91113, 91152, 91189, 91224, 91256, 91286, 91323, 91358,
  91391, 91421, 91449, 91483, 91515, 91545, 91572, 91597, 91629, 91659, 91687, 91712,
  91735, 91776, 91815, 91852, 91886, 91918, 91957, 91994, 92029, 92061, 92091, 92128,
  92163, 92196, 92226, 92254, 92288, 92320, 92350, 92377, 92402, 92434, 92464, 92492,
  92517, 92540, 92581, 92620, 92657, 92691, 92723, 92762, 92799, 92834, 92866, 92896,
  92933, 92968, 93001, 93031, 93059, 93093, 93125, 93155, 93182, 93207, 93239, 93269,
  93297, 93322, 93345, 93386, 93425, 93462, 93496, 93528, 93567, 93604, 93639, 93671,
  93701, 93738, 93773, 93806, 93836, 93864, 93898, 93930, 93960, 93987, 94012, 94044,
  94074, 94102, 94127, 94150, 94191, 94230, 94267, 94301, 94333, 94372, 94409, 94444,
  94476, 94506, 94543, 94578, 94611, 94641, 94669, 94703, 94735, 94765, 94792, 94817,
  94849, 94879, 94907, 94932, 94955, 94996, 95035, 95072, 95106, 95138, 95177, 95214,
  95249, 95281, 95311, 95348, 95383, 95416, 95446, 95474, 95508, 95540, 95570, 95597,
  95622, 95654, 95684, 95712, 95737, 95760, 95792, 95822, 95849, 95874, 95904, 95932,
  95957, 95980, 96007, 96032, 96054, 96074, 96099, 96122, 96142]

def base (q dB dC : Nat) : Nat :=
  baseTab.getD (if q<17 then 25*q+5*dB+dC else 425+4*dB+dC) 0

/-- T3Z (BIG3): an inline chain's part is one word shorter than before (the head loads its header word from the
WOTS header table, so neither the running `s9` bump nor the first rung's `sb` is left; a max-digit copy has no
bump). -/
def partLen (q d : Nat) : Nat :=
  if d=mx q then 4 else if d+1=mx q then 6 else 5+2*(mx q-d)
def pcB (q dB dC : Nat) : Nat := base q dB dC+2*mx q+1
def pcC (q dB dC : Nat) : Nat := pcB q dB dC+partLen q dB
def pcX (q dB dC : Nat) : Nat := pcC q dB dC+partLen q dC
def entW (q k : Nat) : Nat := if q<17 then 176744+256*k+8*q else 209920+8*k

/-- T3Z (BIG3): a table-slot head loading the header word of chain `i` with its first digit `d` from the header
table (`addi a0; addi a2, a0, 48; ld s9, hOff i d(t3); sd s9, 16(a0); sd tp, 24(a0)`), then `j tgt` past the first
rung's `sb` (6 steps). -/
def headJD (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) o)).set .x12 (addC (addC (.reg rb) o) 48)).set .x25 (hLoad i d),
    [(kAt rb o 24,.reg .x4),(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 24) 8,.valid (kAt rb o 16) 8,.valid (hKey i d) 8]⟩,.c (pcOf tgt),.jump,6,6⟩

/-- T3Z: the table-slot head for the penultimate digit (no `addi a2, a0, 48`: its terminal rung sets x12), the
header word with the first digit `d` read from the table, then `j tgt` (5 steps). -/
def headJDTerm (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  ⟨⟨(RegFile.init.set .x10 (addC (.reg rb) o)).set .x25 (hLoad i d),
    [(kAt rb o 24,.reg .x4),(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 24) 8,.valid (kAt rb o 16) 8,.valid (hKey i d) 8]⟩,.c (pcOf tgt),.jump,5,5⟩

/-- T3Z: the rest of a table-slot chain's first rung after its `sb` (`[li a2, slot]`), up to the `ecall` (0 or 1
step from `p`). -/
def tailR (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 1 else 0
  ⟨⟨(match slot with
      | some a => RegFile.init.set .x12 (.c (BitVec.ofNat 64 a))
      | none => RegFile.init), [], []⟩, .c (pcOf (p + n)), .ecall, n, n⟩

/-- T3Z: inline terminal head (no `addi a2, a0, 48`; `li a2, slot` before the `ecall`), the header word with the
first digit `d` read from the table: up to the first `ecall` (5 steps). -/
def headRHT (rb : Reg) (o : Word) (d sl p i : Nat) : Result :=
  {headRH rb o d (some sl) p i with pc:=.c (pcOf (p+5)),steps:=5,cycles:=5}

def shift10 (w : Reg) (b : Nat) : E :=
  if b<10 then .bin .sll (.reg w) (.c (BitVec.ofNat 64 (10-b)))
  else .bin .srl (.reg w) (.c (BitVec.ofNat 64 (b-10)))
def dispatchR (q : Nat) : Result :=
  let sh := shift10 (if q<9 then .x16 else .x17) (if q<9 then 7*q else 7*(q-9))
  let a := .bin .add (.bin .and sh (.reg .x24)) (.reg .x15)
  ⟨⟨RegFile.init.set .x14 a,[],[]⟩,
    .bin .and (.bin .add a (.c (BitVec.ofNat 64 (32*q) + 18446744073709549984#64))) (.c (~~~1#64)),.jump,4,4⟩

def tailDispatchR : Result :=
  let a := .bin .add (.bin .sll (.reg .x29) (.c 5)) (.c 843776)
  ⟨⟨(RegFile.init.set .x14 a).set .x15 (.c 843776),[],[]⟩,
    .bin .and a (.c (~~~1#64)),.jump,4,4⟩

def rungsOK (q d0 sl p : Nat) : Bool :=
  (List.range' d0 (mx q-d0)).all fun m =>
    rOK (vrun (p+2*(m-d0)) 3)
      (rungR m (if m+1=mx q then some sl else none) (p+2*(m-d0)))

/-- T3Z: every table-slot rung of a shared block entered past its `sb`. -/
def tailsOK (q sl p : Nat) : Bool :=
  (List.range (mx q)).all fun m =>
    rOK (vrun (p+2*m+1) 2) (tailR (if m+1=mx q then some sl else none) (p+2*m+1))

def partOK (q i d p : Nat) : Bool :=
  if d=mx q then rOK (vrun p 4) (copyFH .x19 (off i) (slot i) p)
  else rOK (vrun p 8)
      (if d+1=mx q then headRHT .x19 (off i) d (slot i) p i
       else headRH .x19 (off i) d none p i) &&
    rungsOK q (d+1) (slot i) (p+6)

def entCheck (q k : Nat) : Bool :=
  let dA := k%(mx q+1)
  let dB := k/(mx q+1)%(mx q+1)
  let dC := k/(mx q+1)^2
  if dA=mx q then rOK (vrun (entW q k) 7)
    (copyN .x19 (off (3*q)) (slot (3*q)) (pcB q dB dC))
  else rOK (vrun (entW q k) 7)
    (if dA+1=mx q then headJDTerm .x19 (off (3*q)) (base q dB dC+2*dA+1) (3*q) dA
     else headJD .x19 (off (3*q)) (base q dB dC+2*dA+1) (3*q) dA)

def dispatchOK (q dB dC : Nat) : Bool :=
  rOK (vrun (pcX q dB dC) 5)
    (if q<16 then dispatchR (q+1) else if q=16 then tailDispatchR else retR)

def blockCheck (q dB dC : Nat) : Bool :=
  tailsOK q (slot (3*q)) (base q dB dC) &&
  rungsOK q 0 (slot (3*q)) (base q dB dC) &&
  partOK q (3*q+1) dB (pcB q dB dC) &&
  partOK q (3*q+2) dC (pcC q dB dC) && dispatchOK q dB dC

def tripleCheck (q : Nat) : Bool :=
  ((List.range ((mx q+1)^3)).all fun k => entCheck q k) &&
  ((List.range ((mx q+1)^2)).all fun x => blockCheck q (x/(mx q+1)) (x%(mx q+1)))

theorem piece_steps45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<210432) (s : MachineState) (hpc : s.pc=pcOf p)
    (ho : ∀o∈r.st.obl,o.holds s) :
    Steps CanonicalNative.fixture s r.steps r.cycles (r.toState s) :=
  symRun_sound h (lcodeAt p (by omega)) s hpc ((Oblig.all_iff _ _).mpr ho)

theorem piece_ecall45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<210432) (s : MachineState) (ho : ∀o∈r.st.obl,o.holds s)
    (hst : r.stop=.ecall) :
    fetch CanonicalNative.fixture (r.toState s)=some (.base .ECALL) :=
  symRun_ecall h (lcodeAt p (by omega)) s ((Oblig.all_iff _ _).mpr ho) hst

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart29

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart30

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

theorem land_mask10 (n k : Nat) (hk : k≤7) :
    n &&& (1024*(2^k-1))=1024*(n/1024%2^k) := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_and,show (1024 : Nat)=2^10 by norm_num,Nat.testBit_two_pow_mul,Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  by_cases h : 10≤j
  · simp only [h,decide_true,Bool.true_and,show j-10+10=j by omega]
    by_cases hj : j-10<k <;> simp [hj]
  · simp [h]

theorem field_shl10 (W s k : Nat) (hs : s≤10) (hk : k≤7) :
    W*2^s%2^64/1024%2^k=W/2^(10-s)%2^k := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow,show (1024 : Nat)=2^10 by norm_num,
    Nat.testBit_div_two_pow,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,Nat.testBit_mul_two_pow]
  by_cases hj : j<k
  · simp only [hj,decide_true,Bool.true_and,show j+10<64 by omega,show s≤j+10 by omega]
    rw [show j+10-s=j+(10-s) by omega]
  · simp [hj]

def shiftWord10 (W : Word) (b : Nat) : Word := if b<10 then W<<<(10-b) else W>>>(b-10)

theorem word_mask10 (W : Word) (b : Nat) (hb : b<64) :
    shiftWord10 W b &&& 130048#64=BitVec.ofNat 64 (1024*(W.toNat/2^b%128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,show (130048#64).toNat=1024*(2^7-1) by rfl,land_mask10 _ _ (by decide)]
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 1024*(W.toNat/2^b%128)<2^64 by omega)]
  apply congrArg (fun x => 1024*x)
  unfold shiftWord10
  split_ifs with h
  · simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
    rw [field_shl10 _ _ _ (by omega) (by decide),show 10-(10-b)=b by omega]
    rfl
  · simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul,
      show 2^(b-10)*1024=2^b by rw [show (1024 : Nat)=2^10 by rfl,←pow_add];congr 1;omega]
    rfl

theorem shift10_eval (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w=W)
    (b : Nat) (hb : b<64) : (shift10 w b).eval s=shiftWord10 W b := by
  unfold shift10 shiftWord10
  split_ifs with h <;> simp only [E.eval,BinOp.eval,hw,BitVec.toNat_ofNat]
  · rw [Nat.mod_eq_of_lt (show 10-b<2^64 by omega),Nat.mod_eq_of_lt (show 10-b<64 by omega)]
  · rw [Nat.mod_eq_of_lt (show b-10<2^64 by omega),Nat.mod_eq_of_lt (show b-10<64 by omega)]

theorem dispatch_window (X : Word) (q : Nat) :
    X + 712704#64 + (BitVec.ofNat 64 (32*q) + 18446744073709549984#64) =
      X + pcOf 176744 + BitVec.ofNat 64 (32*q) := by
  calc X + 712704#64 + (BitVec.ofNat 64 (32*q) + 18446744073709549984#64) =
      X + (712704#64 + 18446744073709549984#64) + BitVec.ofNat 64 (32*q) := by ac_rfl
    _ = _ := by rfl

theorem dispatch_target (W : Word) (b q : Nat) (hb : b<64) (hq : q<17) :
    ((shiftWord10 W b &&& 130048#64)+pcOf 176744+BitVec.ofNat 64 (32*q)) &&& ~~~1#64 =
      pcOf (entW q (W.toNat/2^b%128)) := by
  rw [word_mask10 W b hb,ofNat_add_ofNat,ofNat_add_ofNat,
    even_andNot1' _ (by omega)]
  unfold pcOf entW
  rw [if_pos hq]
  apply congrArg (BitVec.ofNat 64)
  omega

theorem prologue_target (v : Digest) :
    (((v.extractLsb' 0 64 <<< 10) &&& 130048#64)+pcOf 176744) &&& ~~~1#64 =
      pcOf (176744+256*(v.toNat%128)) := by
  have h := dispatch_target (v.extractLsb' 0 64) 0 0 (by decide) (by decide)
  simpa [shiftWord10,entW,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
    Nat.mod_mod_of_dvd _ (show 128∣2^64 by decide)] using h

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart30

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart31

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def sourceWord (v : Digest) (q : Nat) : Word := if q<9 then v.extractLsb' 0 64 else v.extractLsb' 63 64
def sourceBit (q : Nat) : Nat := if q<9 then 7*q else 7*(q-9)

theorem extract_field (v : Digest) (a b : Nat) (h : b+7≤64) :
    (v.extractLsb' a 64).toNat/2^b%128=v.toNat/2^(a+b)%128 := by
  have hr := Search.ext_shr_mask v a b 7 h
  have hl : (v.extractLsb' a 64 >>> b) &&& 127#64=
      BitVec.ofNat 64 ((v.extractLsb' a 64).toNat/2^b%128) := by
    have he : v.extractLsb' a 64=BitVec.ofNat 64 (v.extractLsb' a 64).toNat := by
      apply BitVec.eq_of_toNat_eq; simp
    conv_lhs => rw [he]
    rw [ofNat_shr _ _ (v.extractLsb' a 64).isLt,Search.ofNat_and127]
  have hh := hl.symm.trans hr
  exact (ofNat_inj (by omega) (by omega)).mp hh

theorem source_field (v : Digest) (q : Nat) (hq : q<17) :
    (sourceWord v q).toNat/2^(sourceBit q)%128=Search.topRank v q := by
  unfold sourceWord sourceBit Search.topRank
  split_ifs with h
  · simpa using extract_field v 0 (7*q) (by omega)
  · rw [extract_field v 63 (7*(q-9)) (by omega),show 63+7*(q-9)=7*q by omega]

theorem dispatch_step {p q : Nat} (hq : q<17) (hp : p<210432)
    (hrun : vrun p 5=some (dispatchR q)) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h16 : s.getReg .x16=v.extractLsb' 0 64)
    (h17 : s.getReg .x17=v.extractLsb' 63 64)
    (h24 : s.getReg .x24=130048#64) (h15 : s.getReg .x15=712704#64) :
    ∃t, Steps CanonicalNative.fixture s 4 4 t ∧ t.pc=pcOf (entW q (Search.topRank v q)) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hW : s.getReg (if q<9 then .x16 else .x17)=sourceWord v q := by
    unfold sourceWord
    split_ifs <;> assumption
  have hb : sourceBit q<64 := by unfold sourceBit;split_ifs <;> omega
  refine ⟨(dispatchR q).toState s,piece_steps45 hrun hp s hpc (by simp [dispatchR]),?_,?_,?_⟩
  · change (((shift10 (if q<9 then .x16 else .x17) (sourceBit q)).eval s &&& s.getReg .x24)+
      s.getReg .x15+(BitVec.ofNat 64 (32*q)+18446744073709549984#64)) &&& ~~~1#64=pcOf (entW q (Search.topRank v q))
    rw [h24,h15,dispatch_window,shift10_eval s _ _ hW _ hb,dispatch_target _ _ q hb hq,source_field v q hq]
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatchR]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatchR,rv_simp]

theorem tail_dispatch_step {p : Nat} (hp : p<210432)
    (hrun : vrun p 5=some tailDispatchR) (s : MachineState) (k : Nat) (hk : k<64)
    (hpc : s.pc=pcOf p) (h29 : s.getReg .x29=BitVec.ofNat 64 k) :
    ∃t, Steps CanonicalNative.fixture s 4 4 t ∧ t.pc=pcOf (entW 17 k) ∧
      RegsExcept s t [.x14,.x15] ∧ Frame s t (fun _ => False) := by
  refine ⟨tailDispatchR.toState s,piece_steps45 hrun hp s hpc (by simp [tailDispatchR]),?_,?_,?_⟩
  · simp only [Result.toState_pc,tailDispatchR,E.eval,BinOp.eval,h29]
    change ((BitVec.ofNat 64 k <<< 5)+BitVec.ofNat 64 843776) &&& ~~~1#64=pcOf (entW 17 k)
    rw [ofNat_shl,ofNat_add_ofNat,even_andNot1' _ (by omega)]
    unfold entW pcOf
    norm_num
    congr 1 <;> omega
  · intro r hr
    rw [Result.toState_getReg]
    simp only [tailDispatchR]
    rw [RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),
      RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),RegFile.init_get_eval]
  · intro A _ _
    simp [tailDispatchR,rv_simp]

#print axioms dispatch_step
#print axioms tail_dispatch_step
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart31

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart32

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_0 : tripleCheck 0=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart32

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart33

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_1 : tripleCheck 1=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart33

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart34

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_2 : tripleCheck 2=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart34

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart35

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_3 : tripleCheck 3=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart35

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart36

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_4 : tripleCheck 4=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart36

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart37

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_5 : tripleCheck 5=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart37

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart38

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_6 : tripleCheck 6=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart38

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart39

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_7 : tripleCheck 7=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart39

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart40

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_8 : tripleCheck 8=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart40

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart41

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_9 : tripleCheck 9=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart41

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart42

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_10 : tripleCheck 10=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart42

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart43

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_11 : tripleCheck 11=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart43

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart44

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_12 : tripleCheck 12=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart44

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart45

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_13 : tripleCheck 13=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart45

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart46

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_14 : tripleCheck 14=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart46

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart47

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_15 : tripleCheck 15=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart47

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart48

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_16 : tripleCheck 16=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart48

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart49

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_17 : tripleCheck 17=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart49

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart50

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem tripleCheck_at (q : Nat) (hq : q<18) : tripleCheck q=true := by
  interval_cases q
  exacts [tripleCheck_0, tripleCheck_1, tripleCheck_2, tripleCheck_3, tripleCheck_4, tripleCheck_5, tripleCheck_6, tripleCheck_7, tripleCheck_8, tripleCheck_9, tripleCheck_10, tripleCheck_11, tripleCheck_12, tripleCheck_13, tripleCheck_14, tripleCheck_15, tripleCheck_16, tripleCheck_17]

theorem entCheck_at (q k : Nat) (hq : q<18) (hk : k<(mx q+1)^3) : entCheck q k=true := by
  have h := tripleCheck_at q hq
  simp only [tripleCheck,Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1 k (List.mem_range.mpr hk)

theorem blockCheck_at (q dB dC : Nat) (hq : q<18) (hB : dB ≤ mx q) (hC : dC ≤ mx q) :
    blockCheck q dB dC=true := by
  have h := tripleCheck_at q hq
  simp only [tripleCheck,Bool.and_eq_true] at h
  have hh : (mx q+1)*dB+dC<(mx q+1)^2 := by
    unfold mx at *
    split_ifs at * <;> omega
  have e1 : ((mx q+1)*dB+dC)/(mx q+1)=dB := by
    unfold mx at *
    split_ifs at * <;> omega
  have e2 : ((mx q+1)*dB+dC)%(mx q+1)=dC := by
    unfold mx at *
    split_ifs at * <;> omega
  have hb := List.all_eq_true.mp h.2 ((mx q+1)*dB+dC) (List.mem_range.mpr hh)
  rwa [e1,e2] at hb

#print axioms tripleCheck_at
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart50

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart51

/-! Machine semantics of one mixed-radix top chain, with exact immutable image checks supplied separately. -/
namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

structure NCtx where
  w : WBytes
  tree : Nat
  leaf : Nat
  S3 : Nat
  digits : Nat → Nat
  ret : Nat

namespace NCtx

def blk (c : NCtx) (i : Nat) : Nat := c.S3 - 1664 + 64 * (53 - i)
def dig (c : NCtx) (i : Nat) : Nat := c.digits i
def topMax (i : Nat) : Nat := mx (i / 3)
def last (i : Nat) : Nat := topMax i - 1

def w0 (i : Nat) : Nat := 0x101 + 2 ^ 40 * i
def w1 (c : NCtx) : Nat := hdr1 c.tree c.leaf
def pad0 (c : NCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800)
def pad1 (c : NCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 32)
def val (c : NCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 48)
def ok (c : NCtx) : Prop :=
  c.tree < 2 ^ 32 ∧ c.leaf < 2 ^ 32 ∧ c.S3 % 8 = 0 ∧ 0x800 + 11288 + 1664 ≤ c.S3 ∧ c.S3 + 2064 ≤ 0x7000 ∧
    c.ret < 209920

/-- T3Z (BIG3): `x28` is the midpoint of the WOTS header table's bank 0 (set by the lower layers' leaf-pk restore
`lui t3, 0xff4`); every head reads its header word from the table. -/
def known (c : NCtx) : List (Reg × Word) :=
  [(.x5, 0), (.x11, 64), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6),
   (.x28, BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank 0 0)), (.x19, BitVec.ofNat 64 c.S3),
   (.x4, BitVec.ofNat 64 c.w1), (.x27, BitVec.ofNat 64 0x101), (.x1, pcOf c.ret)]

def kOf (c : NCtx) (q : Nat) : Nat :=
  c.dig (3*q) + (mx q+1)*c.dig (3*q+1) + (mx q+1)^2*c.dig (3*q+2)
def qb (c : NCtx) (i : Nat) : Nat := base (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def qB (c : NCtx) (i : Nat) : Nat := pcB (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def qC (c : NCtx) (i : Nat) : Nat := pcC (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def qX (c : NCtx) (i : Nat) : Nat := pcX (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def startPc (c : NCtx) (i : Nat) : Nat :=
  if i%3=0 then entW (i/3) (c.kOf (i/3)) else if i%3=1 then c.qB i else c.qC i

def rungPc (c : NCtx) (i m : Nat) : Nat :=
  if i%3=0 then c.qb i+2*m
  else c.startPc i + (if c.dig i = last i then 3 else 4) + 2*(m-c.dig i)
def endPc (c : NCtx) (i : Nat) : Nat :=
  if i%3=0 then c.qB i else if i%3=1 then c.qC i else c.qX i

/-- The memory written by the chains `0 .. i - 1`. -/
def Wr (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  (0x200 ≤ A ∧ A < 0x5D0) ∨ (c.S3 - 1664 + 64 * (54 - i) ≤ A ∧ A < c.blk 0 + 80)
def WrIn (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  c.Wr i A ∨ (c.blk i + 16 ≤ A ∧ A < c.blk i + 32) ∨ (c.blk i + 48 ≤ A ∧ A < c.blk i + 80)

/-- The chain blocks hold the witness at the start `s0`, and (T3Z) the image data (the WOTS header table) is in
place. -/
def Orig0 (c : NCtx) (s0 : MachineState) : Prop :=
  (∀ i, i < 54 → ∀ k < 8, OrigW c.w s0 (c.blk i + 8 * k)) ∧ SigGolfCandidate.T3M.CanonicalPort.Verify.DataOK s0

def Base (c : NCtx) (s0 : MachineState) (W : Nat → Prop) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → s.getReg x = s0.getReg x) ∧ Frame s0 s W ∧
    (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0))

/-- Before chain `i`'s code (T3Z: no running `x25`; the heads read the header table). -/
def ChainIn (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr i) acc s ∧ acc.length = i ∧ s.pc = pcOf (c.startPc i)

def HdrOk (c : NCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat % 2 ^ 32 = 0x101 ∧
    (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat / 2 ^ 40 = i ∧
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1

def StepInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc s ∧ acc.length = i ∧
    c.HdrOk i s ∧ DigAt s (c.blk i + 48) v ∧ s.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    (m < last i → s.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48)) ∧ s.pc = pcOf (c.rungPc i m)

def PreHash (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (t : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc t ∧ acc.length = i ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (w0 i + 2 ^ 32 * m) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1 ∧ DigAt t (c.blk i + 48) v ∧
    t.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    t.getReg .x12 = BitVec.ofNat 64 (if m = last i then slot i else c.blk i + 48) ∧
    t.pc = pcOf (c.rungPc i m + (if m = last i then 2 else 1)) ∧ fetch vimage t = some (.base .ECALL)

def EndInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (i + 1)) acc s ∧ acc.length = i + 1 ∧ s.pc = pcOf (c.endPc i)

/-! ## Geometry -/

theorem blk_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) :
    c.blk i % 8 = 0 ∧ 0x800 + 11288 ≤ c.blk i ∧ c.blk i + 80 ≤ 0x7000 := by
  obtain ⟨-, -, h64, hlo, hhi, -⟩ := hc
  unfold blk; refine ⟨?_, ?_, ?_⟩ <;> omega

theorem blk_le (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) : c.blk i + 64 * i = c.blk 0 := by
  obtain ⟨-, -, -, hlo, -⟩ := hc
  unfold blk; omega

theorem slot_props (i : Nat) (hi : i < 54) : slot i % 16 = 0 ∧ 512 ≤ slot i ∧ slot i + 32 ≤ 0x580 := by
  unfold slot; split <;> omega

theorem base_off (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) (k : Nat) (hk : k ≤ 80) :
    BitVec.ofNat 64 c.S3 + (off i + BitVec.ofNat 64 k) = BitVec.ofNat 64 (c.blk i + k) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  unfold off blk
  rw [ofNat_add_off _ _ _ _ (by omega) (by omega), show c.S3 + 64 * (53 - i) - 1664 = c.S3 - 1664 + 64 * (53 - i) by
    omega]

theorem base_off0 (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) :
    BitVec.ofNat 64 c.S3 + off i = BitVec.ofNat 64 (c.blk i) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  unfold off blk
  rw [ofNat_add_off0 _ _ _ (by omega) (by omega), show c.S3 + 64 * (53 - i) - 1664 = c.S3 - 1664 + 64 * (53 - i) by
    omega]

theorem w0_hdr0 (c : NCtx) (i m : Nat) (hi : i < 54) (hm : m < 256) (ht : c.tree < 2 ^ 32) :
    w0 i + 2 ^ 32 * m = hdr0 1 (0 : Layer).val c.tree (m + 256 * i) := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by norm_num) ht (by omega)]
  unfold w0; simp; ring

theorem w0_lt (i m : Nat) (hi : i < 54) (hm : m < 256) : w0 i + 2 ^ 32 * m < 2 ^ 64 := by
  unfold w0; omega

/-- The machine's hash input at a step of chain `i`. -/
theorem chain_hashInput (c : NCtx) (hc : c.ok) (i m : Nat) (hi : i < 54) (hm : m < 256) (v : Digest)
    (t : MachineState) (h10 : t.getReg .x10 = BitVec.ofNat 64 (c.blk i))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (hp0 : DigAt t (c.blk i) (c.pad0 i)) (hp1 : DigAt t (c.blk i + 32) (c.pad1 i))
    (h16 : t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (w0 i + 2 ^ 32 * m))
    (h24 : t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1)
    (hv : DigAt t (c.blk i + 48) v) :
    hashInput t = toQ (chainInputP 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) v) := by
  obtain ⟨h64, hlo, hhi⟩ := c.blk_props hc i hi
  apply hashInput_toQ t _ 0 (c.blk i) (chainInputP_length _ _ _ _ _ _ _ _) h10 (by omega) (by omega) h11
    (by norm_num)
  rw [wordsOf_chainInputP, show 8 * (0 + 1) = 2 + (2 + (2 + 2)) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_two, readWords_two, readWords_two, readWords_two, hp0.1, hp0.2,
    show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
    show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
    show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp1.1, hp1.2,
    show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hv.1, hv.2, w0_hdr0 c i m hi hm hc.1]
  rfl

theorem orig_frame {c : NCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i k : Nat} (hi : i < 54) (hk : k < 8) (hW : ¬ W (c.blk i + 8 * k)) :
    OrigW c.w t (c.blk i + 8 * k) := by
  have := c.blk_props hc i hi
  unfold OrigW
  rw [hF _ (by omega) hW]
  exact h0.1 i hi k hk

theorem pads_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat}
    (hi : i < 54) (hF : Frame s0 t (c.WrIn i)) :
    DigAt t (c.blk i) (c.pad0 i) ∧ DigAt t (c.blk i + 32) (c.pad1 i) := by
  have hb := c.blk_props hc i hi
  have nW : ∀ k, k = 0 ∨ k = 1 ∨ k = 4 ∨ k = 5 → ¬ c.WrIn i (c.blk i + 8 * k) := by
    intro k hk hw
    have := c.blk_le hc i hi
    have hlo := hc.2.2.2.1
    unfold WrIn Wr blk at *
    omega
  have o0 := orig_frame hF h0 hc hi (k := 0) (by omega) (nW 0 (by omega))
  have o1 := orig_frame hF h0 hc hi (k := 1) (by omega) (nW 1 (by omega))
  have o4 := orig_frame hF h0 hc hi (k := 4) (by omega) (nW 4 (by omega))
  have o5 := orig_frame hF h0 hc hi (k := 5) (by omega) (nW 5 (by omega))
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at o0 o1
  rw [show 8 * 4 = 32 by rfl] at o4
  rw [show c.blk i + 8 * 5 = c.blk i + 32 + 8 by ring] at o5
  refine ⟨DigAt_origW o0 o1 (by omega), ?_⟩
  have := DigAt_origW o4 o5 (by omega)
  rwa [show c.blk i + 32 - 0x800 = c.blk i - 0x800 + 32 by omega] at this

theorem val_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat} (hi : i < 54)
    (hF : Frame s0 t (c.Wr i)) : DigAt t (c.blk i + 48) (c.val i) := by
  have hb := c.blk_props hc i hi
  have nW : ∀ k, k = 6 ∨ k = 7 → ¬ c.Wr i (c.blk i + 8 * k) := by
    intro k hk hw
    have := c.blk_le hc i hi
    have hlo := hc.2.2.2.1
    unfold Wr blk at *
    omega
  have o6 := orig_frame hF h0 hc hi (k := 6) (by omega) (nW 6 (by omega))
  have o7 := orig_frame hF h0 hc hi (k := 7) (by omega) (nW 7 (by omega))
  rw [show c.blk i + 8 * 6 = c.blk i + 48 by ring] at o6
  rw [show c.blk i + 8 * 7 = c.blk i + 48 + 8 by ring] at o7
  have := DigAt_origW o6 o7 (by omega)
  rwa [show c.blk i + 48 - 0x800 = c.blk i - 0x800 + 48 by omega] at this

theorem topMax_bounds (i : Nat) : 3 ≤ topMax i ∧ topMax i ≤ 4 := by
  unfold topMax mx; split <;> omega

theorem last_bounds (i : Nat) : 2 ≤ last i ∧ last i ≤ 3 := by
  have := topMax_bounds i; unfold last; omega

theorem rungPc_succ (c : NCtx) (i m : Nat) (hd : c.dig i ≤ m) :
    c.rungPc i (m+1) = c.rungPc i m+2 := by
  unfold rungPc; split_ifs <;> omega

theorem rungPc_end (c : NCtx) (i : Nat) (hi : i < 54) (hd : c.dig i < topMax i) :
    c.rungPc i (last i) + 3 = c.endPc i := by
  have hm := topMax_bounds i
  have e1 : i%3=1 → c.dig (3*(i/3)+1)=c.dig i := fun h => by rw [show 3*(i/3)+1=i by omega]
  have e2 : i%3=2 → c.dig (3*(i/3)+2)=c.dig i := fun h => by rw [show 3*(i/3)+2=i by omega]
  unfold rungPc endPc startPc qb qB qC qX pcX pcC pcB partLen
  unfold last topMax at *
  split_ifs <;> omega

/-- The step registers hold the steps. -/
theorem posE_eval (c : NCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (i m : Nat) (hm : m ≤ last i) :
    (posE m).eval s = BitVec.ofNat 64 m := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hm3 : m ≤ 3 := by have := last_bounds i; omega
  interval_cases m
  · rfl
  · exact kr .x6 1 (by simp [known]) (by decide)
  · exact kr .x7 2 (by simp [known]) (by decide)
  · exact kr .x8 3 (by simp [known]) (by decide)

theorem w0_low (i m : Nat) (hi : i < 54) (hm : m < 256) :
    (BitVec.ofNat 64 (w0 i + 2 ^ 32 * m)).toNat % 2 ^ 32 = 0x101 ∧
      (BitVec.ofNat 64 (w0 i + 2 ^ 32 * m)).toNat / 2 ^ 40 = i := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi hm)]
  unfold w0; constructor <;> omega

theorem w0_low0 (i : Nat) (hi : i < 54) :
    (BitVec.ofNat 64 (w0 i)).toNat % 2 ^ 32 = 0x101 ∧ (BitVec.ofNat 64 (w0 i)).toNat / 2 ^ 40 = i := by
  have := w0_low i 0 hi (by omega)
  rwa [Nat.mul_zero, Nat.add_zero] at this

end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart51

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart52

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def DigitsOk (c : NCtx) : Prop := ∀i,i<54 → c.dig i ≤ topMax i

theorem dig_group_le (c : NCtx) (hd : c.DigitsOk) (q k : Nat) (hq : q<18) (hk : k<3) :
    c.dig (3*q+k) ≤ mx q := by
  have h := hd (3*q+k) (by omega)
  simpa only [topMax,show (3*q+k)/3=q by omega] using h

theorem kOf_lt (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    c.kOf q < (mx q+1)^3 := by
  have h0 := c.dig_group_le hd q 0 hq (by decide)
  have h1 := c.dig_group_le hd q 1 hq (by decide)
  have h2 := c.dig_group_le hd q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  unfold kOf mx at *
  split_ifs at * <;> omega

theorem kOf_digits (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    c.kOf q%(mx q+1)=c.dig (3*q) ∧
    c.kOf q/(mx q+1)%(mx q+1)=c.dig (3*q+1) ∧
    c.kOf q/(mx q+1)^2=c.dig (3*q+2) := by
  have h0 := c.dig_group_le hd q 0 hq (by decide)
  have h1 := c.dig_group_le hd q 1 hq (by decide)
  have h2 := c.dig_group_le hd q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  unfold kOf mx at *
  split_ifs at * <;> exact ⟨by omega,by omega,by omega⟩

theorem blk_at (c : NCtx) (hd : c.DigitsOk) (i : Nat) (hi : i<54) :
    blockCheck (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))=true :=
  blockCheck_at _ _ _ (by omega) (c.dig_group_le hd _ 1 (by omega) (by decide))
    (c.dig_group_le hd _ 2 (by omega) (by decide))

theorem chk_headJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hd : c.dig i< last i) :
    vrun (c.startPc i) 7=some (headJD .x19 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have he := entCheck_at q (c.kOf q) (by omega) (c.kOf_lt hds q (by omega))
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hds q (by omega)
  have hd' : c.dig (3*q)< mx q-1 := by simpa only [last,topMax,eq] using hd
  unfold entCheck at he
  rw [k1,k2,k3,if_neg (by omega),if_neg (by omega)] at he
  have hs : c.startPc (3*q)=entW q (c.kOf q) := by simp [startPc,h0,eq]
  have hr : c.rungPc (3*q) (c.dig (3*q))=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*c.dig (3*q) := by
    simp [rungPc,qb,h0,eq]
  rw [hs,hr]
  exact rOK_eq he

theorem chk_headJTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hd : c.dig i=last i) :
    vrun (c.startPc i) 7=some (headJDTerm .x19 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have he := entCheck_at q (c.kOf q) (by omega) (c.kOf_lt hds q (by omega))
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hds q (by omega)
  have hm := topMax_bounds (3*q)
  have hd' : c.dig (3*q)=mx q-1 := by simpa only [last,topMax,eq] using hd
  simp only [topMax,eq] at hm
  unfold entCheck at he
  rw [k1,k2,k3,if_neg (by omega),if_pos (by omega)] at he
  have hs : c.startPc (3*q)=entW q (c.kOf q) := by simp [startPc,h0,eq]
  have hr : c.rungPc (3*q) (c.dig (3*q))=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*c.dig (3*q) := by
    simp [rungPc,qb,h0,eq]
  rw [hs,hr]
  exact rOK_eq he

theorem chk_copyJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hd : c.dig i=topMax i) :
    vrun (c.startPc i) 7=some (copyN .x19 (off i) (slot i) (c.endPc i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have he := entCheck_at q (c.kOf q) (by omega) (c.kOf_lt hds q (by omega))
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hds q (by omega)
  have hd' : c.dig (3*q)=mx q := by simpa only [topMax,eq] using hd
  unfold entCheck at he
  rw [k1,k2,k3,if_pos hd'] at he
  have hs : c.startPc (3*q)=entW q (c.kOf q) := by simp [startPc,h0,eq]
  have he' : c.endPc (3*q)=pcB q (c.dig (3*q+1)) (c.dig (3*q+2)) := by simp [endPc,qB,h0,eq]
  rw [hs,he']
  exact rOK_eq he

theorem part_at (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54) (h0 : i%3≠0) :
    partOK (i/3) i (c.dig i) (c.startPc i)=true := by
  obtain ⟨q,r,rfl,hr⟩ : ∃q r,i=3*q+r ∧ r<3 := ⟨i/3,i%3,by omega,by omega⟩
  have eq : (3*q+r)/3=q := by omega
  have hb := c.blk_at hds (3*q+r) hi
  rw [eq] at hb
  unfold blockCheck at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨-,hB⟩,hC⟩,-⟩ := hb
  unfold startPc qB qC
  rw [if_neg h0,eq]
  rcases (show r=1 ∨ r=2 by omega) with rfl|rfl
  · rw [if_pos (by omega)];exact hB
  · rw [if_neg (by omega)];exact hC

theorem chk_headR (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i< last i) :
    vrun (c.startPc i) 8=some (headRH .x19 (off i) (c.dig i) none (c.startPc i) i) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i< mx (i/3)-1 := hd
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_neg (by omega)] at hp
  exact rOK_eq hp.1

theorem chk_headRTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i=last i) :
    vrun (c.startPc i) 8=some (headRHT .x19 (off i) (c.dig i) (slot i) (c.startPc i) i) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i=mx (i/3)-1 := hd
  have hm : 3≤ mx (i/3) := (topMax_bounds i).1
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_pos (by omega)] at hp
  exact rOK_eq hp.1

theorem chk_copyF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i=topMax i) :
    vrun (c.startPc i) 4=some (copyFH .x19 (off i) (slot i) (c.startPc i)) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  change c.dig i=mx (i/3) at hd
  rw [if_pos hd] at hp
  exact rOK_eq hp

theorem chk_rung (c : NCtx) (hds : c.DigitsOk) (i m : Nat) (hi : i<54)
    (hm : c.dig i ≤ m) (hm2 : m ≤ last i) (hfirst : i%3≠0 → c.dig i< m) :
    vrun (c.rungPc i m) 3=some (rungR m (if m=last i then some (slot i) else none) (c.rungPc i m)) := by
  have hmx := topMax_bounds i
  by_cases h0 : i%3=0
  · obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
    have eq : 3*q/3=q := by omega
    have hb := c.blk_at hds (3*q) hi
    rw [eq] at hb
    unfold blockCheck at hb
    simp only [Bool.and_eq_true] at hb
    have hn : m< mx q := by simpa only [last,topMax,eq] using (show m< topMax (3*q) by unfold last at hm2;omega)
    have hh := List.all_eq_true.mp hb.1.1.1.2 m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
    have hr : c.rungPc (3*q) m=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*m := by simp [rungPc,qb,h0,eq]
    have ht : (m+1=mx q) ↔ m=last (3*q) := by unfold last topMax;rw [eq];omega
    simpa only [rungsOK,Nat.sub_zero,Nat.add_zero,hr,ht] using rOK_eq hh
  · have hp := c.part_at hds i hi h0
    have hd := hfirst h0
    have hn : c.dig i< mx (i/3) := by change c.dig i< topMax i;unfold last at hm2;omega
    unfold partOK at hp
    rw [if_neg (by omega),Bool.and_eq_true] at hp
    have hmmax : m< mx (i/3) := by change m<topMax i;unfold last at hm2;omega
    have hh := List.all_eq_true.mp hp.2 m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
    have hr : c.rungPc i m=c.startPc i+6+2*(m-(c.dig i+1)) := by
      unfold rungPc
      rw [if_neg h0,if_neg (by omega)]
      omega
    have ht : (m+1=mx (i/3)) ↔ m=last i := by unfold last topMax;omega
    simpa only [hr,ht] using rOK_eq hh

/-- T3Z: a table-slot chain's first rung entered past its `sb` (the head's `j` target). -/
theorem chk_tail (c : NCtx) (hds : c.DigitsOk) (i m : Nat) (hi : i<54) (h0 : i%3=0) (hm2 : m ≤ last i) :
    vrun (c.rungPc i m+1) 2=some (tailR (if m=last i then some (slot i) else none) (c.rungPc i m+1)) := by
  have hmx := topMax_bounds i
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have hb := c.blk_at hds (3*q) hi
  rw [eq] at hb
  unfold blockCheck at hb
  simp only [Bool.and_eq_true] at hb
  have hn : m< mx q := by simpa only [last,topMax,eq] using (show m< topMax (3*q) by unfold last at hm2;omega)
  have hh := List.all_eq_true.mp hb.1.1.1.1 m (List.mem_range.mpr hn)
  have hr : c.rungPc (3*q) m=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*m := by simp [rungPc,qb,h0,eq]
  have ht : (m+1=mx q) ↔ m=last (3*q) := by unfold last topMax;rw [eq];omega
  simpa only [hr,ht] using rOK_eq hh

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart52

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart53

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

theorem baseTab_all : (baseTab.all fun x => decide (x<96160))=true := by decide +kernel

theorem base_lt (q dB dC : Nat) : base q dB dC<96160 := by
  unfold base
  rw [List.getD_eq_getElem?_getD]
  split
  · cases hn : baseTab[25*q+5*dB+dC]? with
    | none => simp
    | some x => simpa using List.all_eq_true.mp baseTab_all x (List.mem_of_getElem? hn)
  · cases hn : baseTab[425+4*dB+dC]? with
    | none => simp
    | some x => simpa using List.all_eq_true.mp baseTab_all x (List.mem_of_getElem? hn)

theorem mx_bounds (q : Nat) : 3≤ mx q ∧ mx q≤4 := by unfold mx;split <;> omega

theorem partLen_le (q d : Nat) : partLen q d≤14 := by
  have hm := mx_bounds q
  unfold partLen
  split_ifs <;> omega

namespace NCtx

theorem qX_lt (c : NCtx) (i : Nat) : c.qX i<97000 := by
  have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
  have h1 := partLen_le (i/3) (c.dig (3*(i/3)+1))
  have h2 := partLen_le (i/3) (c.dig (3*(i/3)+2))
  have hm := mx_bounds (i/3)
  unfold qX pcX pcC pcB
  omega

theorem startPc_lt (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54) : c.startPc i<210432 := by
  have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
  have h1 := partLen_le (i/3) (c.dig (3*(i/3)+1))
  have hm := mx_bounds (i/3)
  have hk := c.kOf_lt hds (i/3) (by omega)
  unfold startPc entW qB qC pcC pcB mx at *
  split_ifs at * <;> omega

theorem rungPc_lt (c : NCtx) (i m : Nat) (hm : m≤ last i) : c.rungPc i m<210432 := by
  have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
  have h1 := partLen_le (i/3) (c.dig (3*(i/3)+1))
  have hmx := mx_bounds (i/3)
  have hl := last_bounds i
  unfold rungPc qb startPc qB qC pcC pcB
  split_ifs <;> omega

theorem inline_rungPc (c : NCtx) (i : Nat) (h0 : i%3≠0) :
    c.rungPc i (c.dig i)=c.startPc i+(if c.dig i=last i then 3 else 4) := by
  simp [rungPc,h0]

theorem inline_copy_end (c : NCtx) (i : Nat) (h0 : i%3≠0) (hd : c.dig i=topMax i) :
    c.startPc i+4=c.endPc i := by
  have e1 : i%3=1 → c.dig (3*(i/3)+1)=c.dig i := fun h => by rw [show 3*(i/3)+1=i by omega]
  have e2 : i%3=2 → c.dig (3*(i/3)+2)=c.dig i := fun h => by rw [show 3*(i/3)+2=i by omega]
  unfold startPc endPc qB qC qX pcX pcC partLen
  unfold topMax at hd
  split_ifs <;> omega

end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart53

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart54

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

theorem tailR_keeps (slot : Option Nat) (p : Nat) : Keeps (tailR slot p) [.x12] := by
  intro x hx
  simp only [tailR]
  split
  · rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  · rfl

namespace NCtx

/-- **The HASH of step `m` of chain `i`.** -/
theorem prehash_step (c : NCtx) (hc : c.ok) (s0 : MachineState) (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i m : Nat) (hi : i < 54) (hm : m ≤ last i) (hd : c.dig i ≤ m)
    (acc : List Digest) (v : Digest) (t : MachineState) (ht : c.PreHash s0 i acc m v t) :
    t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (chainInputP 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) v) ∧
      ∀ a : BitVec 256,
        (m < last i → c.StepInv s0 i acc (m + 1) (a.extractLsb' 0 128) (writeHash t a)) ∧
        (m = last i → c.EndInv s0 i (acc ++ [a.extractLsb' 0 128]) (writeHash t a)) := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h16, h24, hv, h10, h12, hpc, -⟩ := ht
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → t.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have t5 : t.getReg .x5 = 0 := kr _ _ (by simp [known]) (by decide)
  have t11 : t.getReg .x11 = BitVec.ofNat 64 64 := kr _ _ (by simp [known]) (by decide)
  obtain ⟨p0, p1⟩ := pads_at hc h0 hi hF
  refine ⟨t5, ?_, ?_, ?_⟩
  · apply hashArgs_const t (c.blk i) 64 (if m = last i then slot i else c.blk i + 48) h10 t11 h12 (by omega)
      (by omega) (by omega)
    · split <;> omega
    · split <;> omega
  · exact c.chain_hashInput hc i m hi (by omega) v t h10 t11 p0 p1 h16 h24 hv
  · intro a
    have hdst : ∀ (B : Nat), t.getReg .x12 = BitVec.ofNat 64 B → B + 32 < 2 ^ 64 →
        Frame t (writeHash t a) (fun A => B ≤ A ∧ A < B + 32) := fun B hB hB' => Frame.writeHash t a B hB hB'
    refine ⟨fun hm2 => ?_, fun hm2 => ?_⟩
    · have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by rw [h12, if_neg (by omega)]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.WrIn i) := (hF.trans fr).mono (by
        intro A _ h; rcases h with h | h
        · exact h
        · right; right; omega)
      have fget : ∀ A, A < 2 ^ 64 → ¬ (c.blk i + 48 ≤ A ∧ A < c.blk i + 48 + 32) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA hn => fr A hA hn
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, hlen,
        ⟨?_, ?_, ?_⟩, DigAt.writeHash_lo t a _ d12 (by omega),
        by rw [getReg_writeHash]; exact h10, fun _ => by rw [getReg_writeHash]; exact d12, ?_⟩
      · have hj' := hS j hj
        have hsj := slot_props j (by omega)
        exact hj'.frame fr (by omega) (by omega) (by omega)
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi (by omega))]
        unfold w0; omega
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi (by omega))]
        unfold w0; omega
      · rw [fget _ (by omega) (by omega)]; exact h24
      · rw [pc_writeHash, hpc, if_neg (by omega), c.rungPc_succ i m hd, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
    · subst hm2
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (slot i) := by rw [h12, if_pos rfl]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.Wr (i + 1)) := (hF.trans fr).mono (by
        intro A _ h
        have := c.blk_le hc i hi
        have hlo := hc.2.2.2.1
        unfold WrIn Wr blk at *
        omega)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen], ?_⟩
      · rw [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < acc.length
        · have hj' := hS j hjl
          have hsj := slot_props j (by omega)
          have hmono : slot j + 16 ≤ slot i := by unfold slot; split_ifs <;> omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
          exact hj'.frame fr (by omega) (by omega) (by omega)
        · have hj2 : j = acc.length := by omega
          subst hj2
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
          exact DigAt.writeHash_lo t a _ d12 (by omega)
      · have hd3 : c.dig i < topMax i := by omega
        rw [pc_writeHash, hpc, if_pos rfl, ← c.rungPc_end i hi hd3, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1

/-- **One rung**: `sb POS_m, 20(a0)` (and `li a2, slot` for the last step), up to the `ecall`. -/
theorem rung_piece (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i < 54) (hm : m ≤ last i) (hp : p < 210432)
    (hrun : vrun p 3 = some (rungR m (if m = last i then some (slot i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps vimage s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ fetch vimage t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (slot i)) ∧ (m < last i → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (w0 i + 2 ^ 32 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = last i then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  set r := rungR m (if m = last i then some (slot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungR, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 20⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (20 : Word) = BitVec.ofNat 64 20 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps45 hrun hp s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, rungR])
  have hn : r.steps = (if m = last i then 2 else 1) ∧ r.cycles = (if m = last i then 2 else 1) := by
    simp only [hr, rungR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungR_keeps m (if m = last i then some (slot i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 4 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungR]
    rw [memEval_one s _ _ (c.blk i + 16) A key (by omega) hA]
    split
    · have e1 : (addC (E.reg .x10) 16).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
        rw [addC_eval]; simp only [E.eval, h10]
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
      simp only [E.eval, BinOp.eval]
      rw [e1, c.posE_eval hk hR i m hm]
    · rfl
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_neg (show m ≠ last i by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
    congr 1; unfold w0; ring
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungR]
    by_cases h2 : m = last i <;> simp [h2, E.eval]

/-- T3Z: **the rest of a table-slot chain's first rung** after its `sb` (the head's jump target): `[li a2, slot]`,
up to the `ecall`. -/
theorem tail_piece (i m p : Nat) (hp : p < 210432)
    (hrun : vrun p 2 = some (tailR (if m = last i then some (slot i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) :
    ∃ t, Steps vimage s (if m = last i then 1 else 0) (if m = last i then 1 else 0) t ∧
      fetch vimage t = some (.base .ECALL) ∧ (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (slot i)) ∧ (m ≠ last i → t.getReg .x12 = s.getReg .x12) ∧
      Frame s t (fun _ => False) ∧ t.pc = pcOf (p + (if m = last i then 1 else 0)) := by
  set r := tailR (if m = last i then some (slot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by simp [hr, tailR]
  have hst := piece_steps45 hrun hp s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, tailR])
  have hn : r.steps = (if m = last i then 1 else 0) ∧ r.cycles = (if m = last i then 1 else 0) := by
    simp only [hr, tailR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := tailR_keeps (if m = last i then some (slot i) else none) p
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_,
    fun A hA _ => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_neg h2]
    rw [RegFile.init_get_eval]
  · rw [Result.toState_getMem]; simp [hr, tailR, memEval]
  · rw [Result.toState_pc]; simp only [hr, tailR]
    by_cases h2 : m = last i <;> simp [h2, E.eval]

/-- **A rung after a step's hash.** -/
theorem rung_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : i < 54) (hm : m ≤ last i) (hp : c.rungPc i m < 210432)
    (hrun : vrun (c.rungPc i m) 3 = some (rungR m (if m = last i then some (slot i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps vimage s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    c.rung_piece hc hk i m (c.rungPc i m) hi hm hp hrun s hpc hR h10 hH
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, h16, ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact h10
  · by_cases h2 : m = last i
    · rw [h12a h2, if_pos h2]
    · rw [h12b (by omega), h12 (by omega), if_neg h2]
  · rw [hpc']

end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart54

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart55
namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
namespace NCtx

theorem kAt_eval (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) (k : Nat) (hk : k ≤ 80) : (kAt .x19 (off i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
  simp only [kAt, Addr.eval, E.eval, h19]
  exact c.base_off hc i hi k hk

theorem lAt_eval (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) (k : Nat) (hk : k ≤ 80) :
    (lAt .x19 (off i) k).eval s = s.getMem (BitVec.ofNat 64 (c.blk i + k)) := by
  simp only [lAt, E.eval, addC_eval, h19]
  rw [c.base_off hc i hi k hk]

/-- T3Z (BIG3, the table-load proof of erickeigen's 59cbf8ec / our T3X `LCtx.header_load` on the top layer): a
head's header load `ld s9, hOff i d(t3)` reads word `8 i + d` of the header table's bank 0, which the chain phase
never writes (its frame lies below `0x7000`). -/
theorem header_load (c : NCtx) (hc : c.ok) {s0 s : MachineState} (h0 : c.Orig0 s0) (i d : Nat)
    (hi : i < 54) (hd : d < 8) (hF : Frame s0 s (c.Wr i))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank 0 0)) :
    (Oblig.valid (hKey i d) 8).holds s ∧
      (hLoad i d).eval s = BitVec.ofNat 64 (w0 i + 2 ^ 32 * d) := by
  have hb := c.blk_props hc 0 (by omega)
  have hA : 2 ^ 23 + 4096 ≤ SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d ∧
      SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d + 8 ≤ 2 ^ 24 := by
    unfold SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA; omega
  have key : (hKey i d).eval s = BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d) := by
    simp only [hKey, Addr.eval, E.eval, h28, hOff]
    change BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank 0 0) +
      (BitVec.ofNat 64 (64 * i + 8 * d) - BitVec.ofNat 64 2048) =
        BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d)
    rw [ofNat_add_off0 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank 0 0) (64 * i + 8 * d) 2048
      (by unfold SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA; omega)
      (by unfold SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA; omega)]
    apply congrArg (BitVec.ofNat 64)
    unfold SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA
    omega
  have fr : s.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d)) =
      s0.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d)) := by
    apply hF (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d) (by omega)
    unfold Wr
    intro h
    rcases h with h | h <;> omega
  refine ⟨?_, ?_⟩
  · show accessValid ((hKey i d).eval s) 8 = true
    rw [key]
    exact valid_ofNat _ 8 hA.2 (by unfold SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA; omega)
  · have he : (addC (.reg .x28) (hOff i d)).eval s =
        BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d) := by
      simpa only [hKey, Addr.eval, addC_eval, E.eval] using key
    change s.getMem ((addC (.reg .x28) (hOff i d)).eval s) = _
    rw [he, fr, h0.2.header 0 i d (by norm_num) (by omega) hd]
    all_goals (congr 1 <;> unfold w0 <;> omega)

theorem copy_mem (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (copyMem .x19 (off i) (slot i)) (BitVec.ofNat 64 A) =
      if A = slot i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slot i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) := by
  have hs := slot_props i hi
  unfold copyMem
  rw [memEval_two s _ _ _ _ (slot i + 8) (slot i) A rfl rfl (by omega) (by omega) hA,
    c.lAt_eval hc h19 i hi 56 (by omega), c.lAt_eval hc h19 i hi 48 (by omega)]

theorem copy_obl (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) : ∀ o ∈ copyObl .x19 (off i), o.holds s := by
  have hb := c.blk_props hc i hi
  simp only [copyObl, List.mem_cons, List.not_mem_nil, or_false]
  rintro o (rfl | rfl)
  · show accessValid ((kAt .x19 (off i) 56).eval s) 8 = true
    rw [c.kAt_eval hc h19 i hi 56 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x19 (off i) 48).eval s) 8 = true
    rw [c.kAt_eval hc h19 i hi 48 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)

theorem copy_post (c : NCtx) (hc : c.ok) {s0 s t : MachineState} (h0 : c.Orig0 s0) (i : Nat)
    (hi : i < 54) (acc : List Digest) (hlen : acc.length = i) (hF : Frame s0 s (c.Wr i))
    (hS : ∀ j < acc.length, DigAt s (slot j) (acc.getD j 0))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3)
    (htm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) = memEval s (copyMem .x19 (off i) (slot i)) (BitVec.ofNat 64 A)) :
    Frame s0 t (c.Wr (i + 1)) ∧ ∀ j < (acc ++ [c.val i]).length,
      DigAt t (slot j) ((acc ++ [c.val i]).getD j 0) := by
  have hb := c.blk_props hc i hi
  have hs := slot_props i hi
  have tm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = slot i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slot i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (htm A hA).trans (c.copy_mem hc h19 i hi A hA)
  have hfr : Frame s t (fun A => A = slot i + 8 ∨ A = slot i) := by
    intro A hA hn
    rw [tm A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  refine ⟨(hF.trans hfr).mono ?_, fun j hj => ?_⟩
  · intro A _ h
    have := c.blk_le hc i hi
    have hlo := hc.2.2.2.1
    rcases h with h | h
    · unfold Wr at h ⊢; unfold blk at h this ⊢; omega
    · left; omega
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < acc.length
    · have hsj := slot_props j (by omega)
      have hmono : slot j + 16 ≤ slot i := by unfold slot; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
      exact (hS j hjl).frame hfr (by omega) (by omega) (by omega)
    · have hj2 : j = acc.length := by omega
      subst hj2
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
      have hv := val_at hc h0 hi hF
      refine ⟨?_, ?_⟩
      · rw [tm _ (by omega), if_neg (by omega), if_pos rfl]; exact hv.1
      · rw [tm _ (by omega), if_pos rfl]; exact hv.2

/-- **The max-digit copy of a table-slot chain** (`A = 3q`; T3Z: no `s9` update), then `j` past the shared
block's `A` rungs (5 steps). -/
theorem copyN_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54)
    (hp0 : c.startPc i < 210432)
    (hrun : vrun (c.startPc i) 7 = some (copyN .x19 (off i) (slot i) (c.endPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyN .x19 (off i) (slot i) (c.endPc i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyN] using c.copy_obl hc h19 i hi)
  have hkeep := copyN_keeps .x19 (off i) (slot i) (c.endPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; rfl

/-- **The max-digit copy of an inline chain** (`B`, `C`; T3Z: no bump, 4 instructions). -/
theorem copyFH_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hp0 : c.startPc i < 210432)
    (hend : c.startPc i + 4 = c.endPc i)
    (hrun : vrun (c.startPc i) 4 = some (copyFH .x19 (off i) (slot i) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyFH .x19 (off i) (slot i) (c.startPc i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyFH] using c.copy_obl hc h19 i hi)
  have hkeep := copyFH_keeps .x19 (off i) (slot i) (c.startPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; simp only [hr, copyFH, E.eval]; rw [hend]


end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart55

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart56
namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

theorem headJD_keeps (rb : Reg) (o : Word) (tgt i d : Nat) :
    Keeps (headJD rb o tgt i d) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJD]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem headJDTerm_keeps (rb : Reg) (o : Word) (tgt i d : Nat) :
    Keeps (headJDTerm rb o tgt i d) [.x10, .x25] := by
  intro x hx
  simp only [headJDTerm]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

namespace NCtx
/-- **The head of a table-slot chain** (`A = 3q`; T3Z: the header word of chain `i` with its first digit read from
the header table, then `j` past the first rung's `sb`) up to the first `ecall` (6 steps). -/
theorem headJ_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i < last i)
    (hp0 : c.startPc i < 210432) (hp1 : c.rungPc i (c.dig i) + 1 < 210432)
    (hrun1 : vrun (c.startPc i) 7 = some (headJD .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)))
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (slot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 6 6 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load hc h0 i (c.dig i) hi (by omega) hF (kr _ _ (by simp [known]) (by decide))
  set r := headJD .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJD, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJD_keeps .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  have t12 : t1.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), addC_eval, a0e,
      show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 24 then BitVec.ofNat 64 c.w1
      else if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJD]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 24 ∨ A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, -, h12b, hfr2, hpc2⟩ :=
    tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 t1 hpc1
  have hsteps : r.steps = 6 ∧ r.cycles = 6 := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  have hn : c.dig i ≠ last i := by omega
  rw [if_neg hn] at hst2
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨t, (hst1.trans hst2).of_eq (by norm_num) (by norm_num),
    ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · exact False.elim h
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_pos rfl]
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hreg _ (by decide)]; exact t10
  · rw [h12b hn, t12, if_neg hn]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)

/-- **The head of a table-slot chain at the penultimate digit** (`A = 3q`; no `addi a2, a0, 48`; T3Z: the header
word with the first digit read from the header table, then `j` to the rung's `li a2, slot`) up to the `ecall`
(6 steps). -/
theorem headJTerm_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 210432) (hp1 : c.rungPc i (c.dig i) + 1 < 210432)
    (hrun1 : vrun (c.startPc i) 7 = some (headJDTerm .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)))
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (slot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 6 6 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load hc h0 i (c.dig i) hi (by omega) hF (kr _ _ (by simp [known]) (by decide))
  set r := headJDTerm .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJDTerm, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJDTerm_keeps .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJDTerm]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), a0e]
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 24 then BitVec.ofNat 64 c.w1
      else if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJDTerm]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 24 ∨ A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, h12a, -, hfr2, hpc2⟩ :=
    tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 t1 hpc1
  have hsteps : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  rw [if_pos hd] at hst2
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨t, (hst1.trans hst2).of_eq (by norm_num) (by norm_num),
    ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · exact False.elim h
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_pos rfl]
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hreg _ (by decide)]; exact t10
  · rw [h12a hd, if_pos hd]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)


end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart56

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart57
namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

theorem headRHT_keeps (rb : Reg) (o : Word) (d sl p i : Nat) :
    Keeps (headRHT rb o d sl p i) [.x10, .x12, .x25] :=
  headRH_keeps rb o d (some sl) p i

namespace NCtx
/-- **The head of an inline chain** (`B`, `C`; T3Z: the header word with the first digit read from the header
table, no first-rung `sb`), up to the first `ecall` (5 steps). -/
theorem headR_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i < last i)
    (hp0 : c.startPc i < 210432) (hrp : c.rungPc i (c.dig i) = c.startPc i + 4)
    (hrun : vrun (c.startPc i) 8 = some (headRH .x19 (off i) (c.dig i) none (c.startPc i) i))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load hc h0 i (c.dig i) hi (by omega) hF (kr _ _ (by simp [known]) (by decide))
  set r := headRH .x19 (off i) (c.dig i) none (c.startPc i) i with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst := piece_steps45 hrun hp0 s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headRH])
  have hn : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headRH_keeps .x19 (off i) (c.dig i) none (c.startPc i) i
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRH]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
    split_ifs <;> simp_all
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · have h2 : ¬ c.dig i = last i := by omega
    rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    simp only [h2, if_false]
    rw [addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · have h2 : ¬ c.dig i = last i := by omega
    rw [Result.toState_pc]; simp only [hr, headRH, hrp]
    simp [h2, E.eval]

/-- **The head of an inline chain at the penultimate digit** (`B`, `C`; no `addi a2, a0, 48`, `li a2, slot`
before the `ecall`; T3Z: the header word read from the header table), up to the `ecall` (5 steps). -/
theorem headRTerm_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 210432) (hrp : c.rungPc i (c.dig i) = c.startPc i + 3)
    (hrun : vrun (c.startPc i) 8 =
      some (headRHT .x19 (off i) (c.dig i) (slot i) (c.startPc i) i))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load hc h0 i (c.dig i) hi (by omega) hF (kr _ _ (by simp [known]) (by decide))
  set r := headRHT .x19 (off i) (c.dig i) (slot i) (c.startPc i) i with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRHT, headRH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst := piece_steps45 hrun hp0 s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headRHT, headRH])
  have hn : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headRHT_keeps .x19 (off i) (c.dig i) (slot i) (c.startPc i) i
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRHT, headRH]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
    split_ifs <;> simp_all
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headRHT, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headRHT, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    simp only [hd, if_true, E.eval]
  · rw [Result.toState_pc]; simp only [hr, headRHT, headRH, hrp]
    simp [hd, E.eval]


end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart57

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart58

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem chainInputP_pad (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    pad64 (chainInputP lay tree leaf i step p0 p1 v)=chainInputP lay tree leaf i step p0 p1 v :=
  pad64_of_aligned _ (by rw [chainInputP_length])

theorem chainInputP_blocks (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    (toQ (chainInputP lay tree leaf i step p0 p1 v)).blocks=1 := by
  rw [blocks_toQ ⟨by rw [chainInputP_length];omega,by rw [chainInputP_length]⟩,chainInputP_length]

def rest (c : NCtx) (i m : Nat) (v : Digest) : M Digest :=
  (List.range' m (topMax i-m)).foldlM
    (fun v step => shortHash (chainInputP 0 c.tree c.leaf i step (c.pad0 i) (c.pad1 i) v)) v

theorem rest_succ (c : NCtx) (i m : Nat) (h : m ≤ last i) (v : Digest) :
    c.rest i m v=shortHash (chainInputP 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) v) >>= c.rest i (m+1) := by
  have hm := topMax_bounds i
  unfold last at h
  unfold rest
  rw [show topMax i-m=(topMax i-(m+1))+1 by omega,List.range'_succ,List.foldlM_cons]

theorem rest_max (c : NCtx) (i : Nat) (v : Digest) : c.rest i (topMax i) v=pure v := by
  simp [rest]

theorem chainP_rest (c : NCtx) (i d : Nat) (v : Digest) :
    chainP 0 c.tree c.leaf i d (topMax i-d) (c.pad0 i) (c.pad1 i) v=c.rest i d v := rfl

def preCost (i m : Nat) : Nat := 8+9*(last i-m)+(if m< last i then 1 else 0)

theorem steps_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K (acc++[v]))) :
    ∀k m,m+k=last i → c.dig i ≤ m → ∀v s,c.PreHash s0 i acc m v s →
      SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+3*(topMax i-m)+5) (C+preCost i m) Q (A+preCost i m)
        (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (c.rest i m v) (fun v => K (acc++[v]))) := by
  have hmax := topMax_bounds i
  have hlast := last_bounds i
  have hlastEq : last i+1=topMax i := by unfold last;omega
  intro k
  induction k with
  | zero =>
      intro m hm hd v s hs
      obtain rfl : m=last i := by omega
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc s0 hk h0 i (last i) hi (le_refl _) hd acc v s hs
      rw [rest_succ c i (last i) (le_refl _)]
      have hf := hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ (writeHash s a) N C Q A
          (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (c.rest i (last i+1) (a.extractLsb' 0 128)) (fun v => K (acc++[v]))) := by
        intro a
        rw [hlastEq,rest_max,SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_pure]
        exact hK _ _ ((hpost a).2 rfl)
      have h3 := SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.shortHash_bind (f:=c.rest i (last i+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [chainInputP_pad];exact hin) H
      rw [chainInputP_pad,chainInputP_blocks] at h3
      exact h3.mono (by omega) (by simp [preCost]) (fun hq => ⟨hq,by simp [preCost]⟩)
  | succ k ih =>
      intro m hm hd v s hs
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc s0 hk h0 i m hi (by omega) hd acc v s hs
      rw [rest_succ c i m (by omega)]
      have hf := hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ (writeHash s a) (N+3*(topMax i-(m+1))+5+2)
          (C+preCost i (m+1)+(if m+1=last i then 2 else 1)) Q
          (A+preCost i (m+1)+(if m+1=last i then 2 else 1))
          (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (c.rest i (m+1) (a.extractLsb' 0 128)) (fun v => K (acc++[v]))) := by
        intro a
        have hrun := c.chk_rung hds i (m+1) hi (by omega) (by omega) (fun _ => by omega)
        obtain ⟨u,hu,hp⟩ := c.rung_step hc hk i (m+1) hi (by omega) (c.rungPc_lt i _ (by omega)) hrun acc _ _
          ((hpost a).1 (by omega))
        have ht := ih (m+1) (by omega) (by omega) _ _ hp
        exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hu ht (by split <;> omega) (by omega) (fun hq => ⟨hq,by omega⟩)
      have h3 := SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.shortHash_bind (f:=c.rest i (m+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [chainInputP_pad];exact hin) H
      rw [chainInputP_pad,chainInputP_blocks] at h3
      refine h3.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart58

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart59

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def tableJump (i : Nat) : Nat := if i%3=0 then 1 else 0

/-- T3Z (BIG3): a head is `5` (inline: the table load with the first digit, no first-rung `sb`) or `6` (table slot:
the same load and the jump past the first rung's `sb`); a max-digit copy is `4` (inline, no bump) or `5` (table slot,
no `s9` update). -/
def chainCost (i d : Nat) : Nat :=
  if d=topMax i then 4+tableJump i
  else 5+tableJump i+9*(topMax i-d)-(if d+1=topMax i then 1 else 0)

theorem chainCost_positive (i d : Nat) (hd : d< topMax i) :
    chainCost i d=5+tableJump i+preCost i d := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  unfold chainCost preCost
  rw [if_neg (by omega)]
  split_ifs <;> omega

theorem positive_head (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54)
    (hd : c.dig i< topMax i) (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃t,Steps vimage s (5+tableJump i) (5+tableJump i) t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  have hl : last i+1=topMax i := by have := topMax_bounds i;unfold last;omega
  have hsp := c.startPc_lt hds i hi
  by_cases htab : i%3=0
  · have hrun2 := c.chk_tail hds i (c.dig i) hi htab (by omega)
    have hrp : c.rungPc i (c.dig i)+1<210432 := by
      have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
      have hl2 := last_bounds i
      unfold rungPc qb
      rw [if_pos htab]
      omega
    by_cases ht : c.dig i=last i
    · have hrun1 := c.chk_headJTerm hds i hi htab ht
      obtain ⟨t,hst,htp⟩ := c.headJTerm_step hc hk h0 i hi ht hsp hrp hrun1 hrun2 acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
    · have hrun1 := c.chk_headJ hds i hi htab (by omega)
      obtain ⟨t,hst,htp⟩ := c.headJ_step hc hk h0 i hi (by omega) hsp hrp hrun1 hrun2 acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
  · by_cases ht : c.dig i=last i
    · have hrun := c.chk_headRTerm hds i hi htab ht
      have hr : c.rungPc i (c.dig i)=c.startPc i+3 := by rw [inline_rungPc c i htab,if_pos ht]
      obtain ⟨t,hst,htp⟩ := c.headRTerm_step hc hk h0 i hi ht hsp hr hrun acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
    · have hrun := c.chk_headR hds i hi htab (by omega)
      have hr : c.rungPc i (c.dig i)=c.startPc i+4 := by rw [inline_rungPc c i htab,if_neg ht]
      obtain ⟨t,hst,htp⟩ := c.headR_step hc hk h0 i hi (by omega) hsp hr hrun acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩

/-- One exact mixed-radix chain, ending before the next dispatch. -/
theorem chain_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K (acc++[v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+40) (C+chainCost i (c.dig i)) Q (A+chainCost i (c.dig i))
      (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (chainP 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i) (c.val i))
        (fun v => K (acc++[v]))) := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  have hd := hds i hi
  have hsp := c.startPc_lt hds i hi
  by_cases hmax : c.dig i=topMax i
  · rw [hmax,Nat.sub_self]
    have hp : chainP 0 c.tree c.leaf i (topMax i) 0 (c.pad0 i) (c.pad1 i) (c.val i)=pure (c.val i) := rfl
    rw [hp,SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_pure]
    by_cases htab : i%3=0
    · obtain ⟨t,hst,ht⟩ := c.copyN_step hc hk h0 i hi hsp
        (c.chk_copyJ hds i hi htab hmax) acc s hs
      exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hst (hK _ _ ht) (by omega) (by simp [chainCost,tableJump,htab])
        (fun hq => ⟨hq,by simp [chainCost,tableJump,htab]⟩)
    · obtain ⟨t,hst,ht⟩ := c.copyFH_step hc hk h0 i hi hsp
        (c.inline_copy_end i htab hmax) (c.chk_copyF hds i hi htab hmax) acc s hs
      exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hst (hK _ _ ht) (by omega) (by simp [chainCost,tableJump,htab])
        (fun hq => ⟨hq,by simp [chainCost,tableJump,htab]⟩)
  · have hd' : c.dig i< topMax i := by omega
    rw [chainP_rest]
    have H := c.steps_good hc hds hk h0 i hi acc K N C A Q hK (last i-c.dig i) (c.dig i) (by omega) (le_refl _)
    obtain ⟨t,hst,ht⟩ := c.positive_head hc hds hk h0 i hi hd' acc s hs
    have hj : tableJump i≤1 := by unfold tableJump;split <;> omega
    have he := chainCost_positive i (c.dig i) hd'
    exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hst (H _ _ ht) (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)

#print axioms chain_good
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart59

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart60

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-- The first two chains of each triple fall through to the following inline chain. -/
theorem next_inline (c : NCtx) (s0 : MachineState) (i : Nat) (hi : i<54) (h2 : i%3≠2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    c.ChainIn s0 (i+1) acc s := by
  obtain ⟨hB,hlen,hpc⟩ := hs
  refine ⟨hB,hlen,?_⟩
  rw [hpc]
  unfold endPc startPc
  have e : (i+1)/3=i/3 := by omega
  by_cases h0 : i%3=0
  · rw [if_pos h0,if_neg (show (i+1)%3≠0 by omega),if_pos (show (i+1)%3=1 by omega)]
    unfold qB;rw [e]
  · rw [if_neg h0,if_pos (show i%3=1 by omega),if_neg (show (i+1)%3≠0 by omega),
      if_neg (show (i+1)%3≠1 by omega)]
    unfold qC;rw [e]

def chainF (c : NCtx) (ends : List Digest) (i : Nat) : M (List Digest) := do
  let v ← chainP 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i) (c.val i)
  pure (ends++[v])

def chainsCost (c : NCtx) (i k : Nat) : Nat :=
  ((List.range' i k).map fun j => chainCost j (c.dig j)).sum

/-- Finish a nonempty suffix of one triple, before its four-instruction dispatch. -/
theorem group_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (q : Nat) (hq : q<18) (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t,c.EndInv s0 (3*q+2) ends t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K ends)) :
    ∀ k i, 3*q ≤ i → i+k = 3*q+3 → 0 < k → ∀ acc s, c.ChainIn s0 i acc s →
      SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+40*k) (C+c.chainsCost i k) Q (A+c.chainsCost i k)
        (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero => intro i _ _ h;omega
  | succ k ih =>
    intro i hi hik _ acc s hs
    rw [List.range'_succ,List.foldlM_cons]
    simp only [chainF,bind_assoc,pure_bind,SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_bind]
    have H := c.chain_good hc hds hk h0 i (by omega) acc
      (fun ends => SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' (i+1) k).foldlM c.chainF ends) K)
      (N+40*k) (C+c.chainsCost (i+1) k) (A+c.chainsCost (i+1) k) Q
      (fun v t ht => by
        by_cases hk0 : k=0
        · subst hk0
          have he : i=3*q+2 := by omega
          rw [he] at ht
          simpa [chainsCost] using hK _ t ht
        · have ht' : c.ChainIn s0 (i+1) (acc++[v]) t := c.next_inline s0 i (by omega) (by omega) (acc++[v]) t ht
          exact ih (i+1) (by omega) (by omega) (by omega) (acc++[v]) t ht') s hs
    refine H.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart60

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart61

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def Fit (c : NCtx) (v : Digest) : Prop := ∀i,i<54 → c.dig i=coreDigit 0 v i

theorem fit_digits (c : NCtx) {v : Digest} (hf : c.Fit v) : c.DigitsOk := by
  intro i hi
  rw [hf i hi]
  have h := T3.Nonbinary.coreDigit_le 0 v i
  simpa [maxDigit,topMax,mx,show (i/3<17)↔i<51 by omega] using h

theorem fit_rank (c : NCtx) {v : Digest} (hf : c.Fit v) (hv : topRanksValid v=true)
    (q : Nat) (hq : q<17) : c.kOf q=Search.topRank v q := by
  have hr := T3.Nonbinary.top_rank_lt v hv q hq
  unfold kOf
  rw [hf (3*q) (by omega),hf (3*q+1) (by omega),hf (3*q+2) (by omega)]
  have h0 := T3.Nonbinary.top_core_triple v q 0 hq (by decide)
  have h1 := T3.Nonbinary.top_core_triple v q 1 hq (by decide)
  have h2 := T3.Nonbinary.top_core_triple v q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0,h1,h2]
  simp only [mx,if_pos hq,Nat.reduceAdd,Nat.reducePow,Nat.div_one]
  unfold Search.topRank
  omega

theorem fit_tail (c : NCtx) {v : Digest} (hf : c.Fit v) (hv : v.toNat<2^125) :
    c.kOf 17=v.toNat/2^119 := by
  unfold kOf
  rw [hf 51 (by decide),hf 52 (by decide),hf 53 (by decide)]
  norm_num [mx,coreDigit]
  omega


theorem decode_facts {v : Digest} {ds : List Nat} (h : decode 0 v=some ds) :
    v.toNat<2^125 ∧ topRanksValid v=true ∧ (Search.topDigits v).sum=126 := by
  rw [Search.decode_top] at h
  split_ifs at h with hgood
  · exact hgood

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart61

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart62

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

structure Encoded (v : Digest) (s : MachineState) : Prop where
  lo : s.getReg .x16=v.extractLsb' 0 64
  hi : s.getReg .x17=v.extractLsb' 63 64
  tail : s.getReg .x29=BitVec.ofNat 64 (v.toNat/2^119)
  mask : s.getReg .x24=130048#64
  table : s.getReg .x15=712704#64

theorem dispatch_at (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<18) :
    vrun (c.endPc (3*q+2)) 5=some (if q<16 then dispatchR (q+1) else if q=16 then tailDispatchR else retR) := by
  have hh := c.blk_at hds (3*q+2) (by omega)
  unfold blockCheck at hh
  simp only [Bool.and_eq_true] at hh
  have h := rOK_eq hh.2
  have eq : (3*q+2)/3=q := by omega
  simpa only [dispatchOK,endPc,qX,eq,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff] using h

/-- Between the first seventeen triples, only x14 changes. -/
theorem end_dispatch (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (hv : topRanksValid v=true)
    (q : Nat) (hq : q<16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃t,Steps vimage s 4 4 t ∧ c.ChainIn s0 (3*(q+1)) acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds q (by omega)
  rw [if_pos hq] at hr
  have hbound : c.endPc (3*q+2)<210432 := by
    have := c.qX_lt (3*q+2)
    simpa only [endPc,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff] using (show c.qX (3*q+2)<210432 by omega)
  obtain ⟨t,st,pt,rt,ft⟩ := dispatch_step (by omega) hbound hr s v hpc
    ((hR _ (by decide)).trans he.lo) ((hR _ (by decide)).trans he.hi)
    ((hR _ (by decide)).trans he.mask) ((hR _ (by decide)).trans he.table)
  refine ⟨t,st,⟨⟨fun x hx => ?_,(hF.trans ft).mono (by intro A hA h;rcases h with h|h;simpa only [show 3*q+2+1=3*(q+1) by omega] using h;contradiction),fun j hj => ?_⟩,by omega,?_⟩⟩
  · rw [rt.get (by intro h;simp only [List.mem_singleton] at h;subst x;exact hx (by decide))]
    exact hR x hx
  · exact (hS j hj).frame ft (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [pt]
    unfold startPc
    rw [if_pos (show 3*(q+1)%3=0 by omega),show 3*(q+1)/3=q+1 by omega,c.fit_rank hf hv (q+1) (by omega)]

/-- Changing this unused initial register preserves the original witness. -/
def tailInitial (s0 t : MachineState) : MachineState := s0.setReg .x15 (t.getReg .x15)

theorem tailInitial_mem (s0 t : MachineState) (a : Word) :
    (tailInitial s0 t).getMem a=s0.getMem a := rfl

theorem tailInitial_regs (s0 t : MachineState) (r : Reg) (hr : r≠.x15) :
    (tailInitial s0 t).getReg r=s0.getReg r := by
  unfold tailInitial
  rw [setReg_of_ne s0 _ (by decide)]
  cases r <;> simp_all [MachineState.getReg]

theorem tailInitial_15 (s0 t : MachineState) :
    (tailInitial s0 t).getReg .x15=t.getReg .x15 := by
  unfold tailInitial
  rw [setReg_of_ne s0 _ (by decide)]
  rfl

theorem tailInitial_known (c : NCtx) {s0 t : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) :
    ∀p∈c.known,(tailInitial s0 t).getReg p.1=p.2 := by
  intro p hp
  rw [tailInitial_regs _ _ _ (by rcases p with ⟨r,w⟩;simp only [known,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp;rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,_⟩ := h <;> simp)]
  exact hk p hp

theorem tailInitial_orig (c : NCtx) {s0 t : MachineState} (h0 : c.Orig0 s0) :
    c.Orig0 (tailInitial s0 t) := by
  refine ⟨fun i hi k hk => h0.1 i hi k hk, h0.2.congr (fun A _ _ => tailInitial_mem s0 t _)⟩

/-- The final radix-four table changes x15; the baseline rebase preserves memory exactly. -/
theorem end_tail (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 50 acc s) :
    ∃t,Steps vimage s 4 4 t ∧ c.ChainIn (tailInitial s0 t) 51 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds 16 (by decide)
  norm_num at hr
  have hbound : c.endPc 50<210432 := by
    have := c.qX_lt 50
    simpa only [endPc,Nat.reduceMod,if_false,Nat.reduceEqDiff] using (show c.qX 50<210432 by omega)
  obtain ⟨t,st,pt,rt,ft⟩ := tail_dispatch_step hbound hr s (v.toNat/2^119) (by omega) hpc
    ((hR _ (by decide)).trans he.tail)
  refine ⟨t,st,⟨⟨fun x hx => ?_,?_,fun j hj => ?_⟩,by omega,?_⟩⟩
  · by_cases hx15 : x=.x15
    · subst x;rw [tailInitial_15]
    · rw [tailInitial_regs _ _ _ hx15,rt.get (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or];exact ⟨fun h => hx (by rw [h];decide),hx15⟩)]
      exact hR x hx
  · intro A hA hn
    rw [tailInitial_mem]
    exact ft.get hA (by simp) |>.trans (hF.get hA hn)
  · exact (hS j hj).frame ft (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [pt]
    change pcOf (entW 17 (v.toNat/2^119))=pcOf (entW 17 (c.kOf 17))
    rw [c.fit_tail hf hv]

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart62

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart63

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfResearch.NonbinaryTop
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def digitCredit (i d : Nat) : Nat := if last i≤d then 1 else 0
def digitSum (f : Nat → Nat) : Nat := ((List.range 54).map f).sum
def creditSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => digitCredit i (f i)).sum
def totalCost (f : Nat → Nat) : Nat := ((List.range 54).map fun i => chainCost i (f i)).sum

theorem chainCost_balance (i d : Nat) (hd : d≤topMax i) :
    chainCost i d+9*d+digitCredit i d=5+tableJump i+9*topMax i := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  unfold chainCost digitCredit
  split_ifs <;> omega

theorem total_balance (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    totalCost f+9*digitSum f+creditSum f=2205 := by
  have H : ∀ l : List Nat,(∀i∈l,f i≤topMax i) →
      (l.map fun i => chainCost i (f i)).sum+9*(l.map f).sum+
        (l.map fun i => digitCredit i (f i)).sum=
        (l.map fun i => 5+tableJump i+9*topMax i).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := chainCost_balance i (f i) (h i (by simp))
      have ht := ih (fun j hj => h j (by simp [hj]))
      simp only [List.map_cons,List.sum_cons]
      omega
  have hs := H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))
  have he : ((List.range 54).map fun i => 5+tableJump i+9*topMax i).sum=2205 := by decide +kernel
  exact hs.trans he

/-- Exact cost of all chains, seventeen four-instruction dispatches, and the final jump. -/
theorem total_cost_credit (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i)
    (hs : digitSum f=126) : totalCost f+17*4+1+creditSum f=1140 := by
  have h := total_balance f hd
  omega

theorem range_map_ofFn (f : Nat → Nat) :
    (List.range 54).map f=List.ofFn (fun i : Fin 54 => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

theorem source_credit_parse {v : Digest} {w : Codec.Word}
    (hp : Decoder.parse 17 v.toNat=some w) : creditSum (coreDigit 0 v)=Cost.credit w := by
  unfold creditSum
  rw [range_map_ofFn,List.ofFn_add (n:=51) (m:=3),List.sum_append]
  change (List.ofFn fun i : Fin (17*3) => digitCredit i.val (coreDigit 0 v i.val)).sum+
      (List.ofFn fun k : Fin 3 => digitCredit (51+k.val) (coreDigit 0 v (51+k.val))).sum=Cost.credit w
  rw [List.ofFn_mul]
  simp only [List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  unfold Cost.credit Cost.credit5 Cost.credit4
  apply congrArg₂ Nat.add
  · apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    have he := T3.Nonbinary.coreDigit_parse5 hp j k
    have hl : last (j.val*3+k.val)=3 := by
      unfold last topMax mx
      rw [if_pos (by have := j.isLt;have := k.isLt;omega)]
    simpa only [digitCredit,hl,Nat.mul_comm] using congrArg (fun d => if 3≤d then (1:Nat) else 0) he
  · apply Finset.sum_congr rfl
    intro k hk
    have he := T3.Nonbinary.coreDigit_parse4 hp k
    have hl : last (51+k.val)=2 := by
      unfold last topMax mx
      rw [if_neg (by have := k.isLt;omega)]
    simpa only [digitCredit,hl] using congrArg (fun d => if 2≤d then (1:Nat) else 0) he

theorem source_accepted_credit {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : 11≤creditSum (coreDigit 0 v) := by
  obtain ⟨w,hw,_,_,hc⟩ := T3.Nonbinary.decode_top_credit h
  have hp : Decoder.parse 17 v.toNat=some w := by
    change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=126))=some w at hw
    exact (Option.filter_eq_some_iff.mp hw).1
  rw [source_credit_parse hp]
  exact hc

theorem source_accepted_sum {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : digitSum (coreDigit 0 v)=126 := by
  obtain ⟨w,hw,_,hs,_⟩ := T3.Nonbinary.decode_top_credit h
  have hp : Decoder.parse 17 v.toNat=some w := by
    change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=126))=some w at hw
    exact (Option.filter_eq_some_iff.mp hw).1
  change (dataDigits 0 v).sum=126
  rw [T3.Nonbinary.dataDigits_parse hp,T3.Nonbinary.wordDigits_sum,hs]

theorem source_accepted_total {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : totalCost (coreDigit 0 v)+17*4+1≤1129 := by
  have hd : ∀i,i<54 → coreDigit 0 v i≤topMax i := by
    intro i hi
    have hc := T3.Nonbinary.coreDigit_le (0:Layer) v i
    have he : maxDigit 0 i=topMax i := by
      unfold maxDigit topMax mx
      simp only [ite_true]
      split_ifs <;> omega
    rw [he] at hc
    exact hc
  have hb := total_cost_credit (coreDigit 0 v) hd (source_accepted_sum h)
  have hc := source_accepted_credit h
  omega

#print axioms total_cost_credit
#print axioms source_accepted_total
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart63

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart64

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def TopOut (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x15 → s.getReg x=s0.getReg x) ∧
  Frame s0 s (c.Wr 54) ∧ acc.length=54 ∧
  (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0)) ∧ s.pc=pcOf c.ret

theorem end_return (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 b : MachineState}
    (hk : ∀ p ∈ c.known, s0.getReg p.1=p.2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv (tailInitial s0 b) 53 acc s) :
    ∃ t, Steps vimage s 1 1 t ∧ c.TopOut s0 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds 17 (by decide)
  norm_num at hr
  have hp : c.endPc 53 < 210432 := by
    have := c.qX_lt 53
    simpa only [endPc,Nat.reduceMod,if_false,Nat.reduceEqDiff] using (show c.qX 53<210432 by omega)
  have st := piece_steps45 hr hp s hpc (by simp [retR])
  have h1 : s.getReg .x1=pcOf c.ret :=
    (hR .x1 (by decide)).trans ((tailInitial_regs _ _ _ (by decide)).trans (hk (.x1,pcOf c.ret) (by simp [known])))
  refine ⟨retR.toState s,st,⟨fun x hx hx15 => ?_,?_,hlen,?_,?_⟩⟩
  · exact (retR_keeps.reg s (by simp)).trans ((hR x hx).trans (tailInitial_regs _ _ _ hx15))
  · intro A hA hn
    exact hF A hA hn
  · intro j hj;exact hS j hj
  · rw [Result.toState_pc]
    simp only [retR,E.eval,BinOp.eval,h1]
    exact even_andNot1' _ (by have := hc.2.2.2.2.2;omega)

theorem chainsCost_add (c : NCtx) (i n k : Nat) :
    c.chainsCost i (n+k)=c.chainsCost i n+c.chainsCost (i+n) k := by
  unfold chainsCost
  rw [← List.range'_append_1,List.map_append,List.sum_append]

/-- The seventeen radix-five triples, with only the sixteen intervening dispatches. -/
theorem prefix_good (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : topRanksValid v=true)
    (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv s0 50 acc t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K acc)) :
    ∀ n q, n+q=17 → 0<n → ∀ acc s,c.ChainIn s0 (3*q) acc s →
      SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+124*n) (C+c.chainsCost (3*q) (3*n)+4*(n-1)) Q
        (A+c.chainsCost (3*q) (3*n)+4*(n-1))
        (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' (3*q) (3*n)).foldlM c.chainF acc) K) := by
  intro n
  induction n with
  | zero => intro q _ h;omega
  | succ n ih =>
    intro q hn _ acc s hs
    have hd := c.fit_digits hf
    by_cases hz : n=0
    · subst n
      have hq : q=16 := by omega
      subst q
      have H := c.group_good hc hd hk h0 16 (by decide) K N C A Q hK 3 48 (by decide) (by decide) (by decide) acc s hs
      exact H.mono (by omega) (by simp) (fun h => ⟨h,by simp⟩)
    · rw [show 3*(n+1)=3+3*n by omega,← List.range'_append_1,List.foldlM_append,SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_bind]
      have H := c.group_good hc hd hk h0 q (by omega)
        (fun ends => SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' (3*q+3) (3*n)).foldlM c.chainF ends) K)
        (N+124*n+4) (C+c.chainsCost (3*(q+1)) (3*n)+4*(n-1)+4)
        (A+c.chainsCost (3*(q+1)) (3*n)+4*(n-1)+4) Q
        (fun ends t ht => by
          obtain ⟨u,st,hu⟩ := c.end_dispatch hc hd he hf hv q (by omega) ends t ht
          have H := ih (q+1) (by omega) (by omega) ends u hu
          rw [show 3*(q+1)=3*q+3 by omega] at H
          exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps st H)
        3 (3*q) (le_refl _) (by omega) (by decide) acc s hs
      have ec := c.chainsCost_add (3*q) 3 (3*n)
      rw [show 3*q+3=3*(q+1) by omega] at ec
      exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)

def topP (c : NCtx) : M (List Digest) := (List.range' 0 54).foldlM c.chainF []

/-- All 54 mixed-radix chains, seventeen dispatches and the return instruction. -/
theorem top_good_exact (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125) (hr : topRanksValid v=true)
    (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K acc))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+2321) (C+c.chainsCost 0 54+69) Q (A+c.chainsCost 0 54+69)
      (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM c.topP K) := by
  have hd := c.fit_digits hf
  unfold topP
  rw [show (54:Nat)=51+3 from rfl,← List.range'_append_1,List.foldlM_append,SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_bind]
  have H := c.prefix_good hc hk h0 he hf hr
    (fun ends => SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' 51 3).foldlM c.chainF ends) K)
    (N+125) (C+c.chainsCost 51 3+5) (A+c.chainsCost 51 3+5) Q
    (fun ends t ht => by
      obtain ⟨u,st,hu⟩ := c.end_tail hc hd he hf hv ends t ht
      have H := c.group_good hc hd (c.tailInitial_known hk) (c.tailInitial_orig h0) 17 (by decide)
        K (N+1) (C+1) (A+1) Q
        (fun acc t ht => by
          obtain ⟨u,st,hu⟩ := c.end_return hc hd hk acc t ht
          exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps st (hK acc u hu))
        3 51 (by decide) (by decide) (by decide) ends u hu
      have H := SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps st H
      exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩))
    17 0 (by decide) (by decide) [] s hs
  have ec := c.chainsCost_add 0 51 3
  norm_num only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] at ec H ⊢
  exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)

theorem top_good (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest} {ds : List Nat}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : decode 0 v=some ds)
    (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K acc))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+2321) (C+1129) Q (A+1129) (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM c.topP K) := by
  have hd := decode_facts hv
  have H := c.top_good_exact hc hk h0 he hf hd.1 hd.2.1 K N C A Q hK s hs
  have e : c.chainsCost 0 54=totalCost (coreDigit 0 v) := by
    unfold chainsCost totalCost
    rw [← List.range_eq_range']
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [hf i (List.mem_range.mp hi)]
  have hb := source_accepted_total hv
  rw [e] at H
  exact H.mono (le_refl _) (by omega) (fun h => ⟨h,by omega⟩)

#print axioms top_good
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart64

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart65

/-! Seven-instruction lane sum, adapted from accepted i34-9 PR283.
The T3 top two-bit variant and relaxed first-word bound are proved here. -/
namespace SigGolfCandidate.T3M.CanonicalPort.Verify

/-- Splitting a word by a mask and its complement: the parts have disjoint bits, so they add up to the word. -/
theorem swar7_split (x m : BitVec 64) : (x &&& m) + (x &&& ~~~m) = x := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]; cases x[i] <;> cases m[i] <;> rfl
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]; cases x[i] <;> cases m[i] <;> rfl

/-- `M1` has period 6 with three set bits: bit `i` is set exactly when bit `i + 3` is clear. -/
theorem swar7_period : ∀ i : Fin 61,
    (0x71c71c71c71c71c7#64).getLsbD i.val = !(0x71c71c71c71c71c7#64).getLsbD (i.val + 3) := by
  decide

/-- `(x >>> 3) & M1` is the odd-digit part `x & ~M1` shifted down by three. -/
theorem swar7_shift (x : BitVec 64) :
    (x >>> 3) &&& 0x71c71c71c71c71c7#64 = (x &&& ~~~0x71c71c71c71c71c7#64) >>> 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 61
  · have hp := swar7_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 3 + i = i + 3 by omega]
    simp [show i + 3 < 64 by omega]
  · have hx : x.getLsbD (3 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]

/-- The odd-digit part `x & ~M1` is a multiple of 8 (bits 0..2 belong to `M1`). -/
theorem swar7_low (x : BitVec 64) : (x &&& ~~~0x71c71c71c71c71c7#64).toNat % 8 = 0 := by
  have h7 : (x &&& ~~~0x71c71c71c71c71c7#64) &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 3
    · have : (0x71c71c71c71c71c7#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide
      simp [this]
    · have : (7#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 7 < 2 ^ 3 := by decide
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (7#64).toNat = 2 ^ 3 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this

/-- The 7-step lane word equals the reference one when only the second word is below `2^63`: the odd-digit parts
`A - (A & M1)`, `B - (B & M1)` are multiples of 8 and their sum does not wrap. -/
theorem swar7_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 63) :
    ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64)) +
      (((a + b) - ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64))) >>> 3) =
    ((a >>> 3) &&& 0x71c71c71c71c71c7#64) + (a &&& 0x71c71c71c71c71c7#64) +
      ((b >>> 3) &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64) := by
  rw [swar7_shift a, swar7_shift b]
  set M : BitVec 64 := 0x71c71c71c71c71c7#64 with hM
  have la := swar7_low a
  have lb := swar7_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0x8e38e38e38e38e38 := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat ≤ 0x0e38e38e38e38e38 := by
    have hb' : b.toNat % 2 ^ 63 = b.toNat := Nat.mod_eq_of_lt hb
    have he := Nat.and_mod_two_pow (a := b.toNat) (b := (~~~M).toNat) (n := 63)
    rw [hb', Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left hb)] at he
    rw [BitVec.toNat_and, he]
    simpa [hM] using (Nat.and_le_right : b.toNat &&& ((~~~M).toNat % 2 ^ 63) ≤ (~~~M).toNat % 2 ^ 63)
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 3 = ((a &&& ~~~M) >>> 3) + ((b &&& ~~~M) >>> 3) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl


/-- `M4` has period 4 with two set bits: bit `i` is set exactly when bit `i + 2` is clear. -/
theorem swar2_period : ∀ i : Fin 62,
    (0x3333333333333333#64).getLsbD i.val = !(0x3333333333333333#64).getLsbD (i.val + 2) := by
  decide

/-- `(x >>> 2) & M4` is the odd-digit part `x & ~M4` shifted down by two. -/
theorem swar2_shift (x : BitVec 64) :
    (x >>> 2) &&& 0x3333333333333333#64 = (x &&& ~~~0x3333333333333333#64) >>> 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 62
  · have hp := swar2_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 2 + i = i + 2 by omega]
    simp [show i + 2 < 64 by omega]
  · have hx : x.getLsbD (2 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]

/-- The odd-digit part `x & ~M4` is a multiple of 4 (bits 0..1 belong to `M4`). -/
theorem swar2_low (x : BitVec 64) : (x &&& ~~~0x3333333333333333#64).toNat % 4 = 0 := by
  have h7 : (x &&& ~~~0x3333333333333333#64) &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 2
    · have : (0x3333333333333333#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
      simp [this]
    · have : (3#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 3 < 2 ^ 2 := by decide
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (3#64).toNat = 2 ^ 2 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this

/-- The 7-step lane word equals the reference one when only the second word is below `2^34`: the odd-digit parts
`A - (A & M4)`, `B - (B & M4)` are multiples of 4 and their sum does not wrap. -/
theorem swar2_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 34) :
    ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64)) +
      (((a + b) - ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64))) >>> 2) =
    ((a >>> 2) &&& 0x3333333333333333#64) + (a &&& 0x3333333333333333#64) +
      ((b >>> 2) &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64) := by
  rw [swar2_shift a, swar2_shift b]
  set M : BitVec 64 := 0x3333333333333333#64 with hM
  have la := swar2_low a
  have lb := swar2_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0xcccccccccccccccc := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat < 2 ^ 34 := by
    rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_left hb
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 2 = ((a &&& ~~~M) >>> 2) + ((b &&& ~~~M) >>> 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl


end SigGolfCandidate.T3M.CanonicalPort.Verify

end CanonicalPortPart65
