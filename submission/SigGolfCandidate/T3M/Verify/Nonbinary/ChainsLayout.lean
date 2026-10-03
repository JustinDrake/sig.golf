import SigGolfCandidate.T3M.Verify.ChainRuns

/-! Exact mixed-radix top-chain code layout and symbolic result specifications. -/
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 200000
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

/-! T3Z on the Frodan layout: during the top chain phase `t3 = tBank = HDATA + 2049` (the layer-1 leaf
return's `sub t3, t3, s2` from the layer-1 bank midpoint `headerBank 1 0`). A head reads the header word of chain
`i`, first digit `d` (bank-0 byte `64 i + 8 d`) with `ld s9, (64 i + 8 d - 2049)(t3)`; the one word whose offset
would be `-2049` (chain 0, digit 0: `0x101`) is `mv s9, s11` instead (`s11 = 0x101` on the top layer). -/

/-- The top chain phase's table pointer (`Verify.topBank` in `LayerRuns`). -/
def tBank : Nat := 16728064 + 2049

/-- The 12-bit load offset of header word `(i, d)` from `t3 = HDATA + 2049`. -/
def tOff (i d : Nat) : Word := BitVec.ofNat 64 (64 * i + 8 * d) - 2049
def tKey (i d : Nat) : Addr := ⟨some (.reg .x28), tOff i d⟩
/-- The head's header word: a table load, or `s11` for chain 0 / digit 0. -/
def tLd (i d : Nat) : E := if i = 0 ∧ d = 0 then .reg .x27 else .ld (addC (.reg .x28) (tOff i d))
def tObl (i d : Nat) : List Oblig := if i = 0 ∧ d = 0 then [] else [.valid (tKey i d) 8]

/-- T3Z: an inline head loading the header with its first digit `d` from the table (no byte store), up to the
first `ecall` (5 or 6 steps from `p`). -/
def headRH (rb : Reg) (o : Word) (d : Nat) (slot : Option Nat) (p i : Nat) : Result :=
  let n := if slot.isSome then 6 else 5
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) o)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) o) 48)).set .x25 (tLd i d),
    [(kAt rb o 24, .reg .x4), (kAt rb o 16, tLd i d)],
    [.valid (kAt rb o 24) 8, .valid (kAt rb o 16) 8] ++ tObl i d⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩

/-- T3Z: an inline max-digit copy without the bump, stopped after its 4 instructions. -/
def copyFH (rb : Reg) (o : Word) (slot : Nat) (p : Nat) : Result :=
  ⟨⟨copyRegs rb o, copyMem rb o slot, copyObl rb o⟩, .c (pcOf (p + 4)), .fuel, 4, 4⟩

/-- T3Z (BIG3): a table-slot head loading the header word of chain `i` with its first digit `d` from the header
table (`addi a0; addi a2, a0, 48; ld s9, tOff i d(t3); sd s9, 16(a0); sd tp, 24(a0)`), then `j tgt` past the first
rung's `sb` (6 steps). -/
def headJD (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) o)).set .x12 (addC (addC (.reg rb) o) 48)).set .x25 (tLd i d),
    [(kAt rb o 24,.reg .x4),(kAt rb o 16,tLd i d)],
    [.valid (kAt rb o 24) 8,.valid (kAt rb o 16) 8] ++ tObl i d⟩,.c (pcOf tgt),.jump,6,6⟩

/-- T3Z: the table-slot head for the penultimate digit (no `addi a2, a0, 48`: its terminal rung sets x12), the
header word with the first digit `d` read from the table, then `j tgt` (5 steps). -/
def headJDTerm (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  ⟨⟨(RegFile.init.set .x10 (addC (.reg rb) o)).set .x25 (tLd i d),
    [(kAt rb o 24,.reg .x4),(kAt rb o 16,tLd i d)],
    [.valid (kAt rb o 24) 8,.valid (kAt rb o 16) 8] ++ tObl i d⟩,.c (pcOf tgt),.jump,5,5⟩

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
    Steps Images.verifyImage s r.steps r.cycles (r.toState s) :=
  symRun_sound h (lcodeAt p (by omega)) s hpc ((Oblig.all_iff _ _).mpr ho)

theorem piece_ecall45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<210432) (s : MachineState) (ho : ∀o∈r.st.obl,o.holds s)
    (hst : r.stop=.ecall) :
    fetch Images.verifyImage (r.toState s)=some (.base .ECALL) :=
  symRun_ecall h (lcodeAt p (by omega)) s ((Oblig.all_iff _ _).mpr ho) hst

end SigGolfCandidate.T3M.Nonbinary
