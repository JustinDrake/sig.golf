import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Basic

set_option Elab.async false

/-! Numeric structural component: SiggolfPrefixStructure -/

namespace SiggolfPrefixCertificate

/-- Zero-length unary runs are permitted, including at the root and leaves. -/
inductive Tree (credit : Nat → Nat) : Nat → Nat → Nat → Nat → Prop
  | leaf (h : Nat) : Tree credit h 1 h (credit h)
  | fork (h a p q fl fr cl cr : Nat) (ha : a < h)
      (left : Tree credit (h-a-1) p fl cl)
      (right : Tree credit (h-a-1) q fr cr) :
      Tree credit h (p+q) (a+fl+fr) (credit a+cl+cr)

theorem Tree.leaves_pos {credit : Nat → Nat} {h k f c : Nat}
    (ht : Tree credit h k f c) : 0 < k := by
  induction ht with
  | leaf => omega
  | fork h a p q fl fr cl cr ha left right ihl ihr => omega

/-- Each table value is one plus a fold upper bound; zero denotes infeasibility. -/
structure Certificate (credit : Nat → Nat) (upper : Nat → Nat → Nat → Nat) : Prop where
  leaf : ∀ h, h≤14 → credit h≤39 → h+1≤upper h 1 (credit h)
  fork : ∀ h a p q cl cr, h≤14 → a<h → 0<p → 0<q → p+q≤15 →
    credit a+cl+cr≤39 → 0<upper (h-a-1) p cl → 0<upper (h-a-1) q cr →
    a+upper (h-a-1) p cl+upper (h-a-1) q cr-1≤upper h (p+q) (credit a+cl+cr)

theorem Tree.fold_bound {credit : Nat → Nat} {upper : Nat → Nat → Nat → Nat}
    (hc : Certificate credit upper) {h k f c : Nat} (ht : Tree credit h k f c)
    (hh : h≤14) (hk : k≤15) (hcc : c≤39) : f<upper h k c := by
  induction ht with
  | leaf h => have := hc.leaf h hh hcc; omega
  | fork h a p q fl fr cl cr ha left right ihl ihr =>
      have hp := left.leaves_pos
      have hq := right.leaves_pos
      have hl := ihl (by omega) (by omega) (by omega)
      have hr := ihr (by omega) (by omega) (by omega)
      have hs := hc.fork h a p q cl cr hh ha hp hq hk hcc (by omega) (by omega)
      omega

theorem cost_2413 {credit : Nat → Nat} {upper : Nat → Nat → Nat → Nat}
    (hc : Certificate credit upper)
    (hroot : ∀ c : Fin 40, 464+17*(upper 14 15 c.val-1)-c.val≤2413)
    {f c : Nat} (ht : Tree credit 14 15 f c) (hf : f≤117) :
    464+17*f-c≤2413 := by
  by_cases hcc : c≤39
  · have hb := ht.fold_bound hc (by omega) (by omega) hcc
    have hs := hroot ⟨c,by omega⟩
    simp only at hs
    omega
  · omega

end SiggolfPrefixCertificate

/-! Numeric structural component: SiggolfReverse2322Table -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def oldCredit (a : Nat) : Nat := (if a=0 then 1 else 0)
def credit (a : Nat) : Nat := oldCredit a+(if 3≤a then 1 else 0)

def row0 (k : Nat) : Nat := match k with
  | 1 => 2495375197299664176174612608
  | _ => 0

def row1 (k : Nat) : Nat := match k with
  | 1 => 4990750394599328352349225218
  | 2 => 2495375197299664176174596096
  | _ => 0

def row2 (k : Nat) : Nat := match k with
  | 1 => 7486125591898992528523837827
  | 2 => 7486125591898992528523837824
  | 3 => 4990750394599328352344997888
  | 4 => 2495375197299659743497814016
  | _ => 0

def row3 (k : Nat) : Nat := match k with
  | 1 => 9981500789198656704698450432
  | 2 => 12476875986498320880873063044
  | 3 => 12476875986498320880873062400
  | 4 => 12476875986498320880872980480
  | 5 => 9981500789198656566177300480
  | 6 => 7486125591681117598519394304
  | 7 => 4990445783369189233187094528
  | _ => 0

def row4 (k : Nat) : Nat := match k with
  | 1 => 12476875986498320880873063040
  | 2 => 17467626381097649233222271750
  | 3 => 19963001578397313409396884224
  | 4 => 22458376775696977585571496832
  | 5 => 22458376775696977585569267712
  | 6 => 22458376775696977585284055040
  | 7 => 22458376775696977273898926080
  | 8 => 22458376775696937691480326144
  | 9 => 19963001504029337301213511680
  | 10 => 17331160549995323848587739136
  | _ => 0

def row5 (k : Nat) : Nat := match k with
  | 1 => 14972251183797985057047675648
  | 2 => 22458376775696977585571496839
  | 3 => 27449127170296305937650189312
  | 4 => 32439877564895629857591051656
  | 5 => 34935252762195294033765646336
  | 6 => 37430627959494958209940258816
  | 7 => 39926003156794622351213854720
  | 8 => 42421378354094286527388450816
  | 9 => 42421378354093719141243420672
  | 10 => 42421378354021093718169223168
  | 11 => 42421378344717158265324044288
  | 12 => 42421377153821301600489046016
  | 13 => 42421207010277337740439715840
  | 14 => 42399446345524274415295004672
  | _ => 0

def row6 (k : Nat) : Nat := match k with
  | 1 => 17467626381097649233222288256
  | 2 => 27449127170296305937920721920
  | 3 => 34935252762195298466171913600
  | 4 => 42421378354094286527659198092
  | 5 => 47412128748620994335748621824
  | 6 => 52402877953404762585829754624
  | 7 => 57374134409867370979435724800
  | 8 => 59888852429504245657311152000
  | 9 => 62384227626803909833208627200
  | 10 => 64879602824103574009383223296
  | 11 => 67374978021402666369676214272
  | 12 => 69870353218702330545848713216
  | 13 => 72365727216818379216553771008
  | 14 => 74861102414118043358098096128
  | 15 => 74841607295389038611282264064
  | _ => 0

def row7 (k : Nat) : Nat := match k with
  | 1 => 19963001578397313409396900864
  | 2 => 32439877564895634290269947008
  | 3 => 42421378354094290994693621376
  | 4 => 52402879143292943232087082766
  | 5 => 59889004735118747833989367680
  | 6 => 67375129127906746196677675279
  | 7 => 74841608485277325641780660224
  | 8 => 77356477620713709776698477456
  | 9 => 82327885192975827627346870272
  | 10 => 87318484471775646522653687808
  | 11 => 89833353607212030657294237696
  | 12 => 92328881100903387958419554304
  | 13 => 97300137566589368318809866240
  | 14 => 99814855586298305023395758080
  | 15 => 102310381899397465324170248192
  | _ => 0

def row8 (k : Nat) : Nat := match k with
  | 1 => 22458376775696977585571513472
  | 2 => 37430627959494962642619172096
  | 3 => 49907503945993283523217442560
  | 4 => 62384379932491599936246548367
  | 5 => 72365880721617059884134910336
  | 6 => 82347380311632106208067160592
  | 7 => 92309233676486789760897420160
  | 8 => 97299984071086118113515064728
  | 9 => 102290734465685446465866370048
  | 10 => 107281484860284774818213514752
  | 11 => 109796355176313342620766519296
  | 12 => 114767762757798836906320531072
  | 13 => 119758362036670713430018588672
  | 14 => 122273231172107660514892009216
  | 15 => 127244638744369782763851071488
  | _ => 0

def row9 (k : Nat) : Nat := match k with
  | 1 => 24953751972996641761746126080
  | 2 => 42421378354094290994968397184
  | 3 => 57393629537892276051741261824
  | 4 => 72365880721690256640940787712
  | 5 => 84842756708115380695749479168
  | 6 => 97319631495429523881943534464
  | 7 => 109776860048288437547915742592
  | 8 => 117262984459523188746048982684
  | 9 => 122253736034786195478569045632
  | 10 => 127244486438609458818263322653
  | 11 => 132235236833280849162430664448
  | 12 => 137225987227880736101312910110
  | 13 => 142216737622408015621630103424
  | 14 => 147207488017078838686512763807
  | 15 => 152198238411678725556948144128
  | _ => 0

def row10 (k : Nat) : Nat := match k with
  | 1 => 27449127170296305937920738688
  | 2 => 47412128748693619347317622272
  | 3 => 64879755129791268580265082880
  | 4 => 82347381510888913345635010688
  | 5 => 97319632694613701541721672704
  | 6 => 112291882679226937157773380736
  | 7 => 127244486429240836793439850112
  | 8 => 137225984838808377656485629726
  | 9 => 144692465386067133384696090880
  | 10 => 149702709718802618745839260063
  | 11 => 157169492479069534091723035392
  | 12 => 162179434580278625515172713767
  | 13 => 167170487215628282792290047360
  | 14 => 174637120049982180477530576424
  | 15 => 179647212086399156242294347648
  | _ => 0

def row11 (k : Nat) : Nat := match k with
  | 1 => 29944502367595970114095351296
  | 2 => 52402879143292947699666847360
  | 3 => 72365880721690261108788903936
  | 4 => 92328882300087570050331314432
  | 5 => 109796508681112022387693882496
  | 6 => 127264133863024913349733780736
  | 7 => 144712112810337351226773491456
  | 8 => 157188986407837064642742013855
  | 9 => 167150688666188798633825669888
  | 10 => 172141742482202138654534210464
  | 11 => 179627718138821184884010865536
  | 12 => 184637961281814302432655332904
  | 13 => 194580474204034944452711504128
  | 14 => 197114838467423045664866408873
  | 15 => 207057501306260721628999490432
  | _ => 0

def row12 (k : Nat) : Nat := match k with
  | 1 => 32439877564895634290269963904
  | 2 => 57393629537892276052016072448
  | 3 => 79852006313589253637312724992
  | 4 => 102310383089286226755027601792
  | 5 => 122273384667610343268294262784
  | 6 => 142236385046822893905110419968
  | 7 => 162179739191433865659836596224
  | 8 => 177151987986089123666123689984
  | 9 => 189609063062109973339729204352
  | 10 => 197075847021558801351173739776
  | 11 => 202085942608974015704148497664
  | 12 => 209572218117490042108025591680
  | 13 => 219534072681456278275791641344
  | 14 => 224524974210374480737518672768
  | 15 => 232011100973497043843462143360
  | _ => 0

def row13 (k : Nat) : Nat := match k with
  | 1 => 34935252762195298466444576512
  | 2 => 62384379932491604404365297536
  | 3 => 87338131905488246165836546048
  | 4 => 112291883878484883459723921920
  | 5 => 134750260654108664148892549120
  | 6 => 157208636230620878892624857728
  | 7 => 179647365572530943077210750976
  | 8 => 197114989564341178291456741504
  | 9 => 212067439819213826565127984512
  | 10 => 222029143267525222721131435520
  | 11 => 229496077171332141106720478720
  | 12 => 234506474971612521459333585024
  | 13 => 244487821094085496440456371200
  | 14 => 251973796750921269640273321088
  | 15 => 259440580719448241726817312384
  | _ => 0

def row (h k : Nat) : Nat := match h with
  | 0 => row0 k
  | 1 => row1 k
  | 2 => row2 k
  | 3 => row3 k
  | 4 => row4 k
  | 5 => row5 k
  | 6 => row6 k
  | 7 => row7 k
  | 8 => row8 k
  | 9 => row9 k
  | 10 => row10 k
  | 11 => row11 k
  | 12 => row12 k
  | 13 => row13 k
  | _ => 0

def upper (h k c : Nat) : Nat := (row h k / 128^c) % 128

def checkLeaf (h : Nat) : Bool := (List.range 14).all fun c =>
  decide (credit h ≤ c → h+1 ≤ upper h 1 c)
def checkFork (h k c : Nat) : Bool := (List.range h).all fun a =>
  if credit a > c then true else
    (List.range k).all fun p => if p=0 then true else
      (List.range (c-credit a+1)).all fun cl =>
        let cr := c-credit a-cl
        let ul := upper (h-a-1) p cl
        if ul=0 then true else
          let ur := upper (h-a-1) (k-p) cr
          decide (ur=0 ∨ a+ul+ur-1 ≤ upper h k c)
def checkHeight (h : Nat) : Bool := checkLeaf h &&
  (List.range 16).all fun k => (List.range 14).all fun c => checkFork h k c

def rootCheck : Bool := (List.range 14).all fun a =>
  (List.range 15).all fun p => if p=0 then true else
    (List.range 14).all fun cl =>
      (List.range (14-oldCredit a-cl)).all fun cr =>
        let ul := upper (13-a) p cl
        if ul=0 then true else
          let ur := upper (13-a) (15-p) cr
          decide (ur=0 ∨ 464+16*min 117 (a+ul+ur-2)-(oldCredit a+cl+cr) ≤ 2322)
end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Proof -/
namespace SiggolfReverse2322
open SiggolfPrefixCertificate
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000

structure Certificate : Prop where
  leaf : ∀ h, h≤13 → credit h≤13 → h+1≤upper h 1 (credit h)
  fork : ∀ h a p q cl cr, h≤13 → a<h → 0<p → 0<q → p+q≤15 →
    credit a+cl+cr≤13 → 0<upper (h-a-1) p cl → 0<upper (h-a-1) q cr →
    a+upper (h-a-1) p cl+upper (h-a-1) q cr-1≤upper h (p+q) (credit a+cl+cr)

theorem tree_fold_bound (hc : Certificate) {h k f c : Nat} (ht : Tree credit h k f c)
    (hh : h≤13) (hk : k≤15) (hcc : c≤13) : f<upper h k c := by
  induction ht with
  | leaf h => have := hc.leaf h hh hcc; omega
  | fork h a p q fl fr cl cr ha left right ihl ihr =>
      have hp := left.leaves_pos
      have hq := right.leaves_pos
      have hl := ihl (by omega) (by omega) (by omega)
      have hr := ihr (by omega) (by omega) (by omega)
      have hs := hc.fork h a p q cl cr hh ha hp hq hk hcc (by omega) (by omega)
      omega

theorem certificate_of_checks (checks : ∀ h, h≤13 → checkHeight h=true) : Certificate := by
  constructor
  · intro h hh hc
    have H := checks h hh
    simp only [checkHeight, Bool.and_eq_true] at H
    have HL := H.1
    simp only [checkLeaf, List.all_eq_true] at HL
    have HS := HL (credit h) (List.mem_range.mpr (by omega))
    simpa using HS
  · intro h a p q cl cr hh ha hp hq hpq hc hul hur
    have H := checks h hh
    simp only [checkHeight, Bool.and_eq_true] at H
    have HF := H.2
    simp only [List.all_eq_true] at HF
    have HF := HF (p+q) (List.mem_range.mpr (by omega)) (credit a+cl+cr)
      (List.mem_range.mpr (by omega))
    simp only [checkFork, List.all_eq_true] at HF
    have HA := HF a (List.mem_range.mpr ha)
    have hca : ¬credit a > credit a+cl+cr := by omega
    simp only [hca, ↓reduceIte, List.all_eq_true] at HA
    have HP := HA p (List.mem_range.mpr (by omega))
    have hp0 : ¬p=0 := by omega
    simp only [hp0, ↓reduceIte, List.all_eq_true] at HP
    have HC := HP cl (List.mem_range.mpr (by omega))
    have eqcr : credit a+cl+cr-credit a-cl=cr := by omega
    have eqq : p+q-p=q := by omega
    have hnul : ¬upper (h-a-1) p cl=0 := by omega
    simp only [eqcr, eqq, hnul, ↓reduceIte, decide_eq_true_eq] at HC
    omega

theorem root_bound_of_checks (hc : Certificate) (hcheck : rootCheck=true)
    {a p q fl fr cl cr : Nat} (ha : a<14) (hk : p+q=15)
    (left : Tree credit (14-a-1) p fl cl)
    (right : Tree credit (14-a-1) q fr cr) (hf : a+fl+fr≤117) :
    464+16*(a+fl+fr)-(oldCredit a+cl+cr)≤2322 := by
  by_cases hsmall : oldCredit a+cl+cr≤13
  · have hp := left.leaves_pos
    have hq := right.leaves_pos
    have hl := tree_fold_bound hc left (by omega) (by omega) (by omega)
    have hr := tree_fold_bound hc right (by omega) (by omega) (by omega)
    have hheight : 14-a-1=13-a := by omega
    rw [hheight] at hl hr
    simp only [rootCheck, List.all_eq_true] at hcheck
    have H := hcheck a (List.mem_range.mpr ha) p (List.mem_range.mpr (by omega))
    have hp0 : ¬p=0 := by omega
    simp only [hp0, ↓reduceIte, List.all_eq_true] at H
    have H := H cl (List.mem_range.mpr (by omega)) cr (List.mem_range.mpr (by omega))
    have hpq : 15-p=q := by omega
    have hleft : ¬upper (13-a) p cl=0 := by omega
    simp only [hpq, hleft, ↓reduceIte, decide_eq_true_eq] at H
    have hbound : a+fl+fr ≤ min 117 (a+upper (13-a) p cl+upper (13-a) q cr-2) :=
      Nat.le_min.mpr ⟨hf, by omega⟩
    omega
  · omega

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check0 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_0 : checkLeaf 0=true := by decide +kernel
theorem check_h0_k0 : (List.range 14).all (fun c => checkFork 0 0 c)=true := by decide +kernel
theorem check_h0_k1 : (List.range 14).all (fun c => checkFork 0 1 c)=true := by decide +kernel
theorem check_h0_k2 : (List.range 14).all (fun c => checkFork 0 2 c)=true := by decide +kernel
theorem check_h0_k3 : (List.range 14).all (fun c => checkFork 0 3 c)=true := by decide +kernel
theorem check_h0_k4 : (List.range 14).all (fun c => checkFork 0 4 c)=true := by decide +kernel
theorem check_h0_k5 : (List.range 14).all (fun c => checkFork 0 5 c)=true := by decide +kernel
theorem check_h0_k6 : (List.range 14).all (fun c => checkFork 0 6 c)=true := by decide +kernel
theorem check_h0_k7 : (List.range 14).all (fun c => checkFork 0 7 c)=true := by decide +kernel
theorem check_h0_k8 : (List.range 14).all (fun c => checkFork 0 8 c)=true := by decide +kernel
theorem check_h0_k9 : (List.range 14).all (fun c => checkFork 0 9 c)=true := by decide +kernel
theorem check_h0_k10 : (List.range 14).all (fun c => checkFork 0 10 c)=true := by decide +kernel
theorem check_h0_k11 : (List.range 14).all (fun c => checkFork 0 11 c)=true := by decide +kernel
theorem check_h0_k12 : (List.range 14).all (fun c => checkFork 0 12 c)=true := by decide +kernel
theorem check_h0_k13 : (List.range 14).all (fun c => checkFork 0 13 c)=true := by decide +kernel
theorem check_h0_k14 : (List.range 14).all (fun c => checkFork 0 14 c)=true := by decide +kernel
theorem check_h0_k15 : (List.range 14).all (fun c => checkFork 0 15 c)=true := by decide +kernel
theorem check_height_0 : checkHeight 0=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_0, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h0_k0
  · exact check_h0_k1
  · exact check_h0_k2
  · exact check_h0_k3
  · exact check_h0_k4
  · exact check_h0_k5
  · exact check_h0_k6
  · exact check_h0_k7
  · exact check_h0_k8
  · exact check_h0_k9
  · exact check_h0_k10
  · exact check_h0_k11
  · exact check_h0_k12
  · exact check_h0_k13
  · exact check_h0_k14
  · exact check_h0_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check1 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_1 : checkLeaf 1=true := by decide +kernel
theorem check_h1_k0 : (List.range 14).all (fun c => checkFork 1 0 c)=true := by decide +kernel
theorem check_h1_k1 : (List.range 14).all (fun c => checkFork 1 1 c)=true := by decide +kernel
theorem check_h1_k2 : (List.range 14).all (fun c => checkFork 1 2 c)=true := by decide +kernel
theorem check_h1_k3 : (List.range 14).all (fun c => checkFork 1 3 c)=true := by decide +kernel
theorem check_h1_k4 : (List.range 14).all (fun c => checkFork 1 4 c)=true := by decide +kernel
theorem check_h1_k5 : (List.range 14).all (fun c => checkFork 1 5 c)=true := by decide +kernel
theorem check_h1_k6 : (List.range 14).all (fun c => checkFork 1 6 c)=true := by decide +kernel
theorem check_h1_k7 : (List.range 14).all (fun c => checkFork 1 7 c)=true := by decide +kernel
theorem check_h1_k8 : (List.range 14).all (fun c => checkFork 1 8 c)=true := by decide +kernel
theorem check_h1_k9 : (List.range 14).all (fun c => checkFork 1 9 c)=true := by decide +kernel
theorem check_h1_k10 : (List.range 14).all (fun c => checkFork 1 10 c)=true := by decide +kernel
theorem check_h1_k11 : (List.range 14).all (fun c => checkFork 1 11 c)=true := by decide +kernel
theorem check_h1_k12 : (List.range 14).all (fun c => checkFork 1 12 c)=true := by decide +kernel
theorem check_h1_k13 : (List.range 14).all (fun c => checkFork 1 13 c)=true := by decide +kernel
theorem check_h1_k14 : (List.range 14).all (fun c => checkFork 1 14 c)=true := by decide +kernel
theorem check_h1_k15 : (List.range 14).all (fun c => checkFork 1 15 c)=true := by decide +kernel
theorem check_height_1 : checkHeight 1=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_1, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h1_k0
  · exact check_h1_k1
  · exact check_h1_k2
  · exact check_h1_k3
  · exact check_h1_k4
  · exact check_h1_k5
  · exact check_h1_k6
  · exact check_h1_k7
  · exact check_h1_k8
  · exact check_h1_k9
  · exact check_h1_k10
  · exact check_h1_k11
  · exact check_h1_k12
  · exact check_h1_k13
  · exact check_h1_k14
  · exact check_h1_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check2 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_2 : checkLeaf 2=true := by decide +kernel
theorem check_h2_k0 : (List.range 14).all (fun c => checkFork 2 0 c)=true := by decide +kernel
theorem check_h2_k1 : (List.range 14).all (fun c => checkFork 2 1 c)=true := by decide +kernel
theorem check_h2_k2 : (List.range 14).all (fun c => checkFork 2 2 c)=true := by decide +kernel
theorem check_h2_k3 : (List.range 14).all (fun c => checkFork 2 3 c)=true := by decide +kernel
theorem check_h2_k4 : (List.range 14).all (fun c => checkFork 2 4 c)=true := by decide +kernel
theorem check_h2_k5 : (List.range 14).all (fun c => checkFork 2 5 c)=true := by decide +kernel
theorem check_h2_k6 : (List.range 14).all (fun c => checkFork 2 6 c)=true := by decide +kernel
theorem check_h2_k7 : (List.range 14).all (fun c => checkFork 2 7 c)=true := by decide +kernel
theorem check_h2_k8 : (List.range 14).all (fun c => checkFork 2 8 c)=true := by decide +kernel
theorem check_h2_k9 : (List.range 14).all (fun c => checkFork 2 9 c)=true := by decide +kernel
theorem check_h2_k10 : (List.range 14).all (fun c => checkFork 2 10 c)=true := by decide +kernel
theorem check_h2_k11 : (List.range 14).all (fun c => checkFork 2 11 c)=true := by decide +kernel
theorem check_h2_k12 : (List.range 14).all (fun c => checkFork 2 12 c)=true := by decide +kernel
theorem check_h2_k13 : (List.range 14).all (fun c => checkFork 2 13 c)=true := by decide +kernel
theorem check_h2_k14 : (List.range 14).all (fun c => checkFork 2 14 c)=true := by decide +kernel
theorem check_h2_k15 : (List.range 14).all (fun c => checkFork 2 15 c)=true := by decide +kernel
theorem check_height_2 : checkHeight 2=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_2, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h2_k0
  · exact check_h2_k1
  · exact check_h2_k2
  · exact check_h2_k3
  · exact check_h2_k4
  · exact check_h2_k5
  · exact check_h2_k6
  · exact check_h2_k7
  · exact check_h2_k8
  · exact check_h2_k9
  · exact check_h2_k10
  · exact check_h2_k11
  · exact check_h2_k12
  · exact check_h2_k13
  · exact check_h2_k14
  · exact check_h2_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check3 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_3 : checkLeaf 3=true := by decide +kernel
theorem check_h3_k0 : (List.range 14).all (fun c => checkFork 3 0 c)=true := by decide +kernel
theorem check_h3_k1 : (List.range 14).all (fun c => checkFork 3 1 c)=true := by decide +kernel
theorem check_h3_k2 : (List.range 14).all (fun c => checkFork 3 2 c)=true := by decide +kernel
theorem check_h3_k3 : (List.range 14).all (fun c => checkFork 3 3 c)=true := by decide +kernel
theorem check_h3_k4 : (List.range 14).all (fun c => checkFork 3 4 c)=true := by decide +kernel
theorem check_h3_k5 : (List.range 14).all (fun c => checkFork 3 5 c)=true := by decide +kernel
theorem check_h3_k6 : (List.range 14).all (fun c => checkFork 3 6 c)=true := by decide +kernel
theorem check_h3_k7 : (List.range 14).all (fun c => checkFork 3 7 c)=true := by decide +kernel
theorem check_h3_k8 : (List.range 14).all (fun c => checkFork 3 8 c)=true := by decide +kernel
theorem check_h3_k9 : (List.range 14).all (fun c => checkFork 3 9 c)=true := by decide +kernel
theorem check_h3_k10 : (List.range 14).all (fun c => checkFork 3 10 c)=true := by decide +kernel
theorem check_h3_k11 : (List.range 14).all (fun c => checkFork 3 11 c)=true := by decide +kernel
theorem check_h3_k12 : (List.range 14).all (fun c => checkFork 3 12 c)=true := by decide +kernel
theorem check_h3_k13 : (List.range 14).all (fun c => checkFork 3 13 c)=true := by decide +kernel
theorem check_h3_k14 : (List.range 14).all (fun c => checkFork 3 14 c)=true := by decide +kernel
theorem check_h3_k15 : (List.range 14).all (fun c => checkFork 3 15 c)=true := by decide +kernel
theorem check_height_3 : checkHeight 3=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_3, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h3_k0
  · exact check_h3_k1
  · exact check_h3_k2
  · exact check_h3_k3
  · exact check_h3_k4
  · exact check_h3_k5
  · exact check_h3_k6
  · exact check_h3_k7
  · exact check_h3_k8
  · exact check_h3_k9
  · exact check_h3_k10
  · exact check_h3_k11
  · exact check_h3_k12
  · exact check_h3_k13
  · exact check_h3_k14
  · exact check_h3_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check4 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_4 : checkLeaf 4=true := by decide +kernel
theorem check_h4_k0 : (List.range 14).all (fun c => checkFork 4 0 c)=true := by decide +kernel
theorem check_h4_k1 : (List.range 14).all (fun c => checkFork 4 1 c)=true := by decide +kernel
theorem check_h4_k2 : (List.range 14).all (fun c => checkFork 4 2 c)=true := by decide +kernel
theorem check_h4_k3 : (List.range 14).all (fun c => checkFork 4 3 c)=true := by decide +kernel
theorem check_h4_k4 : (List.range 14).all (fun c => checkFork 4 4 c)=true := by decide +kernel
theorem check_h4_k5 : (List.range 14).all (fun c => checkFork 4 5 c)=true := by decide +kernel
theorem check_h4_k6 : (List.range 14).all (fun c => checkFork 4 6 c)=true := by decide +kernel
theorem check_h4_k7 : (List.range 14).all (fun c => checkFork 4 7 c)=true := by decide +kernel
theorem check_h4_k8 : (List.range 14).all (fun c => checkFork 4 8 c)=true := by decide +kernel
theorem check_h4_k9 : (List.range 14).all (fun c => checkFork 4 9 c)=true := by decide +kernel
theorem check_h4_k10 : (List.range 14).all (fun c => checkFork 4 10 c)=true := by decide +kernel
theorem check_h4_k11 : (List.range 14).all (fun c => checkFork 4 11 c)=true := by decide +kernel
theorem check_h4_k12 : (List.range 14).all (fun c => checkFork 4 12 c)=true := by decide +kernel
theorem check_h4_k13 : (List.range 14).all (fun c => checkFork 4 13 c)=true := by decide +kernel
theorem check_h4_k14 : (List.range 14).all (fun c => checkFork 4 14 c)=true := by decide +kernel
theorem check_h4_k15 : (List.range 14).all (fun c => checkFork 4 15 c)=true := by decide +kernel
theorem check_height_4 : checkHeight 4=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_4, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h4_k0
  · exact check_h4_k1
  · exact check_h4_k2
  · exact check_h4_k3
  · exact check_h4_k4
  · exact check_h4_k5
  · exact check_h4_k6
  · exact check_h4_k7
  · exact check_h4_k8
  · exact check_h4_k9
  · exact check_h4_k10
  · exact check_h4_k11
  · exact check_h4_k12
  · exact check_h4_k13
  · exact check_h4_k14
  · exact check_h4_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check5 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_5 : checkLeaf 5=true := by decide +kernel
theorem check_h5_k0 : (List.range 14).all (fun c => checkFork 5 0 c)=true := by decide +kernel
theorem check_h5_k1 : (List.range 14).all (fun c => checkFork 5 1 c)=true := by decide +kernel
theorem check_h5_k2 : (List.range 14).all (fun c => checkFork 5 2 c)=true := by decide +kernel
theorem check_h5_k3 : (List.range 14).all (fun c => checkFork 5 3 c)=true := by decide +kernel
theorem check_h5_k4 : (List.range 14).all (fun c => checkFork 5 4 c)=true := by decide +kernel
theorem check_h5_k5 : (List.range 14).all (fun c => checkFork 5 5 c)=true := by decide +kernel
theorem check_h5_k6 : (List.range 14).all (fun c => checkFork 5 6 c)=true := by decide +kernel
theorem check_h5_k7 : (List.range 14).all (fun c => checkFork 5 7 c)=true := by decide +kernel
theorem check_h5_k8 : (List.range 14).all (fun c => checkFork 5 8 c)=true := by decide +kernel
theorem check_h5_k9 : (List.range 14).all (fun c => checkFork 5 9 c)=true := by decide +kernel
theorem check_h5_k10 : (List.range 14).all (fun c => checkFork 5 10 c)=true := by decide +kernel
theorem check_h5_k11 : (List.range 14).all (fun c => checkFork 5 11 c)=true := by decide +kernel
theorem check_h5_k12 : (List.range 14).all (fun c => checkFork 5 12 c)=true := by decide +kernel
theorem check_h5_k13 : (List.range 14).all (fun c => checkFork 5 13 c)=true := by decide +kernel
theorem check_h5_k14 : (List.range 14).all (fun c => checkFork 5 14 c)=true := by decide +kernel
theorem check_h5_k15 : (List.range 14).all (fun c => checkFork 5 15 c)=true := by decide +kernel
theorem check_height_5 : checkHeight 5=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_5, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h5_k0
  · exact check_h5_k1
  · exact check_h5_k2
  · exact check_h5_k3
  · exact check_h5_k4
  · exact check_h5_k5
  · exact check_h5_k6
  · exact check_h5_k7
  · exact check_h5_k8
  · exact check_h5_k9
  · exact check_h5_k10
  · exact check_h5_k11
  · exact check_h5_k12
  · exact check_h5_k13
  · exact check_h5_k14
  · exact check_h5_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check6 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_6 : checkLeaf 6=true := by decide +kernel
theorem check_h6_k0 : (List.range 14).all (fun c => checkFork 6 0 c)=true := by decide +kernel
theorem check_h6_k1 : (List.range 14).all (fun c => checkFork 6 1 c)=true := by decide +kernel
theorem check_h6_k2 : (List.range 14).all (fun c => checkFork 6 2 c)=true := by decide +kernel
theorem check_h6_k3 : (List.range 14).all (fun c => checkFork 6 3 c)=true := by decide +kernel
theorem check_h6_k4 : (List.range 14).all (fun c => checkFork 6 4 c)=true := by decide +kernel
theorem check_h6_k5 : (List.range 14).all (fun c => checkFork 6 5 c)=true := by decide +kernel
theorem check_h6_k6 : (List.range 14).all (fun c => checkFork 6 6 c)=true := by decide +kernel
theorem check_h6_k7 : (List.range 14).all (fun c => checkFork 6 7 c)=true := by decide +kernel
theorem check_h6_k8 : (List.range 14).all (fun c => checkFork 6 8 c)=true := by decide +kernel
theorem check_h6_k9 : (List.range 14).all (fun c => checkFork 6 9 c)=true := by decide +kernel
theorem check_h6_k10 : (List.range 14).all (fun c => checkFork 6 10 c)=true := by decide +kernel
theorem check_h6_k11 : (List.range 14).all (fun c => checkFork 6 11 c)=true := by decide +kernel
theorem check_h6_k12 : (List.range 14).all (fun c => checkFork 6 12 c)=true := by decide +kernel
theorem check_h6_k13 : (List.range 14).all (fun c => checkFork 6 13 c)=true := by decide +kernel
theorem check_h6_k14 : (List.range 14).all (fun c => checkFork 6 14 c)=true := by decide +kernel
theorem check_h6_k15 : (List.range 14).all (fun c => checkFork 6 15 c)=true := by decide +kernel
theorem check_height_6 : checkHeight 6=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_6, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h6_k0
  · exact check_h6_k1
  · exact check_h6_k2
  · exact check_h6_k3
  · exact check_h6_k4
  · exact check_h6_k5
  · exact check_h6_k6
  · exact check_h6_k7
  · exact check_h6_k8
  · exact check_h6_k9
  · exact check_h6_k10
  · exact check_h6_k11
  · exact check_h6_k12
  · exact check_h6_k13
  · exact check_h6_k14
  · exact check_h6_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check7 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_7 : checkLeaf 7=true := by decide +kernel
theorem check_h7_k0 : (List.range 14).all (fun c => checkFork 7 0 c)=true := by decide +kernel
theorem check_h7_k1 : (List.range 14).all (fun c => checkFork 7 1 c)=true := by decide +kernel
theorem check_h7_k2 : (List.range 14).all (fun c => checkFork 7 2 c)=true := by decide +kernel
theorem check_h7_k3 : (List.range 14).all (fun c => checkFork 7 3 c)=true := by decide +kernel
theorem check_h7_k4 : (List.range 14).all (fun c => checkFork 7 4 c)=true := by decide +kernel
theorem check_h7_k5 : (List.range 14).all (fun c => checkFork 7 5 c)=true := by decide +kernel
theorem check_h7_k6 : (List.range 14).all (fun c => checkFork 7 6 c)=true := by decide +kernel
theorem check_h7_k7 : (List.range 14).all (fun c => checkFork 7 7 c)=true := by decide +kernel
theorem check_h7_k8 : (List.range 14).all (fun c => checkFork 7 8 c)=true := by decide +kernel
theorem check_h7_k9 : (List.range 14).all (fun c => checkFork 7 9 c)=true := by decide +kernel
theorem check_h7_k10 : (List.range 14).all (fun c => checkFork 7 10 c)=true := by decide +kernel
theorem check_h7_k11 : (List.range 14).all (fun c => checkFork 7 11 c)=true := by decide +kernel
theorem check_h7_k12 : (List.range 14).all (fun c => checkFork 7 12 c)=true := by decide +kernel
theorem check_h7_k13 : (List.range 14).all (fun c => checkFork 7 13 c)=true := by decide +kernel
theorem check_h7_k14 : (List.range 14).all (fun c => checkFork 7 14 c)=true := by decide +kernel
theorem check_h7_k15 : (List.range 14).all (fun c => checkFork 7 15 c)=true := by decide +kernel
theorem check_height_7 : checkHeight 7=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_7, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h7_k0
  · exact check_h7_k1
  · exact check_h7_k2
  · exact check_h7_k3
  · exact check_h7_k4
  · exact check_h7_k5
  · exact check_h7_k6
  · exact check_h7_k7
  · exact check_h7_k8
  · exact check_h7_k9
  · exact check_h7_k10
  · exact check_h7_k11
  · exact check_h7_k12
  · exact check_h7_k13
  · exact check_h7_k14
  · exact check_h7_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check8 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_8 : checkLeaf 8=true := by decide +kernel
theorem check_h8_k0 : (List.range 14).all (fun c => checkFork 8 0 c)=true := by decide +kernel
theorem check_h8_k1 : (List.range 14).all (fun c => checkFork 8 1 c)=true := by decide +kernel
theorem check_h8_k2 : (List.range 14).all (fun c => checkFork 8 2 c)=true := by decide +kernel
theorem check_h8_k3 : (List.range 14).all (fun c => checkFork 8 3 c)=true := by decide +kernel
theorem check_h8_k4 : (List.range 14).all (fun c => checkFork 8 4 c)=true := by decide +kernel
theorem check_h8_k5 : (List.range 14).all (fun c => checkFork 8 5 c)=true := by decide +kernel
theorem check_h8_k6 : (List.range 14).all (fun c => checkFork 8 6 c)=true := by decide +kernel
theorem check_h8_k7 : (List.range 14).all (fun c => checkFork 8 7 c)=true := by decide +kernel
theorem check_h8_k8 : (List.range 14).all (fun c => checkFork 8 8 c)=true := by decide +kernel
theorem check_h8_k9 : (List.range 14).all (fun c => checkFork 8 9 c)=true := by decide +kernel
theorem check_h8_k10 : (List.range 14).all (fun c => checkFork 8 10 c)=true := by decide +kernel
theorem check_h8_k11 : (List.range 14).all (fun c => checkFork 8 11 c)=true := by decide +kernel
theorem check_h8_k12 : (List.range 14).all (fun c => checkFork 8 12 c)=true := by decide +kernel
theorem check_h8_k13 : (List.range 14).all (fun c => checkFork 8 13 c)=true := by decide +kernel
theorem check_h8_k14 : (List.range 14).all (fun c => checkFork 8 14 c)=true := by decide +kernel
theorem check_h8_k15 : (List.range 14).all (fun c => checkFork 8 15 c)=true := by decide +kernel
theorem check_height_8 : checkHeight 8=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_8, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h8_k0
  · exact check_h8_k1
  · exact check_h8_k2
  · exact check_h8_k3
  · exact check_h8_k4
  · exact check_h8_k5
  · exact check_h8_k6
  · exact check_h8_k7
  · exact check_h8_k8
  · exact check_h8_k9
  · exact check_h8_k10
  · exact check_h8_k11
  · exact check_h8_k12
  · exact check_h8_k13
  · exact check_h8_k14
  · exact check_h8_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check9 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_9 : checkLeaf 9=true := by decide +kernel
theorem check_h9_k0 : (List.range 14).all (fun c => checkFork 9 0 c)=true := by decide +kernel
theorem check_h9_k1 : (List.range 14).all (fun c => checkFork 9 1 c)=true := by decide +kernel
theorem check_h9_k2 : (List.range 14).all (fun c => checkFork 9 2 c)=true := by decide +kernel
theorem check_h9_k3 : (List.range 14).all (fun c => checkFork 9 3 c)=true := by decide +kernel
theorem check_h9_k4 : (List.range 14).all (fun c => checkFork 9 4 c)=true := by decide +kernel
theorem check_h9_k5 : (List.range 14).all (fun c => checkFork 9 5 c)=true := by decide +kernel
theorem check_h9_k6 : (List.range 14).all (fun c => checkFork 9 6 c)=true := by decide +kernel
theorem check_h9_k7 : (List.range 14).all (fun c => checkFork 9 7 c)=true := by decide +kernel
theorem check_h9_k8 : (List.range 14).all (fun c => checkFork 9 8 c)=true := by decide +kernel
theorem check_h9_k9 : (List.range 14).all (fun c => checkFork 9 9 c)=true := by decide +kernel
theorem check_h9_k10 : (List.range 14).all (fun c => checkFork 9 10 c)=true := by decide +kernel
theorem check_h9_k11 : (List.range 14).all (fun c => checkFork 9 11 c)=true := by decide +kernel
theorem check_h9_k12 : (List.range 14).all (fun c => checkFork 9 12 c)=true := by decide +kernel
theorem check_h9_k13 : (List.range 14).all (fun c => checkFork 9 13 c)=true := by decide +kernel
theorem check_h9_k14 : (List.range 14).all (fun c => checkFork 9 14 c)=true := by decide +kernel
theorem check_h9_k15 : (List.range 14).all (fun c => checkFork 9 15 c)=true := by decide +kernel
theorem check_height_9 : checkHeight 9=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_9, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h9_k0
  · exact check_h9_k1
  · exact check_h9_k2
  · exact check_h9_k3
  · exact check_h9_k4
  · exact check_h9_k5
  · exact check_h9_k6
  · exact check_h9_k7
  · exact check_h9_k8
  · exact check_h9_k9
  · exact check_h9_k10
  · exact check_h9_k11
  · exact check_h9_k12
  · exact check_h9_k13
  · exact check_h9_k14
  · exact check_h9_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check10 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_10 : checkLeaf 10=true := by decide +kernel
theorem check_h10_k0 : (List.range 14).all (fun c => checkFork 10 0 c)=true := by decide +kernel
theorem check_h10_k1 : (List.range 14).all (fun c => checkFork 10 1 c)=true := by decide +kernel
theorem check_h10_k2 : (List.range 14).all (fun c => checkFork 10 2 c)=true := by decide +kernel
theorem check_h10_k3 : (List.range 14).all (fun c => checkFork 10 3 c)=true := by decide +kernel
theorem check_h10_k4 : (List.range 14).all (fun c => checkFork 10 4 c)=true := by decide +kernel
theorem check_h10_k5 : (List.range 14).all (fun c => checkFork 10 5 c)=true := by decide +kernel
theorem check_h10_k6 : (List.range 14).all (fun c => checkFork 10 6 c)=true := by decide +kernel
theorem check_h10_k7 : (List.range 14).all (fun c => checkFork 10 7 c)=true := by decide +kernel
theorem check_h10_k8 : (List.range 14).all (fun c => checkFork 10 8 c)=true := by decide +kernel
theorem check_h10_k9 : (List.range 14).all (fun c => checkFork 10 9 c)=true := by decide +kernel
theorem check_h10_k10 : (List.range 14).all (fun c => checkFork 10 10 c)=true := by decide +kernel
theorem check_h10_k11 : (List.range 14).all (fun c => checkFork 10 11 c)=true := by decide +kernel
theorem check_h10_k12 : (List.range 14).all (fun c => checkFork 10 12 c)=true := by decide +kernel
theorem check_h10_k13 : (List.range 14).all (fun c => checkFork 10 13 c)=true := by decide +kernel
theorem check_h10_k14 : (List.range 14).all (fun c => checkFork 10 14 c)=true := by decide +kernel
theorem check_h10_k15 : (List.range 14).all (fun c => checkFork 10 15 c)=true := by decide +kernel
theorem check_height_10 : checkHeight 10=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_10, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h10_k0
  · exact check_h10_k1
  · exact check_h10_k2
  · exact check_h10_k3
  · exact check_h10_k4
  · exact check_h10_k5
  · exact check_h10_k6
  · exact check_h10_k7
  · exact check_h10_k8
  · exact check_h10_k9
  · exact check_h10_k10
  · exact check_h10_k11
  · exact check_h10_k12
  · exact check_h10_k13
  · exact check_h10_k14
  · exact check_h10_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check11 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_11 : checkLeaf 11=true := by decide +kernel
theorem check_h11_k0 : (List.range 14).all (fun c => checkFork 11 0 c)=true := by decide +kernel
theorem check_h11_k1 : (List.range 14).all (fun c => checkFork 11 1 c)=true := by decide +kernel
theorem check_h11_k2 : (List.range 14).all (fun c => checkFork 11 2 c)=true := by decide +kernel
theorem check_h11_k3 : (List.range 14).all (fun c => checkFork 11 3 c)=true := by decide +kernel
theorem check_h11_k4 : (List.range 14).all (fun c => checkFork 11 4 c)=true := by decide +kernel
theorem check_h11_k5 : (List.range 14).all (fun c => checkFork 11 5 c)=true := by decide +kernel
theorem check_h11_k6 : (List.range 14).all (fun c => checkFork 11 6 c)=true := by decide +kernel
theorem check_h11_k7 : (List.range 14).all (fun c => checkFork 11 7 c)=true := by decide +kernel
theorem check_h11_k8 : (List.range 14).all (fun c => checkFork 11 8 c)=true := by decide +kernel
theorem check_h11_k9 : (List.range 14).all (fun c => checkFork 11 9 c)=true := by decide +kernel
theorem check_h11_k10 : (List.range 14).all (fun c => checkFork 11 10 c)=true := by decide +kernel
theorem check_h11_k11 : (List.range 14).all (fun c => checkFork 11 11 c)=true := by decide +kernel
theorem check_h11_k12 : (List.range 14).all (fun c => checkFork 11 12 c)=true := by decide +kernel
theorem check_h11_k13 : (List.range 14).all (fun c => checkFork 11 13 c)=true := by decide +kernel
theorem check_h11_k14 : (List.range 14).all (fun c => checkFork 11 14 c)=true := by decide +kernel
theorem check_h11_k15 : (List.range 14).all (fun c => checkFork 11 15 c)=true := by decide +kernel
theorem check_height_11 : checkHeight 11=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_11, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h11_k0
  · exact check_h11_k1
  · exact check_h11_k2
  · exact check_h11_k3
  · exact check_h11_k4
  · exact check_h11_k5
  · exact check_h11_k6
  · exact check_h11_k7
  · exact check_h11_k8
  · exact check_h11_k9
  · exact check_h11_k10
  · exact check_h11_k11
  · exact check_h11_k12
  · exact check_h11_k13
  · exact check_h11_k14
  · exact check_h11_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check12 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_12 : checkLeaf 12=true := by decide +kernel
theorem check_h12_k0 : (List.range 14).all (fun c => checkFork 12 0 c)=true := by decide +kernel
theorem check_h12_k1 : (List.range 14).all (fun c => checkFork 12 1 c)=true := by decide +kernel
theorem check_h12_k2 : (List.range 14).all (fun c => checkFork 12 2 c)=true := by decide +kernel
theorem check_h12_k3 : (List.range 14).all (fun c => checkFork 12 3 c)=true := by decide +kernel
theorem check_h12_k4 : (List.range 14).all (fun c => checkFork 12 4 c)=true := by decide +kernel
theorem check_h12_k5 : (List.range 14).all (fun c => checkFork 12 5 c)=true := by decide +kernel
theorem check_h12_k6 : (List.range 14).all (fun c => checkFork 12 6 c)=true := by decide +kernel
theorem check_h12_k7 : (List.range 14).all (fun c => checkFork 12 7 c)=true := by decide +kernel
theorem check_h12_k8 : (List.range 14).all (fun c => checkFork 12 8 c)=true := by decide +kernel
theorem check_h12_k9 : (List.range 14).all (fun c => checkFork 12 9 c)=true := by decide +kernel
theorem check_h12_k10 : (List.range 14).all (fun c => checkFork 12 10 c)=true := by decide +kernel
theorem check_h12_k11 : (List.range 14).all (fun c => checkFork 12 11 c)=true := by decide +kernel
theorem check_h12_k12 : (List.range 14).all (fun c => checkFork 12 12 c)=true := by decide +kernel
theorem check_h12_k13 : (List.range 14).all (fun c => checkFork 12 13 c)=true := by decide +kernel
theorem check_h12_k14 : (List.range 14).all (fun c => checkFork 12 14 c)=true := by decide +kernel
theorem check_h12_k15 : (List.range 14).all (fun c => checkFork 12 15 c)=true := by decide +kernel
theorem check_height_12 : checkHeight 12=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_12, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h12_k0
  · exact check_h12_k1
  · exact check_h12_k2
  · exact check_h12_k3
  · exact check_h12_k4
  · exact check_h12_k5
  · exact check_h12_k6
  · exact check_h12_k7
  · exact check_h12_k8
  · exact check_h12_k9
  · exact check_h12_k10
  · exact check_h12_k11
  · exact check_h12_k12
  · exact check_h12_k13
  · exact check_h12_k14
  · exact check_h12_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Check13 -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem check_leaf_13 : checkLeaf 13=true := by decide +kernel
theorem check_h13_k0 : (List.range 14).all (fun c => checkFork 13 0 c)=true := by decide +kernel
theorem check_h13_k1 : (List.range 14).all (fun c => checkFork 13 1 c)=true := by decide +kernel
theorem check_h13_k2 : (List.range 14).all (fun c => checkFork 13 2 c)=true := by decide +kernel
theorem check_h13_k3 : (List.range 14).all (fun c => checkFork 13 3 c)=true := by decide +kernel
theorem check_h13_k4 : (List.range 14).all (fun c => checkFork 13 4 c)=true := by decide +kernel
theorem check_h13_k5 : (List.range 14).all (fun c => checkFork 13 5 c)=true := by decide +kernel
theorem check_h13_k6 : (List.range 14).all (fun c => checkFork 13 6 c)=true := by decide +kernel
theorem check_h13_k7 : (List.range 14).all (fun c => checkFork 13 7 c)=true := by decide +kernel
theorem check_h13_k8 : (List.range 14).all (fun c => checkFork 13 8 c)=true := by decide +kernel
theorem check_h13_k9 : (List.range 14).all (fun c => checkFork 13 9 c)=true := by decide +kernel
theorem check_h13_k10 : (List.range 14).all (fun c => checkFork 13 10 c)=true := by decide +kernel
theorem check_h13_k11 : (List.range 14).all (fun c => checkFork 13 11 c)=true := by decide +kernel
theorem check_h13_k12 : (List.range 14).all (fun c => checkFork 13 12 c)=true := by decide +kernel
theorem check_h13_k13 : (List.range 14).all (fun c => checkFork 13 13 c)=true := by decide +kernel
theorem check_h13_k14 : (List.range 14).all (fun c => checkFork 13 14 c)=true := by decide +kernel
theorem check_h13_k15 : (List.range 14).all (fun c => checkFork 13 15 c)=true := by decide +kernel
theorem check_height_13 : checkHeight 13=true := by
  simp only [checkHeight, Bool.and_eq_true]
  refine ⟨check_leaf_13, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk0 : k<16 := List.mem_range.mp hk
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega

  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_h13_k0
  · exact check_h13_k1
  · exact check_h13_k2
  · exact check_h13_k3
  · exact check_h13_k4
  · exact check_h13_k5
  · exact check_h13_k6
  · exact check_h13_k7
  · exact check_h13_k8
  · exact check_h13_k9
  · exact check_h13_k10
  · exact check_h13_k11
  · exact check_h13_k12
  · exact check_h13_k13
  · exact check_h13_k14
  · exact check_h13_k15

end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322RootCheck -/
namespace SiggolfReverse2322
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem root_check : rootCheck=true := by decide +kernel
end SiggolfReverse2322

/-! Numeric structural component: SiggolfReverse2322Certified -/
namespace SiggolfReverse2322
open SiggolfPrefixCertificate
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000

theorem checks_all (h : Nat) (hh : h≤13) : checkHeight h=true := by
  have hc : h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 ∨ h=8 ∨ h=9 ∨ h=10 ∨ h=11 ∨ h=12 ∨ h=13 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_height_0
  · exact check_height_1
  · exact check_height_2
  · exact check_height_3
  · exact check_height_4
  · exact check_height_5
  · exact check_height_6
  · exact check_height_7
  · exact check_height_8
  · exact check_height_9
  · exact check_height_10
  · exact check_height_11
  · exact check_height_12
  · exact check_height_13

theorem certificate : Certificate := certificate_of_checks checks_all

theorem root_bound {a p q fl fr cl cr : Nat} (ha : a<14) (hk : p+q=15)
    (left : Tree credit (14-a-1) p fl cl)
    (right : Tree credit (14-a-1) q fr cr) (hf : a+fl+fr≤117) :
    464+16*(a+fl+fr)-(oldCredit a+cl+cr)≤2322 :=
  root_bound_of_checks certificate root_check ha hk left right hf

end SiggolfReverse2322

/-!
# Iteration parameters

The numeric parameters for the proved bound on accepting verification runs and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Universal accepting-run bound after fifteen leaf-offset instruction eliminations,
three static root-header loads, one retained top-layer base, and the exact structural
PORS segment credit with conditional two-fold prefixes and exact root reserve. Query formatting is an injective global relabel. -/
def verifyCycleBound : Nat := 10203

/-- The witness charge `⌈13712 / 256⌉`: sparse PORS cells use consumed tweak slots,
with packed lower authentication paths and external buffer `0x1270 .. 0x4800`. -/
def witnessCharge : Nat := 54

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
