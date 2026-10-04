import SigGolfCandidate.SphincsSecurity.Scheme
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.HashOutputSplit
import SigGolfCandidate.T3.Rev
import Mathlib
import SigGolfCandidate.T3.FullCache.MacDefs

namespace SigGolfCandidate.T3
open OracleComp OracleSpec
open SphincsSecurity (bytesLE)
abbrev Digest := BitVec 128
abbrev Message := BitVec 256
abbrev HashOutput := BitVec 256
abbrev HashInput := List UInt8
abbrev HashSpec := HashInput →ₒ HashOutput
abbrev Layer := Fin 4
abbrev Region := Fin 131040 → UInt8
abbrev Coordinate := BitVec 128 ⊕ (Message ⊕ Region)
abbrev Spec := SphincsSecurity.OracleWorld + (Coordinate →ₒ HashOutput)
abbrev M := OracleComp Spec
def height (lay : Layer) : Nat := ![12, 7, 6, 6] lay
def chainCount (lay : Layer) : Nat := ![54, 43, 43, 43] lay
def dataCount (lay : Layer) : Nat := if lay = 0 then 54 else 42
def width (lay : Layer) (i : Nat) : Nat := if lay = 0 ∧ 51 ≤ i then 2 else 3
def maxDigit (lay : Layer) (i : Nat) : Nat :=
  if lay = 0 then (if i < 51 then 4 else 3) else 7
def target (lay : Layer) : Nat := ![126, 196, 196, 196] lay
def encodedBits (lay : Layer) : Nat := if lay = 0 then 125 else 126
def capacity (lay : Layer) : Nat := if lay = 0 then 213 else 301
def attemptLimit : Nat := 2 ^ 20
def counterLimit : Nat := 2 ^ 22
def coordinates : Nat := 7
def bucketBits : Nat := 4
def childHeight : Nat := 7
def openings : Nat := 21
def authCapacity : Nat := 115
def zero16 : HashInput := List.replicate 16 0
def packedNodeTag (tag : Nat) : Prop := tag % 256 = 3 ∨ tag % 256 = 9 ∨ tag % 256 = 10
instance (tag : Nat) : Decidable (packedNodeTag tag) := inferInstanceAs
  (Decidable (tag % 256 = 3 ∨ tag % 256 = 9 ∨ tag % 256 = 10))
def revNodeTag (tag : Nat) : Prop := tag % 256 = 9 ∨ tag % 256 = 10
instance (tag : Nat) : Decidable (revNodeTag tag) := inferInstanceAs
  (Decidable (tag % 256 = 9 ∨ tag % 256 = 10))
def nodeWord (tag position index : Nat) : Nat :=
  if revNodeTag tag then
    Rev.revBits 64 ((if tag % 256 = 9 then index % 2^32 ^^^ 2048 else index % 2^32) + position % 2^32 * 2^32)
  else index % 2^32 + position % 2^32 * 2^32
theorem nodeWord_lt (tag position index : Nat) : nodeWord tag position index < 2^64 := by
  unfold nodeWord
  have hp := Nat.mod_lt position (show 0 < 2^32 by decide)
  have hi := Nat.mod_lt index (show 0 < 2^32 by decide)
  split_ifs
  · exact Rev.revBits_lt 64 _
  · exact Rev.revBits_lt 64 _
  · norm_num only at hp hi ⊢; omega
theorem nodeWord_normal (tag position index : Nat) :
    nodeWord (tag % 256) (position % 2^32) (index % 2^32) = nodeWord tag position index := by
  simp only [nodeWord, revNodeTag, Nat.mod_mod]
  rfl
theorem nodeWord_normal' (tag position index : Nat) :
    nodeWord (tag % 256) (position % 4294967296) (index % 4294967296) = nodeWord tag position index :=
  nodeWord_normal tag position index
theorem nodeWord_inj {tag position index position' index' : Nat} (hp : position < 2^32) (hi : index < 2^32)
    (hp' : position' < 2^32) (hi' : index' < 2^32)
    (h : nodeWord tag position index = nodeWord tag position' index') : position = position' ∧ index = index' := by
  unfold nodeWord at h
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hp', Nat.mod_eq_of_lt hi'] at h
  have hx : ∀ v, v < 2^32 → v ^^^ 2048 < 2^32 := fun v hv => Nat.xor_lt_two_pow hv (by decide)
  have hxi := hx index hi
  have hxi' := hx index' hi'
  split_ifs at h with hr h9
  · have h2 := Rev.revBits_inj (by omega) (by omega) h
    have hpp : position = position' := by omega
    refine ⟨hpp, ?_⟩
    have hxx : index ^^^ 2048 = index' ^^^ 2048 := by omega
    have := congrArg (· ^^^ 2048) hxx
    simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
  · have h2 := Rev.revBits_inj (by omega) (by omega) h
    omega
  · omega
def header (tag lay tree position index : Nat) : BitVec 128 :=
  BitVec.ofNat 128 (1 + tag % 256 * 2^8 + lay % 256 * 2^16 +
    (tree / 2^32 % 256) * 2^24 +
    if packedNodeTag tag then tree % 2^32 * 2^32 + nodeWord tag position index * 2^64
    else position % 2^32 * 2^32 + tree % 2^32 * 2^64 + index % 2^32 * 2^96)
def pad64 (input : HashInput) : HashInput :=
  input ++ List.replicate ((64 - input.length % 64) % 64) 0
def privateInput (secret : BitVec 256) (coordinate : Coordinate) : HashInput :=
  let payload := match coordinate with
    | .inl tweak => (tweak, [])
    | .inr (.inl message) => (header 7 0 0 0 0, bytesLE 32 message)
    | .inr (.inr region) => (header 14 0 0 0 0, List.ofFn region)
  pad64 (bytesLE 16 (secret.extractLsb' 0 128) ++ bytesLE 16 payload.1 ++
    bytesLE 16 (secret.extractLsb' 128 128) ++ zero16 ++ payload.2)
def publicHash (input : HashInput) : M HashOutput := Spec.query (.inl (.inr (pad64 input)))
def privateHash (coordinate : Coordinate) : M HashOutput := Spec.query (.inr coordinate)
def shortHash (input : HashInput) : M Digest := do
  pure ((← publicHash input).extractLsb' 0 128)
def privatePair (tag lay tree position index : Nat) : M (Digest × Digest) := do
  let output ← privateHash (.inl (header tag lay tree position index))
  pure (output.extractLsb' 0 128, output.extractLsb' 128 128)
def privateMacKey : M SiggolfT3Mac4.MacKey := do
  let k0 ← privateHash (.inl (header 14 0 0 0 0))
  let k1 ← privateHash (.inl (header 14 0 0 0 1))
  pure (fun i => if i = 0 then k0 else k1)
def privateMac (region : Region) : M HashOutput := do
  let key ← privateMacKey
  pure (SiggolfT3Mac4.encodeTag (SiggolfT3Mac4.macTag key (List.ofFn region)))
def privateNonce (message : Message) : M Digest := do
  pure ((← privateHash (.inr (.inl message))).extractLsb' 0 128)
def pairedMask (level pair : Nat) : M (Digest × Digest) := privatePair 13 0 0 level pair
def mask (level index : Nat) : M Digest := do
  let pair ← pairedMask level (index/2)
  pure (if index%2=0 then pair.1 else pair.2)
def realHandler (secret : BitVec 256) : QueryImpl Spec (OracleComp SphincsSecurity.OracleWorld)
  | .inl input => liftM (SphincsSecurity.OracleWorld.query input)
  | .inr coordinate => liftM (SphincsSecurity.OracleWorld.query (.inr (privateInput secret coordinate)))
def realize {α : Type} (secret : BitVec 256) (program : M α) :
    OracleComp SphincsSecurity.OracleWorld α := simulateQ (realHandler secret) program
def chainHeaderLow (lay : Layer) (tree leaf i step : Nat) : BitVec 64 :=
  let tr := tree % 2^31
  let lf := leaf % 4096
  let routed := (tr * 2 ^ height lay + lf) % 2^32
  let extra := tr / 2^(32-height lay) + (lf / 2^height lay) * 2^(height lay-1)
  BitVec.ofNat 64 (128 + i % 64 + step % 8 * 2^8 + routed * 2^16 +
    lay.val * 2^48 + 193 * 2^56 +
    extra % 2 * 2^6 + extra / 2 % 32 * 2^11 + extra / 64 * 2^50)
def chainHeaderSpill (tree leaf i step : Nat) : Nat :=
  tree % 2^40 / 2^31 + (leaf % 2^32 / 4096) * 2^9 +
    (i % 2^24 / 64) * 2^29 + (step % 256 / 8) * 2^47
def chainHeaderFlaggedLow (lay : Layer) (tree leaf i step : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((chainHeaderLow lay tree leaf i step).toNat +
    (if chainHeaderSpill tree leaf i step = 0 then 0 else 1) * 2^55)
def chainHeader (lay : Layer) (tree leaf i step : Nat) : BitVec 128 :=
  BitVec.ofNat 64 (chainHeaderSpill tree leaf i step) ++ chainHeaderFlaggedLow lay tree leaf i step
def chainInput (lay : Layer) (tree leaf i step : Nat) (value : Digest) : HashInput :=
  zero16 ++ bytesLE 16 (chainHeader lay tree leaf i step) ++ zero16 ++ bytesLE 16 value
def chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => shortHash (chainInput lay tree leaf i step value)) value
def leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) : M Digest :=
  shortHash (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (header 2 lay.val tree 0 leaf) ++
    (ends.drop 1).flatMap (bytesLE 16))
def buildLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool := false) : M (Digest × List Digest) := do
  let state ← (List.range ((chainCount lay + 1) / 2)).foldlM
    (fun (state : List Digest × List Digest) pair => do
      let seeds ← privatePair 0 lay.val tree pair leaf
      (List.range 2).foldlM (fun (state : List Digest × List Digest) half => do
        let i := 2*pair+half
        if chainCount lay ≤ i then return state
        let seed := if half = 0 then seeds.1 else seeds.2
        let digit := digits.getD i 0
        let value ← chain lay tree leaf i 0 digit seed
        if signatureOnly then return (state.1, state.2 ++ [value])
        let last ← chain lay tree leaf i digit (maxDigit lay i - digit) value
        pure (state.1 ++ [last], state.2 ++ [value])) state) ([], [])
  if signatureOnly then return (0, state.2)
  let root ← leafHash lay tree leaf state.1
  pure (root, state.2)
def nodeHash (tag lay tree heap : Nat) (left right : Digest) : M Digest :=
  shortHash (bytesLE 16 left ++ bytesLE 16 (header tag lay tree 0 heap) ++ zero16 ++ bytesLE 16 right)
def buildLevel (tag lay tree h level : Nat) (nodes : List Digest) : M (List Digest) :=
  (List.range (nodes.length / 2)).mapM fun i =>
    nodeHash tag lay tree (2 ^ (h-level) + i) (nodes.getD (2*i) 0) (nodes.getD (2*i+1) 0)
def buildLevels (tag lay tree h : Nat) (leaves : List Digest) : M (List (List Digest)) :=
  (List.range' 1 h).foldlM (fun levels level => do
    let nodes ← buildLevel tag lay tree h level (levels.getD (level-1) [])
    pure (levels ++ [nodes])) [leaves]
def buildTree (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List Digest) leaf => do
      let (root, values) ← buildLeaf lay tree leaf (if leaf = selected then digits else [])
      pure (state.1 ++ [root], if leaf = selected then values else state.2)) ([], [])
  let levels ← buildLevels 3 lay.val tree (height lay) state.1
  pure (levels, state.2)
structure Cache where
  tag : HashOutput
  region : Region
def cacheBytes (cache : Cache) : HashInput := bytesLE 32 cache.tag ++ List.ofFn cache.region
def maskedLevel (nodes : List Digest) (level : Nat) : M (List Digest) := do
  let pairs ← (List.range (2^(11-level))).mapM fun pair => do
    let masks ← pairedMask level pair
    pure [nodes.getD (2*pair) 0 ^^^ masks.1, nodes.getD (2*pair+1) 0 ^^^ masks.2]
  pure pairs.flatten
def keygenPayload : M (Digest × Region) := do
  let (levels, _) ← buildTree 0 0 0 []
  let masked ← (List.range' 0 12).mapM fun level => maskedLevel (levels.getD level []) level
  let raw := (masked.flatten.flatMap (bytesLE 16)).toArray
  pure ((levels.getD 12 []).getD 0 0, fun i => raw.getD i.val 0)
def keygen : M (Digest × Cache) := do
  let (publicKey, region) ← keygenPayload
  let tag ← privateMac region
  pure (publicKey, ⟨tag, region⟩)
def coreDigit (lay : Layer) (value : Digest) (i : Nat) : Nat :=
  if lay = 0 then
    if i < 51 then (value.toNat / 2^(7*(i/3)) % 128) / 5^(i%3) % 5
    else value.toNat / 2^(119+2*(i-51)) % 4
  else value.toNat / 2^(3*i) % 8
def topRanksValid (value : Digest) : Bool :=
  (List.range 17).all fun j => decide (value.toNat / 2^(7*j) % 128 < 125)
def dataDigits (lay : Layer) (value : Digest) : List Nat :=
  (List.range (dataCount lay)).map (coreDigit lay value)
def decode (lay : Layer) (value : Digest) : Option (List Nat) :=
  if value.toNat ≥ 2 ^ encodedBits lay then none else
  let digits := dataDigits lay value
  let total := digits.sum
  if lay = 0 then
    if topRanksValid value && decide (total = target lay) then some digits else none
  else if total ≤ target lay ∧ target lay - total < 8 then
    some (digits ++ [target lay - total])
  else none
def encodingInput (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : BitVec 32) : HashInput :=
  bytesLE 16 message ++ bytesLE 16 (header 4 lay.val tree 0 leaf) ++ bytesLE 4 counter
def counterSearch (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : Nat) :
    Nat → M (Option (BitVec 32 × List Nat))
  | 0 => pure none
  | fuel+1 => do
      let answer ← shortHash (encodingInput lay tree leaf message (BitVec.ofNat 32 counter))
      match decode lay answer with
      | none => counterSearch lay tree leaf message (counter+1) fuel
      | some digits => pure (some (BitVec.ofNat 32 counter, digits))
structure Selection where
  bucket : Nat
  leaves : List Nat
  deriving DecidableEq, Repr
def selections (output : HashOutput) : List Selection :=
  (List.range 7).map fun c =>
    let number := output.toNat / 2^(31+25*c)
    ⟨number % 16, ((List.range 3).map fun j => number / 2^(4+7*j) % 128).mergeSort (· ≤ ·)⟩
def authCount (leaves : List Nat) : Nat :=
  7 + ((leaves.zip (leaves.drop 1)).map fun p => (p.1 ^^^ p.2).log2 + 1).sum - 4
def admissible (chosen : List Selection) : Bool :=
  chosen.all (fun s => decide (s.leaves.Nodup)) &&
    decide (28 + (chosen.map fun s => authCount s.leaves).sum ≤ 115)
def digestGate (output : HashOutput) : Bool := decide (output.toNat / 2^206 % 8 = 0)
def digestAdmissible (output : HashOutput) : Bool :=
  admissible (selections output) && digestGate output
def digestInput (rho : Digest) (message : Message) (counter : BitVec 32) : HashInput :=
  bytesLE 16 rho ++ bytesLE 16 (header 12 0 0 0 counter.toNat) ++ bytesLE 32 message
def digest (rho : Digest) (message : Message) (counter : BitVec 32) : M HashOutput :=
  publicHash (digestInput rho message counter)
def digestSearch (rho : Digest) (message : Message) (counter : Nat) :
    Nat → M (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel+1 => do
      let output ← digest rho message (BitVec.ofNat 32 counter)
      if digestAdmissible output then return some (BitVec.ofNat 32 counter, output)
      digestSearch rho message (counter+1) fuel
def ftsLeaf (index coord leaf : Nat) (secret : Digest) : M Digest :=
  shortHash (zero16 ++ bytesLE 16 (header 9 coord index 0 leaf) ++ bytesLE 16 secret ++ zero16)
def buildFts (index coord : Nat) : M (List (List Digest) × List Digest) := do
  let state ← (List.range 1024).foldlM
    (fun (state : List Digest × List Digest) pair => do
      let (left, right) ← privatePair 8 coord index 0 pair
      let leftLeaf ← ftsLeaf index coord (2*pair) left
      let rightLeaf ← ftsLeaf index coord (2*pair+1) right
      pure (state.1 ++ [leftLeaf,rightLeaf],state.2 ++ [left,right])) ([], [])
  let levels ← buildLevels 10 coord index 11 state.1
  pure (levels,state.2)
def hasLeaf (leaves : List Nat) (level index : Nat) : Bool :=
  leaves.any fun leaf => decide (index * 2 ^ level ≤ leaf ∧ leaf < (index+1) * 2 ^ level)
def frontier (leaves : List Nat) : Nat → Nat → List (Nat × Nat)
  | 0, index => if hasLeaf leaves 0 index then [] else [(0,index)]
  | level+1, index =>
      if hasLeaf leaves (level+1) index then
        frontier leaves level (2*index) ++ frontier leaves level (2*index+1)
      else [(level+1,index)]
def forestPk (index : Nat) (roots : List Digest) : M Digest :=
  shortHash (bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++
    (roots.drop 1).flatMap (bytesLE 16))
def route (index : Nat) (lay : Layer) : Nat × Nat :=
  let below := (![19,12,6,0] : Layer → Nat) lay
  (index / 2 ^ below % 2 ^ height lay, index / 2 ^ (below + height lay))
def readLE (bytes : HashInput) : Nat := bytes.foldr (fun b n => b.toNat + 256*n) 0
def readDigest (bytes : HashInput) : Digest := BitVec.ofNat 128 (readLE bytes)
def topPath (cache : Cache) (leaf : Nat) : M (List Digest) :=
  (List.range 12).mapM fun level => do
    let sibling := leaf / 2 ^ level ^^^ 1
    let offset := 16*(8192 - 2^(13-level) + sibling)
    let value := readDigest (List.ofFn fun i : Fin 16 =>
      cache.region ⟨(offset+i.val)%131040, Nat.mod_lt _ (by decide)⟩)
    let m ← mask level sibling
    pure (value ^^^ m)
def signTop (cache : Cache) (leaf : Nat) (digits : List Nat) : M (List Digest × List Digest) := do
  let (_,values) ← buildLeaf 0 0 leaf digits true
  let path ← topPath cache leaf
  pure (values,path)
abbrev Pieces := List Digest × List Digest
def signLayers (cache : Cache) (index : Nat) : Nat → Digest → M (Option (List Pieces))
  | 0, _ => pure (some [])
  | n+1, message => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf,tree) := route index lay
      let some (_,digits) ← counterSearch lay tree leaf message 0 counterLimit | pure none
      if n=0 then
        let part ← signTop cache leaf digits
        pure (some [part])
      else
        let (levels,values) ← buildTree lay tree leaf digits
        let path := (List.range (height lay)).map fun j => (levels.getD j []).getD (leaf/2^j ^^^ 1) 0
        let some previous ← signLayers cache index n ((levels.getD (height lay) []).getD 0 0) | pure none
        pure (some (previous ++ [(values,path)]))
structure LayerSignature (lay : Layer) where
  values : Fin (chainCount lay) → Digest
  path : Fin (height lay) → Digest
structure Signature where
  rho : Digest
  secrets : Fin 21 → Digest
  proof : Fin 115 → Digest
  layers : (lay : Layer) → LayerSignature lay
structure Witness where
  signature : Signature
  digestCounter : BitVec 32
  counters : Layer → BitVec 32
def piecesSignature (lay : Layer) (pieces : Pieces) : LayerSignature lay :=
  ⟨fun i => pieces.1.getD i.val 0,fun i => pieces.2.getD i.val 0⟩
def signPayload (cache : Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (_,output) ← digestSearch rho message 0 attemptLimit | pure none
  let index := output.toNat % 2^31
  let chosen := selections output
  let state ← (List.range 7).foldlM
    (fun (state : List Digest × List Digest × List Digest) coord => do
      let sel := chosen.getD coord ⟨0,[]⟩
      let (levels,secrets) ← buildFts index coord
      let selected := sel.leaves.map (fun s => sel.bucket*128+s)
      let opened := selected.map (fun s => secrets.getD s 0)
      let inner := (frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
      let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
      pure (state.1 ++ opened,state.2.1 ++ inner ++ outer,
        state.2.2 ++ [(levels.getD 11 []).getD 0 0])) ([],[],[])
  let root ← forestPk index state.2.2
  let some layers ← signLayers cache index 4 root | pure none
  pure (some ⟨rho,fun i => state.1.getD i.val 0,fun i => state.2.1.getD i.val 0,
    fun lay => piecesSignature lay (layers.getD lay.val ([],[]))⟩)
def sign (cache : Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayload cache message
def serializeLayer {lay : Layer} (sig : LayerSignature lay) : HashInput :=
  (List.ofFn sig.values).flatMap (bytesLE 16) ++ (List.ofFn sig.path).flatMap (bytesLE 16)
def serialize (sig : Signature) : HashInput :=
  bytesLE 16 sig.rho ++ (List.ofFn sig.secrets).flatMap (bytesLE 16) ++
    (List.ofFn sig.proof).flatMap (bytesLE 16) ++
    (List.ofFn fun lay => serializeLayer (sig.layers lay)).flatten
def recoverChild (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) : Nat → Nat → Nat → M (Option (Digest × Nat))
  | level,node,used =>
      if !hasLeaf leaves level node then
        if h : used < 115 then pure (some (proof ⟨used,h⟩,used+1)) else pure none
      else match level with
      | 0 => do
          let value ← ftsLeaf index coord node (values.getD (leaves.idxOf node) 0)
          pure (some (value,used))
      | level+1 => do
          let some (left,next) ← recoverChild index coord leaves values proof level (2*node) used | pure none
          let some (right,next) ← recoverChild index coord leaves values proof level (2*node+1) next | pure none
          let value ← nodeHash 10 coord index (2^(11-(level+1))+node) left right
          pure (some (value,next))
def recoverFts (sig : Signature) (index : Nat) (chosen : List Selection) : M (Option Digest) := do
  let state ← (List.range 7).foldlM
    (fun (state : Option (List Digest × Nat)) coord => do
      let some (roots,used) := state | pure none
      let sel := chosen.getD coord ⟨0,[]⟩
      let selected := sel.leaves.map (fun s => sel.bucket*128+s)
      let values := (List.range 3).map (fun j => sig.secrets ⟨(coord*3+j)%21,Nat.mod_lt _ (by decide)⟩)
      let some (value,next) ← recoverChild index coord selected values sig.proof 7 sel.bucket used | pure none
      let result ← (List.range 4).foldlM
        (fun (state : Option (Digest × Nat)) j => do
          let some (value,used) := state | pure none
          if h : used < 115 then
            let other := sig.proof ⟨used,h⟩
            let pair := if sel.bucket/2^j%2=0 then (value,other) else (other,value)
            let parent ← nodeHash 10 coord index (2^(4-j-1)+sel.bucket/2^(j+1)) pair.1 pair.2
            pure (some (parent,used+1))
          else pure none) (some (value,next))
      let some (root,next) := result | pure none
      pure (some (roots ++ [root],next))) (some ([],0))
  let some (roots,used) := state | pure none
  if !(List.range (115-used)).all (fun j =>
      decide (sig.proof ⟨(used+j)%115,Nat.mod_lt _ (by decide)⟩ = 0)) then return none
  pure (some (← forestPk index roots))
def recoverLayer (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf,tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chain lay tree leaf i.val (digits.getD i.val 0)
      (maxDigit lay i.val-digits.getD i.val 0) ((sig.layers lay).values i)
  let value ← leafHash lay tree leaf ends
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := (sig.layers lay).path j
    let pair := if leaf/2^j.val%2=0 then (value,other) else (other,value)
    nodeHash 3 lay.val tree (2^(height lay-j.val-1)+leaf/2^(j.val+1)) pair.1 pair.2) value
def expandLayers (sig : Signature) (index : Nat) : Nat → Digest → M (Option (Digest × List (BitVec 32)))
  | 0,value => pure (some (value,[]))
  | n+1,value => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf,tree) := route index lay
      let some (counter,digits) ← counterSearch lay tree leaf value 0 counterLimit | pure none
      let root ← recoverLayer sig index lay digits
      let some (root,counters) ← expandLayers sig index n root | pure none
      pure (some (root,counters ++ [counter]))
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) := do
  let some (counter,output) ← digestSearch sig.rho message 0 attemptLimit | pure none
  let index := output.toNat%2^31
  let some root ← recoverFts sig index (selections output) | pure none
  let some (root,counters) ← expandLayers sig index 4 root | pure none
  if root ≠ pk then return none
  pure (some ⟨sig,counter,fun lay => counters.getD lay.val 0⟩)
def verifyLayers (w : Witness) (index : Nat) : Nat → Digest → M (Option Digest)
  | 0,root => pure (some root)
  | n+1,root => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ counterLimit then return none
      let (leaf,tree) := route index lay
      let answer ← shortHash (encodingInput lay tree leaf root counter)
      let some digits := decode lay answer | pure none
      let value ← recoverLayer w.signature index lay digits
      verifyLayers w index n value
def verify (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ attemptLimit then return false
  let output ← digest w.signature.rho message w.digestCounter
  let chosen := selections output
  if !digestAdmissible output then return false
  let index := output.toNat%2^31
  let some root ← recoverFts w.signature index chosen | pure false
  let some root ← verifyLayers w index 4 root | pure false
  pure (root==pk)
end SigGolfCandidate.T3
