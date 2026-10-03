import SigGolfCandidate.SphincsSecurity.Proof.RandomizedStatement

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
structure SecretKey where
  parameter : PublicParameter
  root : Digest
  otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest
  ftsSecret : Index → FtsTree → FtsLeaf → Digest
  top : Nat → Nat → Digest
namespace Concrete
noncomputable opaque randomnessSampleableType : SampleableType Randomness :=
  SampleableType.ofFintype Randomness
noncomputable local instance : SampleableType Randomness := randomnessSampleableType
noncomputable def sampleRandomness : ProbComp Randomness :=
  $ᵗ Randomness
attribute [irreducible] sampleRandomness
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]
noncomputable local instance : SampleableType PublicParameter :=
  SampleableType.ofFintype PublicParameter
noncomputable opaque otsSecretsSampleableType :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
noncomputable local instance :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  otsSecretsSampleableType
noncomputable opaque ftsSecretsSampleableType :
    SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
  SampleableType.ofFintype (Index → FtsTree → FtsLeaf → Digest)
noncomputable local instance : SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
  ftsSecretsSampleableType
def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (secret : ChainIndex → Digest) : m (ChainIndex → Digest) :=
  sequenceFin fun chainIdx =>
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx)
def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let values ← sequenceFin fun chainIdx =>
            chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val (secret chainIdx)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf secret message attempts (counter + 1)
def otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    m (Option (Counter × (ChainIndex → Digest))) :=
  otsSignFrom parameter lay tree leaf secret message encodingAttemptLimit 0
def treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← oneTimePublicKey parameter lay tree leaf (secret leaf)
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← treeNode parameter lay tree secret level (2 * nodeIdx)
      let right ← treeNode parameter lay tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)
def treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : m Digest :=
  treeNode parameter lay tree secret (layerHeight lay) 0
def treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) : m (Fin maxLayerHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < layerHeight lay then
      treeNode parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      pure 0
def ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := ftsLeafOfNat nodeIdx
      ftsLeafHash parameter index tree leaf.val (secret leaf)
  | level + 1, nodeIdx => do
      let left ← ftsNode parameter index tree secret level (2 * nodeIdx)
      let right ← ftsNode parameter index tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.ftsNode index tree (ftsHeapIndex (level + 1) nodeIdx))
        (nodePayload left right)
def ftsKey (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) : m Digest :=
  ftsNode parameter index porsTree (secret porsTree) ftsTreeHeight 0
def ftsOpen (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) : m FtsSignature := do
  let slots := sortedSlots leaves
  let plan := schedule (sortedLeaves leaves)
  let segments ← sequenceFin fun j : Fin ftsSegments => do
    let segment := plan.getD j.val default
    let nodes ← sequenceFin (n := segment.folds.val) fun i =>
      let position := segment.reads.getD i.val (0, 0)
      ftsNode parameter index porsTree (secret porsTree) position.1 position.2
    return segment.toSegment nodes
  return { perm := fun s => (slots.getD s.val ⟨0, by decide⟩).castSucc
           secrets := fun s => secret porsTree (leaves (slots.getD s.val ⟨0, by decide⟩))
           segments := segments }
noncomputable def sampleParameter : ProbComp PublicParameter :=
  pure 0
noncomputable def sampleOtsSecrets :
    ProbComp (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  $ᵗ (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
noncomputable def sampleFtsSecrets : ProbComp (Index → FtsTree → FtsLeaf → Digest) :=
  $ᵗ (Index → FtsTree → FtsLeaf → Digest)
def keygenRoot (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) : m Digest := do
  let (_, _, root) ← buildLayerTree parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  return root
def keygenTable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    m (Nat → Nat → Digest) := do
  let (_, table) ← buildLayerTable parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  return table
noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM sampleParameter
  let otsSecret ← liftM sampleOtsSecrets
  let ftsSecret ← liftM sampleFtsSecrets
  let top ← liftM
    (keygenTable parameter (otsSecret topLayer rootTree) : OracleComp HashSpec (Nat → Nat → Digest))
  let root := top (layerHeight topLayer) 0
  return (⟨root, parameter⟩, ⟨parameter, root, otsSecret, ftsSecret, top⟩)
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  if Admissible digest then
    return some (digestIndex digest, digestLeaves digest)
  else
    return none
noncomputable def signDigestLoop : Nat → SecretKey → Message →
    OracleComp OracleWorld (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _secretKey, _message => pure none
  | attempts + 1, secretKey, message => do
      let randomness ← liftM sampleRandomness
      let attempt ← liftM
        (signAttempt secretKey message randomness :
          OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))
      match attempt with
      | some (index, leaves) => pure (some (randomness, index, leaves))
      | none => signDigestLoop attempts secretKey message
def layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) : m Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    treeRoot secretKey.parameter below (treeIndexAt index below)
      (secretKey.otsSecret below (treeIndexAt index below))
  else
    ftsKey secretKey.parameter index (secretKey.ftsSecret index)
def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    m (Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  match ← otsSign secretKey.parameter lay tree leaf (secretKey.otsSecret lay tree leaf) message with
  | none => return none
  | some (counter, values) => do
      let path ← treePath secretKey.parameter lay tree (secretKey.otsSecret lay tree) leaf
      return some (counter, values, path)
def signAfterDigest (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) : OracleComp HashSpec (Option Signature) :=
  signFrom secretKey.parameter index (fun tree leaf => pure (secretKey.ftsSecret index tree leaf))
    (fun lay tree leaf chainIdx => pure (secretKey.otsSecret lay tree leaf chainIdx))
    (fun level nodeIdx => pure (secretKey.top level nodeIdx)) randomness leaves
noncomputable def sign (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature) := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => return none
  | some (randomness, index, leaves) =>
      liftM (signAfterDigest secretKey randomness index leaves : OracleComp HashSpec (Option Signature))
attribute [irreducible] treeNode ftsNode sampleParameter sampleOtsSecrets sampleFtsSecrets keygen sign
  keygenRoot keygenTable signAfterDigest
end Concrete
noncomputable def Concrete.scheme : Scheme SecretKey where
  keygen := Concrete.keygen
  sign := Concrete.sign
  verify := fun publicKey message signature =>
    liftM (Concrete.verify publicKey message signature : OracleComp HashSpec Bool)
abbrev IndependentSecurityStatement : Prop :=
  HasClassicalSecurityBits Concrete.scheme 127
end SphincsSecurity
