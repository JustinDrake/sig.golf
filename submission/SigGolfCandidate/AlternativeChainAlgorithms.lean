import SigGolfCandidate.Budget.Numeric
import SigGolfCandidate.Equiv.Basic
import SigGolfCandidate.Legacy.Programs
import SigGolfCandidate.Sign.Words
import SigGolfCandidate.Verify.Swar
import SigGolfCandidate.Rv.Hash
import SigGolfCandidate.Rv.Steps
import VCVio.OracleComp.QueryTracking.WriterCost
import Mathlib.Tactic.IrreducibleDef
import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.Ref.Basic
import SigGolfCandidate.Ref.Scheme
import SigGolfCandidate.Ref.Count
import SigGolfCandidate.Ref.Lemmas

import SigGolfCandidate.Ref.AddressQueries
import SigGolfCandidate.Rv.Tactic
import SigGolfCandidate.Equiv.Tree
import SigGolfCandidate.SphincsSecurity.Completeness.Decay
import SigGolfCandidate.SphincsSecurity.Completeness.Code
import SigGolfCandidate.SphincsSecurity.Completeness.Uniform

/-!
Reference implementation under development: four-layer radix-four/FORS.

This file is not the production submission and does not assert a certificate.
It defines the proposed oracle algorithms before their RISC-V refinement. All
loops are explicitly finite. Its protocol byte is 2. An independently proved
address-header involution prepares its chain queries for an in-place verifier.
-/

set_option profiler true
set_option profiler.threshold 1000
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace SigGolfCandidate.Base4Candidate.Reference

open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal
open SigGolfCandidate.Ref (Val zeros byte le32 slice answerBytes)

def height (lay : Nat) : Nat := if lay = 0 then 12 else 7
def route (idx lay : Nat) : Nat × Nat :=
  let cut := if lay = 0 then 21 else 7 * (3 - lay)
  (idx / 2 ^ cut % 2 ^ height lay, idx / 2 ^ (cut + height lay))

def header (tag lay tree pos index : Nat) : List Byte :=
  [byte 2, byte tag, byte lay, byte (tree / 2 ^ 32)] ++
    le32 pos ++ le32 tree ++ le32 index

def input (tag lay tree pos index : Nat) (payload : List Byte) : List Byte :=
  header tag lay tree pos index ++ zeros 16 ++ payload

def hash (bs : List Byte) : OracleComp HashSpec (BitVec 256) :=
  HashSpec.query (Base4Candidate.AddressFormat.queryPerm (SigGolfCandidate.Ref.pad64 bs))

def h16 (bs : List Byte) : OracleComp HashSpec Val := do
  let out ← hash bs
  pure (answerBytes 16 out)

def pair (bs : List Byte) : OracleComp HashSpec (Val × Val) := do
  let out ← hash bs
  pure ((answerBytes 32 out).take 16, (answerBytes 32 out).drop 16)

def chainInput (lay tree leaf i step : Nat) (v : Val) : List Byte :=
  header 1 lay tree (256 * i + step - 1) leaf ++ zeros 32 ++ v

def chainInputP (lay tree leaf i step : Nat) (pad v : Val) : List Byte :=
  header 1 lay tree (256 * i + step - 1) leaf ++ pad ++ v

def walk (lay tree leaf i start count : Nat) (v : Val) : OracleComp HashSpec Val :=
  (List.range' start count).foldlM
    (fun v step => h16 (chainInput lay tree leaf i step v)) v

def walkP (lay tree leaf i start count : Nat) (pad v : Val) : OracleComp HashSpec Val :=
  (List.range' start count).foldlM
    (fun v step => h16 (chainInputP lay tree leaf i step pad v)) v

def chainWithCapture (lay tree leaf i digit : Nat) (v : Val) :
    OracleComp HashSpec (Val × Val) :=
  (List.range' 1 3).foldlM (fun (st : Val × Val) step => do
    let next ← h16 (chainInput lay tree leaf i step st.1)
    pure (next, if step = digit then next else st.2)) (v, v)

end SigGolfCandidate.Base4Candidate.Reference
