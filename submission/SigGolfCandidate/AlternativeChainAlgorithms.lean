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

theorem walkP_zero (lay tree leaf i start count : Nat) (v : Val) :
    walkP lay tree leaf i start count (zeros 32) v = walk lay tree leaf i start count v := rfl

theorem ranges_split (s a b : Nat) :
    List.range' s (a+b) = List.range' s a ++ List.range' (s+a) b := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
    simp only [Nat.succ_add, List.range'_succ, List.cons_append]
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1 a]

theorem walk_add (lay tree leaf i start a b : Nat) (v : Val) :
    walk lay tree leaf i start (a+b) v = (do
      let mid ← walk lay tree leaf i start a v
      walk lay tree leaf i (start+a) b mid) := by
  unfold walk
  rw [ranges_split, List.foldlM_append]

/-- A disclosed initialPart and the verifier's remaining steps compose exactly. -/
theorem walk_recover (lay tree leaf i digit : Nat) (hd : digit ≤ 3) (v : Val) :
    (do
      let mid ← walk lay tree leaf i 1 digit v
      walk lay tree leaf i (digit+1) (3-digit) mid) = walk lay tree leaf i 1 3 v := by
  simpa only [Nat.add_comm 1 digit, Nat.add_sub_of_le hd] using
    (walk_add lay tree leaf i 1 digit (3-digit) v).symm

def chainWithCapture (lay tree leaf i digit : Nat) (v : Val) :
    OracleComp HashSpec (Val × Val) :=
  (List.range' 1 3).foldlM (fun (st : Val × Val) step => do
    let next ← h16 (chainInput lay tree leaf i step st.1)
    pure (next, if step = digit then next else st.2)) (v, v)

/-- The captured value is precisely a initialPart, including the zero-step case. -/
theorem chainWithCapture_split (lay tree leaf i digit : Nat) (hd : digit ≤ 3) (v : Val) :
    chainWithCapture lay tree leaf i digit v = (do
      let initialPart ← walk lay tree leaf i 1 digit v
      let endpoint ← walk lay tree leaf i (digit+1) (3-digit) initialPart
      pure (endpoint, initialPart)) := by
  unfold chainWithCapture walk
  have hc := fun x l hx a c => SigGolfCandidate.Equiv.capFold_notin
    (fun step v => h16 (chainInput lay tree leaf i step v)) x l hx a c
  cases digit with
  | zero =>
    rw [hc 0 _ (by simp)]
    simp
  | succ k =>
    have hs : List.range' 1 3 =
        List.range' 1 k ++ (1+k) :: List.range' (1+k+1) (2-k) := by
      rw [← List.range'_succ, show 2-k+1 = 3-k by omega, List.range'_append_1]
      congr 1
      omega
    rw [hs, List.foldlM_append, hc (k+1) _ (by simp; omega)]
    simp only [map_bind, bind_map_left, List.foldlM_cons, bind_assoc, pure_bind]
    rw [show List.range' 1 (k+1) = List.range' 1 k ++ [1+k] by
      rw [List.range'_concat]; simp]
    simp only [List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_assoc, bind_pure]
    congr 1
    funext w
    congr 1
    funext z
    rw [if_pos (by omega), hc (k+1) _ (by simp),
      show k+1+1 = 1+k+1 by omega, show 3-(k+1) = 2-k by omega]
    simp only [map_eq_bind_pure_comp, Function.comp_def]

end SigGolfCandidate.Base4Candidate.Reference
