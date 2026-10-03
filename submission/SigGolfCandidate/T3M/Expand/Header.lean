import SigGolfCandidate.T3M.Witness.SideCode
namespace SigGolfCandidate.T3M.Expand
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The byte actually stored by the dense-header producer, including malformed generic counts. -/
def emitHeader (cnt : Nat) (merge : Bool) (par : Nat) : Nat :=
  ((segOffset cnt+par%segSideMod cnt) ||| (if merge then 128 else 0))%256

theorem emitHeader_lt (cnt par : Nat) (m : Bool) : emitHeader cnt m par <256 := Nat.mod_lt _ (by decide)

theorem emitHeader_fields : ∀ (cnt : Fin 11) (par : Fin 16) (m : Bool),
    emitHeader cnt.val m par.val = SideCode.sideHeader cnt.val (if m then 1 else 0) par.val := by decide +kernel

theorem emitHeader_canonical (cnt par : Nat) (m : Bool) (hc : cnt<11) (hp : par<16) :
    emitHeader cnt m par = SideCode.sideHeader cnt (if m then 1 else 0) par :=
  emitHeader_fields ⟨cnt,hc⟩ ⟨par,hp⟩ m

theorem emitHeader_mod (cnt par : Nat) (m : Bool) : emitHeader cnt m (par%16)=emitHeader cnt m par := by
  unfold emitHeader
  rw [Nat.mod_mod_of_dvd _ (SideCode.segSideMod_dvd_sixteen cnt)]

/-- Fixed-width operations of the two native packing paths. -/
def packLarge (cnt par : BitVec 64) : BitVec 64 := (cnt<<<4)-49+(par&&&15)
def packSmall (cnt par : BitVec 64) : BitVec 64 :=
  let mask := ((1 : BitVec 64) <<< cnt.toNat)-1
  (par&&&mask)+mask

theorem pack_header : ∀ (cnt par : Fin 16) (m : Bool),
    (((if cnt.val<4 then packSmall (BitVec.ofNat 64 cnt.val) (BitVec.ofNat 64 par.val)
      else packLarge (BitVec.ofNat 64 cnt.val) (BitVec.ofNat 64 par.val)) |||
      (if m then 128 else 0)).truncate 8).toNat = emitHeader cnt.val m par.val := by decide +kernel
end SigGolfCandidate.T3M.Expand
