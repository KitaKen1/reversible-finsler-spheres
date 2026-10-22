module

public import Finsler.Loop.H1PuncturedPatchHomology

/-! Fixed-base alignment gives a genuine strong-H1 based-loop
homeomorphism between any two poles, including antipodal poles.
The rotation is constant on this domain, so no continuity of a
rotor across the antipodal locus is required. -/
@[expose] public section
namespace Finsler.H1BasedFiberTransport
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.H1LocalFiber (based)
open Finsler.CompactH1Alignment Finsler.H1FiberBase
open Finsler.H1OrthogonalLength Finsler.H1OrthogonalContinuity Finsler.NearbyRotor
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def forward {n : ℕ} (y z : Sphere n) (u : based y) : based z :=
  ⟨align u.val z, basepoint_align u.val z⟩

theorem reverse_forward {n : ℕ} (y z : Sphere n) (u : based y) :
    forward z y (forward y z u) = u := by
  apply Subtype.ext
  have hp : point u.val = y := Subtype.ext u.property
  change align (align u.val z) y = u.val
  simpa only [hp] using align_reverse u.val z

theorem continuous_forward {n : ℕ} (y z : Sphere n) : Continuous (forward y z) := by
  have he : (fun u : based y => align u.val z) =
      (fun u : based y => rotateLoop (rotor (y : Ambient n) (z : Ambient n)) u.val) := by
    funext u
    unfold align
    rw [u.property]
  have hc : Continuous (fun u : based y => align u.val z) := by
    rw [he]
    exact continuous_rotateLoop_family _ continuous_const _ continuous_subtype_val
  exact hc.subtype_mk _

def homeomorph {n : ℕ} (y z : Sphere n) : based y ≃ₜ based z where
  toFun := forward y z
  invFun := forward z y
  left_inv := reverse_forward y z
  right_inv := reverse_forward z y
  continuous_toFun := continuous_forward y z
  continuous_invFun := continuous_forward z y

def homologyIso {n : ℕ} (y z : Sphere n) (k : ℕ) :
    homologyZMod2 (TopCat.of (based y)) k ≅ homologyZMod2 (TopCat.of (based z)) k :=
  ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).mapIso
    (TopCat.isoOfHomeo (homeomorph y z))

theorem homology_zero_transport {n : ℕ} (y z : Sphere n) (k : ℕ)
    (h : IsZero (homologyZMod2 (TopCat.of (based y)) k)) :
    IsZero (homologyZMod2 (TopCat.of (based z)) k) := h.of_iso (homologyIso z y k)

end
end Finsler.H1BasedFiberTransport
