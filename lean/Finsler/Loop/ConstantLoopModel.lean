module

public import Finsler.Topology.SphereTopClass

/-! Identify the ACTUAL constant H1-loop subspace with the sphere.
The inverse is actual point evaluation; the range witness proves its
inverse law. Positive cohomology vanishing is transported from Tau Ceti. -/

@[expose] public section
namespace Finsler.ConstantLoopModel
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.BorelEvaluation
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def fromSphere (n : ℕ) : sphere n ⟶ TopCat.of (consts n) :=
  TopCat.ofHom ⟨fun x => ⟨constantSphereLoop x, x, rfl⟩,
    (SphereTopClass.constantSphereLoop_continuous n).subtype_mk _⟩

def toSphere (n : ℕ) : TopCat.of (consts n) ⟶ sphere n :=
  TopCat.ofHom ⟨fun u => eval n u.val, (eval n).continuous.comp continuous_subtype_val⟩

theorem from_to (n : ℕ) : fromSphere n ≫ toSphere n = 𝟙 (sphere n) := by
  ext x : 1
  exact eval_constant x

theorem to_from (n : ℕ) : toSphere n ≫ fromSphere n = 𝟙 (TopCat.of (consts n)) := by
  ext u : 1
  apply Subtype.ext
  change constantSphereLoop (eval n u.val) = u.val
  obtain ⟨x, hx⟩ := u.property
  rw [← hx, eval_constant]

def iso (n : ℕ) : sphere n ≅ TopCat.of (consts n) :=
  ⟨fromSphere n, toSphere n, from_to n, to_from n⟩

def cohomologyEquiv (n k : ℕ) :
    cohomologyZMod2 (TopCat.of (consts n)) k ≃ₗ[ZMod 2] cohomologyZMod2 (sphere n) k :=
  ((singularCohomologyZMod2 k).mapIso (iso n).op).toLinearEquiv

theorem cohomology_eq_zero (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≠ n)
    (a : cohomologyZMod2 (TopCat.of (consts n)) k) : a = 0 := by
  apply (cohomologyEquiv n k).injective
  rw [map_zero]
  exact SphereTopClass.cohomology_eq_zero_of_ne n k hk hkn _

theorem cohomology_subsingleton (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≠ n) :
    Subsingleton (cohomologyZMod2 (TopCat.of (consts n)) k) :=
  ⟨fun a b => (cohomology_eq_zero n k hk hkn a).trans (cohomology_eq_zero n k hk hkn b).symm⟩

end
end Finsler.ConstantLoopModel
