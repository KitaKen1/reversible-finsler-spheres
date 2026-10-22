module

public import Finsler.Loop.H1PuncturedRelativeChart
public import TauCeti.AlgebraicTopology.Sphere.Puncture
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-! The ACTUAL entire punctured evaluation patch is homotopy
equivalent to the ACTUAL strong-H1 based loop space. Use pinned
TauCeti contractibility of a punctured sphere; the resulting forward
map is the existing concrete alignment, not an abstract substitute. -/
@[expose] public section
namespace Finsler.H1PuncturedPatchHomology
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison
open Finsler.H1LocalFiber (based)
open Finsler.H1PuncturedEvaluationChart
open scoped ContinuousMap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

theorem base_contractible {n : ℕ} (y : Sphere n) : ContractibleSpace (base y) := by
  change ContractibleSpace ({MeridianLoopFamily.antipode y}ᶜ : Set (Sphere n))
  exact TauCeti.contractibleSpace_sphere_compl_singleton _

def baseEquiv {n : ℕ} (y : Sphere n) : (base y) ≃ₕ Unit := by
  letI := base_contractible y
  exact (ContractibleSpace.hequiv_unit (base y)).some

def productEquiv {n : ℕ} (y : Sphere n) : (base y × based y) ≃ₕ based y :=
  ((baseEquiv y).prodCongr (ContinuousMap.HomotopyEquiv.refl (based y))).trans
    (Homeomorph.uniqueProd Unit (based y)).toHomotopyEquiv

def patchEquiv {n : ℕ} (y : Sphere n) : fiber y ≃ₕ based y :=
  (chart y).toHomotopyEquiv.trans (productEquiv y)

theorem patchEquiv_apply {n : ℕ} (y : Sphere n) (u : fiber y) :
    ((patchEquiv y).toFun u).val = CompactH1Alignment.align u.val y := rfl

def patchHomologyIso {n : ℕ} (y : Sphere n) (k : ℕ) :
    homologyZMod2 (TopCat.of (fiber y)) k ≅ homologyZMod2 (TopCat.of (based y)) k :=
  (patchEquiv y).singularHomologyIso coeff k

def fullDomainHomologyIso {n : ℕ} (y : Sphere n) (k : ℕ) :
    homologyZMod2 (TopCat.of (H1PuncturedRelativeChart.fullDomain y)) k ≅
      homologyZMod2 (TopCat.of (based y)) k :=
  ((H1PuncturedRelativeChart.fullDomainHomeomorph y).symm.toHomotopyEquiv.singularHomologyIso coeff k).trans
    (patchHomologyIso y k)

theorem fullDomain_homology_zero_of_based {n : ℕ} (y : Sphere n) (k : ℕ)
    (h : IsZero (homologyZMod2 (TopCat.of (based y)) k)) :
    IsZero (homologyZMod2 (TopCat.of (H1PuncturedRelativeChart.fullDomain y)) k) :=
  h.of_iso (fullDomainHomologyIso y k)

end
end Finsler.H1PuncturedPatchHomology
