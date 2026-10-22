module

public import Finsler.Loop.H1PuncturedEvaluationChart
public import Finsler.Loop.FullLoopModel

/-! Actual constant-relative product charts on the TWO open
punctured evaluation domains. Their maps land in the ORIGINAL full
loop pair; the cover is also checked on its actual univ-subtype model.
No Mayer-Vietoris or homology vanishing is inferred from the cover. -/
@[expose] public section
namespace Finsler.H1PuncturedRelativeChart
open CategoryTheory
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.H1LocalFiber (based)
open Finsler.H1FiberBase Finsler.CompactH1Alignment
open Finsler.H1PuncturedEvaluationChart Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

def localConstants {n : ℕ} (y : Sphere n) : Set (fiber y) := {u | u.val ∈ consts n}
def productConstants {n : ℕ} (y : Sphere n) : Set (base y × based y) :=
  {p | p.2.val = constantSphereLoop y}

theorem chart_constants_iff {n : ℕ} (y : Sphere n) (u : fiber y) :
    chart y u ∈ productConstants y ↔ u ∈ localConstants y := by
  constructor
  · intro hu
    have he := congrArg Subtype.val (inverse_forward y u)
    change align (align u.val y) (point u.val) = u.val at he
    change align u.val y = constantSphereLoop y at hu
    rw [hu, RightConstantJoinHomotopy.align_constant] at he
    exact ⟨point u.val, he⟩
  · rintro ⟨x, hx⟩
    change align u.val y = constantSphereLoop y
    rw [← hx, RightConstantJoinHomotopy.align_constant]

abbrev pair {n : ℕ} (y : Sphere n) : TopPair.{0} :=
  TopPair.ofSubset (X := TopCat.of (fiber y)) (localConstants y)
abbrev productPair {n : ℕ} (y : Sphere n) : TopPair.{0} :=
  TopPair.ofSubset (X := TopCat.of (base y × based y)) (productConstants y)

def chartIso {n : ℕ} (y : Sphere n) :
    TopCat.of (fiber y) ≅ TopCat.of (base y × based y) := TopCat.isoOfHomeo (chart y)

def forwardPair {n : ℕ} (y : Sphere n) : pair y ⟶ productPair y :=
  TopPair.ofSubsetMap (chartIso y).hom (fun u hu => (chart_constants_iff y u).mpr hu)

theorem forwardPair_fst {n : ℕ} (y : Sphere n) :
    TopPair.Hom.fst (forwardPair y) = (chartIso y).hom := by
  unfold forwardPair
  ext u : 1
  exact TopPair.ofSubsetMap_fst_apply _ _ u

theorem forwardPair_subspace_surjective {n : ℕ} (y : Sphere n) :
    Function.Surjective (TopPair.Hom.snd (forwardPair y)) := by
  intro p
  have hp : chart y ((chart y).symm p.val) ∈ productConstants y := by
    rw [Homeomorph.apply_symm_apply]
    exact p.property
  refine ⟨⟨(chart y).symm p.val, (chart_constants_iff y _).mp hp⟩, ?_⟩
  apply Subtype.ext
  rw [forwardPair, TopPair.ofSubsetMap_snd_apply]
  exact (chart y).apply_symm_apply p.val

def pairIso {n : ℕ} (y : Sphere n) : pair y ≅ productPair y := by
  letI : IsIso (TopPair.Hom.fst (forwardPair y)) := by rw [forwardPair_fst]; infer_instance
  letI : IsIso (forwardPair y) := TopPair.isIso_of_isIso_fst_of_surjective_snd (forwardPair y)
    (forwardPair_subspace_surjective y)
  exact asIso (forwardPair y)

def toFull {n : ℕ} (y : Sphere n) : pair y ⟶ fullPair n :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun u => ⟨u.val, Set.mem_univ _⟩, continuous_subtype_val.subtype_mk _⟩)
    (TopCat.ofHom ⟨fun u => ⟨u.val.val, u.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩)

def evaluation {n : ℕ} (y : Sphere n) : (pair y).fst ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun u => point u.val, continuous_point.comp continuous_subtype_val⟩

theorem evaluation_square {n : ℕ} (y : Sphere n) :
    TopPair.Hom.fst (toFull y) ≫ BorelEvaluation.fullEval n = evaluation y := by ext u : 1; rfl

def fullDomain {n : ℕ} (y : Sphere n) : Set (fullPair n).fst :=
  {u | point u.val ∈ base y}

theorem fullDomain_open {n : ℕ} (y : Sphere n) : IsOpen (fullDomain y) :=
  (H1PuncturedEvaluationChart.base_open y).preimage (continuous_point.comp continuous_subtype_val)

theorem fullDomain_cover {n : ℕ} (y : Sphere n) :
    fullDomain y ∪ fullDomain (antipode y) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro u
  have he : point u.val ∈ base y ∪ base (antipode y) := by rw [base_cover]; trivial
  exact he

def fullDomainHomeomorph {n : ℕ} (y : Sphere n) : fiber y ≃ₜ fullDomain y where
  toFun u := ⟨⟨u.val, Set.mem_univ _⟩, u.property⟩
  invFun u := ⟨u.val.val, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem toFull_factor {n : ℕ} (y : Sphere n) :
    TopPair.Hom.fst (toFull y) =
      TopCat.ofHom ⟨fullDomainHomeomorph y, (fullDomainHomeomorph y).continuous⟩ ≫
        SupportedCap.subspaceMap (fullPair n).fst (fullDomain y) := by ext u : 1; rfl

end
end Finsler.H1PuncturedRelativeChart
