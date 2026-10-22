module

public import Finsler.Analysis.H1LocalFiber
public import Finsler.Topology.RightConstantJoinHomotopy
public import Finsler.Topology.BorelLoop
public import TauCeti.Topology.Category.TopPair

/-! Upgrade the ACTUAL strong-H1 evaluation product chart to an
isomorphism of pairs with the actual constant-loop subspace. Under
the chart, constants are precisely base times the constant based loop.
This does not assert any unproved homology calculation of the fiber. -/
@[expose] public section
namespace Finsler.H1ConstantRelativeFiberChart
open CategoryTheory
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.H1LocalFiber Finsler.H1FiberBase Finsler.CompactH1Alignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def localConstants {n : ℕ} (y : Sphere n) : Set (nearFiber y) :=
  {u | u.val ∈ consts n}

def productConstants {n : ℕ} (y : Sphere n) : Set (nearBases y × based y) :=
  {p | p.2.val = constantSphereLoop y}

theorem chart_constants_iff {n : ℕ} (y : Sphere n) (u : nearFiber y) :
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

abbrev localPair {n : ℕ} (y : Sphere n) : TopPair.{0} :=
  TopPair.ofSubset (X := TopCat.of (nearFiber y)) (localConstants y)

abbrev productPair {n : ℕ} (y : Sphere n) : TopPair.{0} :=
  TopPair.ofSubset (X := TopCat.of (nearBases y × based y)) (productConstants y)

def chartIso {n : ℕ} (y : Sphere n) :
    TopCat.of (nearFiber y) ≅ TopCat.of (nearBases y × based y) :=
  TopCat.isoOfHomeo (chart y)

def forwardPair {n : ℕ} (y : Sphere n) : localPair y ⟶ productPair y :=
  TopPair.ofSubsetMap (chartIso y).hom
    (fun u hu => (chart_constants_iff y u).mpr hu)

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

theorem forwardPair_fst {n : ℕ} (y : Sphere n) :
    TopPair.Hom.fst (forwardPair y) = (chartIso y).hom := by
  unfold forwardPair
  ext u : 1
  exact TopPair.ofSubsetMap_fst_apply _ _ u

def pairIso {n : ℕ} (y : Sphere n) : localPair y ≅ productPair y := by
  letI : IsIso (TopPair.Hom.fst (forwardPair y)) := by
    rw [forwardPair_fst]
    infer_instance
  letI : IsIso (forwardPair y) :=
    TopPair.isIso_of_isIso_fst_of_surjective_snd (forwardPair y) (forwardPair_subspace_surjective y)
  exact asIso (forwardPair y)

theorem chart_evaluation {n : ℕ} (y : Sphere n) (u : nearFiber y) :
    (chart y u).1.val = point u.val := rfl

theorem inverse_evaluation {n : ℕ} (y : Sphere n) (p : nearBases y × based y) :
    point ((chart y).symm p).val = p.1.val := by
  apply Subtype.ext
  exact basepoint_align p.2.val p.1.val

end
end Finsler.H1ConstantRelativeFiberChart
