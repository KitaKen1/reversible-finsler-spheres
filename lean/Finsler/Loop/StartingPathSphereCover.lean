module

public import Finsler.Loop.StartingPathSpace
public import Finsler.Loop.H1PuncturedEvaluationChart

/-! The ACTUAL starting-point path space is covered by the two
endpoint-puncture opens. Since that actual total space contracts,
the actual MV map from the overlap onto the patch sum is surjective
in every positive degree. One actual fixed-end fiber maps into both. -/
@[expose] public section
namespace Finsler.StartingPathSphereCover
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison
open Finsler.H1PuncturedEvaluationChart Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

abbrev total {n : ℕ} (x : Sphere n) : TopCat.{0} := StartingPathSpace.space (TopCat.of (Sphere n)) x
def domain {n : ℕ} (x axis : Sphere n) : Set (total x) :=
  (StartingPathSpace.endpoint (TopCat.of (Sphere n)) x) ⁻¹' base axis

theorem domain_open {n : ℕ} (x axis : Sphere n) : IsOpen (domain x axis) :=
  (base_open axis).preimage (StartingPathSpace.endpoint (TopCat.of (Sphere n)) x).hom.continuous

theorem domain_cover {n : ℕ} (x axis : Sphere n) :
    domain x axis ∪ domain x (antipode axis) = Set.univ := by
  change (StartingPathSpace.endpoint (TopCat.of (Sphere n)) x) ⁻¹' base axis ∪
    (StartingPathSpace.endpoint (TopCat.of (Sphere n)) x) ⁻¹' base (antipode axis) = Set.univ
  rw [← Set.preimage_union, base_cover, Set.preimage_univ]

abbrev patch {n : ℕ} (x axis : Sphere n) : TopCat.{0} := TopCat.of (domain x axis)
abbrev overlap {n : ℕ} (x axis : Sphere n) : TopCat.{0} :=
  TopCat.of (domain x axis ∩ domain x (antipode axis) : Set (total x))
abbrev patches {n : ℕ} (x axis : Sphere n) (k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  homologyZMod2 (patch x axis) k ⊞ homologyZMod2 (patch x (antipode axis)) k

def north {n : ℕ} (x axis : Sphere n) : overlap x axis ⟶ patch x axis :=
  TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)
def south {n : ℕ} (x axis : Sphere n) : overlap x axis ⟶ patch x (antipode axis) :=
  TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_right)
def inclusion {n : ℕ} (x axis : Sphere n) : patch x axis ⟶ total x :=
  TopCat.ofHom (ContinuousMap.subtypeVal (domain x axis))

def toPatches {n : ℕ} (x axis : Sphere n) (k : ℕ) :
    homologyZMod2 (overlap x axis) k ⟶ patches x axis k :=
  SSet.mayerVietorisToBiprod coeff (TopCat.toSSet.map (north x axis))
    (TopCat.toSSet.map (south x axis)) k
def fromPatches {n : ℕ} (x axis : Sphere n) (k : ℕ) :
    patches x axis k ⟶ homologyZMod2 (total x) k :=
  SSet.mayerVietorisFromBiprod coeff (TopCat.toSSet.map (inclusion x axis))
    (TopCat.toSSet.map (inclusion x (antipode axis))) k

theorem toPatches_surjective {n : ℕ} (x axis : Sphere n) (k : ℕ) :
    Function.Surjective (toPatches x axis (k + 1)).hom := by
  have hs := TopCat.mayerVietoris_exact₂ (X := total x) coeff (domain_open x axis)
    (domain_open x (antipode axis)) (domain_cover x axis) (k + 1)
  have ht := ModuleCat.subsingleton_of_isZero
    (StartingPathSpace.positive_homology_zero (TopCat.of (Sphere n)) x k)
  intro z
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp hs z (ht.elim _ _)
  exact ⟨w, hw⟩

def fiberToOverlap {n : ℕ} (x axis z : Sphere n) (hz : z ∈ base axis ∩ base (antipode axis)) :
    TopCat.of (Path x z) ⟶ overlap x axis :=
  TopCat.ofHom ⟨fun p => ⟨⟨p.toContinuousMap, p.source⟩, by
    change p 1 ∈ base axis ∩ base (antipode axis)
    rw [p.target]
    exact hz⟩, (continuous_induced_dom.subtype_mk _).subtype_mk _⟩

end
end Finsler.StartingPathSphereCover
