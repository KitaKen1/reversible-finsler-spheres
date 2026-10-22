module

public import Finsler.Loop.ConstantLoopModel
public import Finsler.Loop.RetractedPairNaturality
public import Finsler.Loop.RetractedPairCohomology
public import Finsler.Topology.LengthEnergyMaps

/-! Actual evaluation retractions to the ORIGINAL constant H1-loop
subspace, for every subspace containing constants. The same construction
commutes with all subspace inclusions, including every positive strict
Finsler length cut and the actual original fullPair. -/

@[expose] public section
namespace Finsler.ConstantSublevelRetract
open CategoryTheory Topology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def retraction {n : ℕ} (U : Set (Loops n)) (hU : consts n ⊆ U) :
    (pairOf hU).fst ⟶ (pairOf hU).snd :=
  SupportedCap.subspaceMap (Loops n) U ≫ TopCat.ofHom (BorelEvaluation.eval n) ≫
    ConstantLoopModel.fromSphere n

theorem left_inverse {n : ℕ} (U : Set (Loops n)) (hU : consts n ⊆ U) :
    (pairOf hU).map ≫ retraction U hU = 𝟙 (pairOf hU).snd := by
  ext u : 1
  apply Subtype.ext
  change constantSphereLoop (BorelEvaluation.eval n u.val) = u.val
  obtain ⟨P, hP⟩ := u.property
  rw [← hP, BorelEvaluation.eval_constant]

def inclusion {n : ℕ} {U V : Set (Loops n)} (hU : consts n ⊆ U) (hV : consts n ⊆ V)
    (hUV : U ⊆ V) : pairOf hU ⟶ pairOf hV :=
  TopPair.ofHom (TopCat.ofHom (ContinuousMap.inclusion hUV)) (𝟙 _) (by ext x : 1; rfl)

theorem retraction_square {n : ℕ} {U V : Set (Loops n)}
    (hU : consts n ⊆ U) (hV : consts n ⊆ V) (hUV : U ⊆ V) :
    TopPair.Hom.fst (inclusion hU hV hUV) ≫ retraction V hV =
      retraction U hU ≫ TopPair.Hom.snd (inclusion hU hV hUV) := by
  ext x : 1
  rfl

theorem section_natural {n : ℕ} {U V : Set (Loops n)}
    (hU : consts n ⊆ U) (hV : consts n ⊆ V) (hUV : U ⊆ V) :
    TopPair.singularChainComplexMap (inclusion hU hV hUV) coeff ≫
      RetractedPairChains.sectionMap (pairOf hV) (retraction V hV) (left_inverse V hV) =
    RetractedPairChains.sectionMap (pairOf hU) (retraction U hU) (left_inverse U hU) ≫
      push (TopPair.Hom.fst (inclusion hU hV hUV)) :=
  RetractedPairNaturality.sectionMap (inclusion hU hV hUV) _ _ _ _
    (retraction_square hU hV hUV)

theorem constants_short {n : ℕ} (F : ReversibleMetric n) {a : ℝ} (ha : 0 < a) :
    consts n ⊆ SelfCutOscillation.short F a := by
  rintro _ ⟨P, rfl⟩
  have he := SobolevEnergy.energy_constantSphereLoop F P
  have hs := SobolevLength.length_sq_le_energy F (constantSphereLoop P)
  have hz : SobolevLength.length F (constantSphereLoop P) = 0 := by
    nlinarith [SobolevLength.length_nonneg F (constantSphereLoop P)]
  change SobolevLength.length F (constantSphereLoop P) < a
  rw [hz]
  exact ha

def shortPair {n : ℕ} (F : ReversibleMetric n) {a : ℝ} (ha : 0 < a) : TopPair.{0} :=
  pairOf (constants_short F ha)

theorem full_relative_injective (n q : ℕ) :
    Function.Injective (relativeToPool (fullPair n) q).hom :=
  RetractedPairCohomology.relativeToPool_injective (fullPair n)
    (retraction Set.univ (Set.subset_univ _)) (left_inverse Set.univ (Set.subset_univ _)) q

theorem short_relative_injective {n : ℕ} (F : ReversibleMetric n) {a : ℝ} (ha : 0 < a) (q : ℕ) :
    Function.Injective (relativeToPool (shortPair F ha) q).hom :=
  RetractedPairCohomology.relativeToPool_injective (shortPair F ha)
    (retraction _ (constants_short F ha)) (left_inverse _ (constants_short F ha)) q

end
end Finsler.ConstantSublevelRetract
