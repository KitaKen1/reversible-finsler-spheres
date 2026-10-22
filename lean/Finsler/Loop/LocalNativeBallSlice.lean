module

public import Finsler.Loop.LocalNativeBallCut
public import Finsler.Loop.NativeMatchingTestedPairing

/-! Identify the TRUE Q,Q slice of the whole-ball original cut
extension with the OLD matching-meridian cut maps. The exact actual
clocks and repeated directions are compared BEFORE the strong-H1
construction. Thus original tested transgression is zero for the
two adjacent branches and the remaining primitive for the nonadjacent
branch on the WHOLE ball product. This is not a Thom-cap value. -/
@[expose] public section
namespace Finsler.LocalNativeBallSlice
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SobolevCircleRepresentative
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def centerParameter {n : ℕ} (P : Sphere n) (v₀ : equator P) : MeridianNorthParameterChart.sourceSet P :=
  MeridianNorthParameterChart.inverse P ⟨LocalNativeBallCut.center P v₀,
    NativeNorthSupportPatch.close_north P v₀ _ (by simp)⟩
def centerTime {n : ℕ} (P : Sphere n) (v₀ : equator P) := (centerParameter P v₀).val.1
def centerDirection {n : ℕ} (P : Sphere n) (v₀ : equator P) := (centerParameter P v₀).val.2

def matchingMap {n : ℕ} (P : Sphere n) (s : ClosedInterval) (v : equator P) :
    TopCat.of (equator P) ⟶ NativeMeridianPairCoordinates.parameters P :=
  TopCat.ofHom ⟨fun w => ((s, v), ((s, v), w)),
    (continuous_const.prodMk continuous_const).prodMk
      ((continuous_const.prodMk continuous_const).prodMk continuous_id)⟩

theorem matching_source {n : ℕ} (P : Sphere n) (b : Fin 3) (s : ClosedInterval) (v : equator P) :
    matchingMap P s v ≫ NativeMeridianPairCoordinates.intoSource P b =
      NativeMatchingTestedPairing.middleSlice P s v ≫ NativeMeridianMatchingLoci.intoSource P b := by
  apply TopCat.ext
  intro w
  fin_cases b <;> rfl

theorem matching_cut {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (s : ClosedInterval) (v : equator P) :
    matchingMap P s v ≫ NativeMeridianPairCoordinates.intoCut P v₀ b =
      NativeMatchingTestedPairing.middleSlice P s v ≫ NativeMeridianMatchingLoci.intoCut P v₀ b := by
  change (matchingMap P s v ≫ NativeMeridianPairCoordinates.intoSource P b) ≫ NativeTripleSelfEvaluation.intoCut P v₀ =
    (NativeMatchingTestedPairing.middleSlice P s v ≫ NativeMeridianMatchingLoci.intoSource P b) ≫ NativeTripleSelfEvaluation.intoCut P v₀
  exact congrArg (fun f => f ≫ NativeTripleSelfEvaluation.intoCut P v₀) (matching_source P b s v)

theorem native_center {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    SmallBallProductReduction.sectionMap (LocalNativeBallCut.center P v₀) (TopCat.of (equator P)) ≫
      LocalNativeBallCut.toNative P v₀ = matchingMap P (centerTime P v₀) (centerDirection P v₀) := by
  apply TopCat.ext
  intro w
  rfl

theorem cut_center {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    SmallBallProductReduction.sectionMap (LocalNativeBallCut.center P v₀) (TopCat.of (equator P)) ≫
      LocalNativeBallCut.cutParameters P v₀ b =
      NativeMatchingTestedPairing.middleSlice P (centerTime P v₀) (centerDirection P v₀) ≫
        NativeMeridianMatchingLoci.intoCut P v₀ b := by
  change (_ ≫ LocalNativeBallCut.toNative P v₀) ≫ NativeMeridianPairCoordinates.intoCut P v₀ b = _
  rw [native_center]
  exact matching_cut P v₀ b _ _

theorem tube_center {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    SmallBallProductReduction.sectionMap (LocalNativeBallCut.center P v₀) (TopCat.of (equator P)) ≫
      LocalNativeBallCut.toTube P v₀ b =
      NativeMatchingTestedPairing.middleSlice P (centerTime P v₀) (centerDirection P v₀) ≫
        NativeMeridianMatchingLoci.intoDiagonal P v₀ b ≫
          TopCat.ofHom ⟨DiagonalSelfCutRepresentatives.intoTube, DiagonalSelfCutRepresentatives.continuous_intoTube n⟩ := by
  apply TopCat.ext
  intro w
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (cut_center P v₀ b) w

theorem testedSlice_matching {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.testedSlice P v₀ b =
      NativeMatchingTestedPairing.middleSlice P (centerTime P v₀) (centerDirection P v₀) ≫
        NativeMatchingAdjacentFactors.testedMap P v₀ b := by
  apply TopCat.ext
  intro w
  exact congrArg (fun z : H1SelfCutNeighborhood.tube n => sphereCircleMap (H1SelfCutNeighborhood.left z))
    (ConcreteCategory.congr_hom (tube_center P v₀ b) w)

theorem retainedSlice_matching {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.retainedSlice P v₀ b =
      NativeMatchingTestedPairing.middleSlice P (centerTime P v₀) (centerDirection P v₀) ≫
        NativeMatchingRetainedFactors.retainedMap P v₀ b := by
  apply TopCat.ext
  intro w
  exact congrArg (fun z : H1SelfCutNeighborhood.tube n => sphereCircleMap (H1SelfCutNeighborhood.right z))
    (ConcreteCategory.congr_hom (tube_center P v₀ b) w)

theorem adjacent01_constant {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    LocalNativeBallCut.testedSlice P v₀ 0 = TopCat.ofHom (ContinuousMap.const (equator P)
      (NativeMatchingAdjacentFactors.testedMap P v₀ 0 (centerTime P v₀, (centerDirection P v₀, v₀)))) := by
  rw [testedSlice_matching]
  apply TopCat.ext
  intro w
  exact NativeMatchingAdjacentFactors.adjacent01_independent P v₀ (centerDirection P v₀) w v₀ (centerTime P v₀)

theorem adjacent12_constant {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    LocalNativeBallCut.testedSlice P v₀ 2 = TopCat.ofHom (ContinuousMap.const (equator P)
      (NativeMatchingAdjacentFactors.testedMap P v₀ 2 (centerTime P v₀, (centerDirection P v₀, v₀)))) := by
  rw [testedSlice_matching]
  apply TopCat.ext
  intro w
  exact NativeMatchingAdjacentFactors.adjacent12_independent P v₀ (centerDirection P v₀) w v₀ (centerTime P v₀)

theorem adjacent01_slice_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) (hq : q ≠ 0)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (LocalNativeBallCut.testedSlice P v₀ 0) q).hom a = 0 := by
  rw [adjacent01_constant]
  exact NativeMatchingTestedPairing.constant_pullback_zero (TopCat.of (equator P)) (ContinuousLoopModel.space n)
    (NativeMatchingAdjacentFactors.testedMap P v₀ 0 (centerTime P v₀, (centerDirection P v₀, v₀))) q hq a

theorem adjacent12_slice_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) (hq : q ≠ 0)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (LocalNativeBallCut.testedSlice P v₀ 2) q).hom a = 0 := by
  rw [adjacent12_constant]
  exact NativeMatchingTestedPairing.constant_pullback_zero (TopCat.of (equator P)) (ContinuousLoopModel.space n)
    (NativeMatchingAdjacentFactors.testedMap P v₀ 2 (centerTime P v₀, (centerDirection P v₀, v₀))) q hq a

theorem nonadjacent_slice (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (LocalNativeBallCut.testedSlice P v₀ 1) m).hom (MeridianLoopClass.ordinaryTransgression m) =
      (cohPullback (ordinary P v₀) m).hom (MeridianLoopClass.ordinaryTransgression m) := by
  rw [testedSlice_matching]
  exact NativeMatchingTestedPairing.tested_pullback m hm P v₀ (centerTime P v₀) (centerDirection P v₀)

theorem adjacent01_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) (hq : q ≠ 0)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (LocalNativeBallCut.tested P v₀ 0) q).hom a = 0 := by
  rw [LocalNativeBallCut.tested_reduced, adjacent01_slice_zero P v₀ q hq a, map_zero]

theorem adjacent12_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) (hq : q ≠ 0)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (LocalNativeBallCut.tested P v₀ 2) q).hom a = 0 := by
  rw [LocalNativeBallCut.tested_reduced, adjacent12_slice_zero P v₀ q hq a, map_zero]

theorem nonadjacent_reduced (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (LocalNativeBallCut.tested P v₀ 1) m).hom (MeridianLoopClass.ordinaryTransgression m) =
      (cohPullback (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))) m).hom
        ((cohPullback (ordinary P v₀) m).hom (MeridianLoopClass.ordinaryTransgression m)) := by
  rw [LocalNativeBallCut.tested_reduced, nonadjacent_slice m hm P v₀]

end
end Finsler.LocalNativeBallSlice
