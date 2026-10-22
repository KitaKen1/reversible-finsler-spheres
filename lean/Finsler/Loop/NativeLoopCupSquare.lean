module

public import Finsler.Loop.NativeBasedCupSquare
public import Finsler.Loop.NativeBVOrdinaryCupRotation

/-! Transport the proved square-zero property from actual based paths
through the H1 inclusion and actual punctured evaluation cover. The
result holds for EVERY degree m class on free loops for m>=2, so in
particular for the SAME original GH_0; no loop-space product splitting. -/
@[expose] public section
namespace Finsler.NativeLoopCupSquare
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.MeridianLoopFamily Finsler.H1PuncturedRelativeChart
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def basedPathMap {n : ℕ} (P : Sphere n) : TopCat.of (H1LocalFiber.based P) ⟶ BasedMeridianProducts.space P :=
  BasedContinuousLoopModel.inclusion P ≫ (TopCat.isoOfHomeo (BasedLoopPathSpace.homeomorph P)).hom

theorem basedPathMap_injective {n : ℕ} (P : Sphere n) (q : ℕ) :
    Function.Injective (homologyPushZMod2 (basedPathMap P) q).hom := by
  intro a b hab
  apply BasedLoopHomologyInjection.homology_injective P q
  apply (BasedLoopPathSpace.homologyIso P q).toLinearEquiv.injective
  rw [basedPathMap, ← SplitPairHomologyKernel.push_comp_apply, ← SplitPairHomologyKernel.push_comp_apply] at hab
  exact hab

variable (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)

include hm v₀ in
theorem based_square_zero (a : cohomologyZMod2 (TopCat.of (H1LocalFiber.based P)) m) : cupZMod2 a a = 0 :=
  CupSquareZeroTransport.along_injective_homology (basedPathMap P) m (basedPathMap_injective P m)
    (NativeBasedCupSquare.square_zero m hm P v₀) a

include hm v₀ in
theorem patch_square_zero (a : cohomologyZMod2 (TopCat.of (fullDomain P)) m) : cupZMod2 a a = 0 := by
  have hi : Function.Injective (homologyPushZMod2 (NativeEvaluationOverlapProduct.northAlignment P) m).hom := by
    rw [← NativeEvaluationPatchGeneration.alignment_homology]
    exact (H1PuncturedPatchHomology.fullDomainHomologyIso P m).toLinearEquiv.injective
  exact CupSquareZeroTransport.along_injective_homology _ m hi (based_square_zero m hm P v₀) a

include hm P v₀ in
theorem full_square_zero (a : cohomologyZMod2 (fullPair (m + 1)).fst m) : cupZMod2 a a = 0 := by
  let w : equator (antipode P) := (MeridianEquatorHomology.equator_nonempty (by omega) (antipode P)).some
  have hs : Function.Surjective (homologyPushZMod2
      (TopCat.ofHom (ContinuousMap.subtypeVal (fullDomain (antipode P)))) (m + m)).hom := by
    have h := NativeEvaluationPatchGeneration.south_generates P v₀ ((1 + 1) * m)
      (NativeGHCoverSurjectivity.fromPatches_surjective m hm P v₀ 1)
    exact (congrArg (fun q => Function.Surjective (homologyPushZMod2
      (TopCat.ofHom (ContinuousMap.subtypeVal (fullDomain (antipode P)))) q).hom)
      (show (1 + 1) * m = m + m by omega)).mp h
  exact CupSquareZeroTransport.detected_by_surjective_homology _ m hs
    (patch_square_zero m hm (antipode P) w) a

include hm P v₀ in
theorem square_zero (a : cohomologyZMod2 (Loops (m + 1)) m) : cupZMod2 a a = 0 := by
  apply (FullLoopModel.cohomologyEquiv (m + 1) (m + m)).injective
  change (cohPullback (FullLoopModel.forget (m + 1)) (m + m)).hom (cupZMod2 a a) =
    (cohPullback (FullLoopModel.forget (m + 1)) (m + m)).hom 0
  rw [map_zero, Cup.naturality]
  exact full_square_zero m hm P v₀ _

include hm P v₀ in
theorem primitive_square_zero : cupZMod2 (MeridianLoopClass.H1TransgressionClass m)
    (MeridianLoopClass.H1TransgressionClass m) = 0 := square_zero m hm P v₀ _

include hm P v₀ in
theorem original_square_class_zero (F : Geometry.ReversibleMetric (m + 1)) :
    cupZMod2 (cocycleClass _ m (NativeNearCutPrimitiveGH.original m hm F)
      (NativeNearCutPrimitiveGH.original_closed m hm F))
      (cocycleClass _ m (NativeNearCutPrimitiveGH.original m hm F)
      (NativeNearCutPrimitiveGH.original_closed m hm F)) = 0 := square_zero m hm P v₀ _

end
end Finsler.NativeLoopCupSquare
