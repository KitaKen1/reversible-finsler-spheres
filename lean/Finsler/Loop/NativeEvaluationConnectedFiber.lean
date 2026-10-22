module

public import Finsler.Loop.SphereProductHomologyDetection
public import Finsler.Loop.H1BasedFiberTransport

/-! Apply the proved sphere-product detector to the ORIGINAL H1
evaluation overlap. Its only fiber-topology input is genuine path
connectedness of the genuine based strong-H1 loop space. This input
and the based degree-n homology gaps are not asserted here. -/
@[expose] public section
namespace Finsler.NativeEvaluationConnectedFiber
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.H1LocalFiber (based)
open Finsler.MeridianLoopFamily Finsler.MeridianEquatorHomology
open Finsler.H1PuncturedEvaluationChart Finsler.NativeEvaluationMayerVietoris
open Finsler.ProductHomologyZeroDetection Finsler.ProductHomologyDetectionTransport
open Finsler.NativeEvaluationOverlapProduct
open scoped ContinuousMap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem baseOverlap_eq {n : ℕ} (y : Sphere n) :
    (base y ∩ base (antipode y) : Set (Sphere n)) =
      ({antipode y}ᶜ ∩ {-antipode y}ᶜ : Set (Sphere n)) := by
  ext x
  rfl

def baseOverlapEquiv {n : ℕ} (y : Sphere n) :
    baseOverlap y ≃ₕ orthogonalSphere (antipode y) :=
  (Homeomorph.setCongr (baseOverlap_eq y)).toHomotopyEquiv.trans
    (TauCeti.equatorHomotopyEquiv (antipode y))

theorem product_detects (m : ℕ) (y : Sphere (m + 1)) [PathConnectedSpace (based y)] :
    ∀ c : homologyZMod2 (model y) m,
      (homologyPushZMod2 (baseProjection y) m).hom c = 0 →
      (homologyPushZMod2 (fiberProjection y) m).hom c = 0 → c = 0 := by
  change Detects (baseOverlap y) (TopCat.of (based y)) m
  exact detects_of_equiv (baseOverlapEquiv y) _ m
    (SphereProductHomologyDetection.detects_sphere m (orthogonal_dimension (antipode y)) _)

theorem joint_overlap (m : ℕ) (y : Sphere (m + 1)) [PathConnectedSpace (based y)]
    (z : homologyZMod2 (overlap y) m)
    (he : (homologyPushZMod2 (overlapEvaluation y) m).hom z = 0)
    (hp : (toPatches y m).hom z = 0) : z = 0 :=
  NativeEvaluationProductDetection.joint_overlap_of_product_projections y m (product_detects m y) z he hp

theorem original_UNIT_of_based_gap_and_pathConnected (m : ℕ) (hm : 2 ≤ m)
    (y : Sphere (m + 1)) (v₀ : equator y) [PathConnectedSpace (based y)]
    (hN : IsZero (homologyZMod2 (TopCat.of (based y)) (m + 1))) :
    NativeConstantUnitDefect.cutFull m (by omega) y v₀ =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  NativeEvaluationProductDetection.original_UNIT_of_based_gap_and_product_detection m hm y v₀ hN
    (H1BasedFiberTransport.homology_zero_transport y (antipode y) (m + 1) hN) (product_detects m y)

theorem original_relativeCut_zero_of_based_gap_and_pathConnected (m : ℕ) (hm : 2 ≤ m)
    (y : Sphere (m + 1)) (v₀ : equator y) [PathConnectedSpace (based y)]
    (hN : IsZero (homologyZMod2 (TopCat.of (based y)) (m + 1))) :
    NativeConstantUnitDefect.relativeCut m (by omega) y v₀ = 0 :=
  NativeEvaluationPatchGap.original_relativeCut_zero_of_based_gap_and_overlap m hm y v₀ hN
    (H1BasedFiberTransport.homology_zero_transport y (antipode y) (m + 1) hN) (joint_overlap m y)

end
end Finsler.NativeEvaluationConnectedFiber
