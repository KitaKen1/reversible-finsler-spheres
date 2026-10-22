module

public import Finsler.Loop.FirstInputRotationTimeEndpoints
public import Finsler.Loop.FirstInputRotationOriginalFactors
public import Finsler.Loop.TubeExtensionSquare

/-! At rotation zero the actual full-cylinder Thom/tested cup,
including the literal tested zero extension, factors through the
original first input and cut time. No global closure of that extension
or of this cup is asserted. -/

@[expose] public section
namespace Finsler.FirstInputRotationZeroTimeFactors

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedCapNaturality
open Finsler.FirstInputRotationCutCylinder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)

def projection : TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R) ⟶
    TopCat.of (ClosedInterval × P) :=
  TopCat.ofHom ⟨fun z => (z.1, z.2.val.1), by fun_prop⟩

def properZero : TopCat.of (FirstInputRotatingCut.source α β R r) ⟶
    TopCat.of (FirstInputRotationAmbientCover.proper α β R r) :=
  TopCat.ofHom ⟨fun z => ⟨(0, z.val), z.property⟩, by fun_prop⟩

theorem properZero_square :
    properZero α β R r ≫ SupportedCap.subspaceMap
      (FirstInputRotationAmbientCover.ambient α β R) (FirstInputRotationAmbientCover.proper α β R r) =
      SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (FirstInputRotatingCut.source α β R r) ≫
          FirstInputRotationTimeEndpoints.cylinderSlice α β R 0 ≫ reorder α β R := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem properZero_stage :
    properZero α β R r ≫ (FirstInputRotationAmbientCover.properIso α β R r).inv =
      FirstInputRotationEndpoints.stage α β R r 0 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem projection_square :
    FirstInputRotationOriginalFactors.projection α β R r ≫
      SupportedCap.subspaceMap (TopCat.of (ClosedInterval × P)) (CompactRotatedCutData.source α r) =
      SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (FirstInputRotatingCut.source α β R r) ≫ projection α β R := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable (hR : R ≤ 1 / 2) (hr : r < 1)

def originalThom {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × P)) (m + 1) :=
  AnnularSelfCut.familyCocycle (m + 1) (by omega) h α

def originalTested (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) :
    singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × P)) p :=
  TubeCochainExtension.extend (TopCat.of (ClosedInterval × P)) (CompactRotatedCutData.source α r) p
    (cochainPullback (FirstInputRotationOriginalFactors.originalTester α r hr) p T)

theorem thom_zero {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (FirstInputRotationTimeEndpoints.cylinderSlice α β R 0) (m + 1)
      (thom α β R hR (by omega) h) =
      cochainPullback (projection α β R) (m + 1) (originalThom α h) := by
  have he : (FirstInputRotationTimeEndpoints.cylinderSlice α β R 0 ≫ reorder α β R) ≫
      FirstInputRotationAmbientCover.ambientEvaluation α β R hR =
        projection α β R ≫ AnnularSelfCut.familyMap α := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    change (z.1, FirstInputRotationFamily.family α β R (hR.trans_lt (by norm_num)) (0, z.2)) = _
    rw [FirstInputRotationFamily.family_zero]
    rfl
  change cochainPullback _ (m + 1)
    (cochainPullback (reorder α β R) (m + 1)
      (cochainPullback (FirstInputRotationAmbientCover.ambientEvaluation α β R hR) (m + 1)
        (AnnularSelfCut.cocycle (m + 1) (by omega) h))) = _
  rw [← pullback_comp, ← pullback_comp, he, pullback_comp]
  rfl

theorem tested_zero (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) :
    cochainPullback (FirstInputRotationTimeEndpoints.cylinderSlice α β R 0) p
      (tested α β R r hR hr p T) =
      cochainPullback (projection α β R) p (originalTested α r hr p T) := by
  have hrot := TubeExtensionSquare.pullback_extend
    (FirstInputRotationTimeEndpoints.cylinderSlice α β R 0 ≫ reorder α β R)
    (FirstInputRotationAmbientCover.proper α β R r) (FirstInputRotatingCut.source α β R r)
    (properZero α β R r) (fun _ => Iff.rfl) (properZero_square α β R r) p
    (cochainPullback (FirstInputRotationAmbientCover.properIso α β R r).inv p
      (FirstInputRotationCochains.tested α β R r hR hr p T))
  have horig := TubeExtensionSquare.pullback_extend (projection α β R)
    (CompactRotatedCutData.source α r) (FirstInputRotatingCut.source α β R r)
    (FirstInputRotationOriginalFactors.projection α β R r) (fun _ => Iff.rfl)
    (projection_square α β R r) p
    (cochainPullback (FirstInputRotationOriginalFactors.originalTester α r hr) p T)
  rw [← pullback_comp, properZero_stage,
    FirstInputRotationOriginalFactors.tested_zero α β R r hR hr p T] at hrot
  change cochainPullback _ p (cochainPullback (reorder α β R) p
    (FirstInputRotationAmbientCap.ambientTested α β R r hR hr p T)) = _
  rw [← pullback_comp]
  exact hrot.trans horig.symm

def originalGamma {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) :
    singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × P)) ((m + 1) + p) :=
  cochainCup (m + 1) p (originalThom α h) (originalTested α r hr p T)

theorem gamma_zero {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) :
    cochainPullback (FirstInputRotationTimeEndpoints.cylinderSlice α β R 0) ((m + 1) + p)
      (cochainCup (m + 1) p (thom α β R hR (by omega) h) (tested α β R r hR hr p T)) =
      cochainPullback (projection α β R) ((m + 1) + p) (originalGamma α r hr h p T) := by
  rw [cochainCup_naturality, thom_zero, tested_zero, ← cochainCup_naturality]
  rfl

end
end Finsler.FirstInputRotationZeroTimeFactors
