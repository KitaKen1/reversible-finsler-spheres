module

public import Finsler.Loop.LocalNativeBallPairSum
public import Finsler.Loop.NeighborhoodComplementCutLoops
public import Finsler.Loop.NativeNorthWrappedChart

/-! Actual wrapped original strong-H1 cut maps on the WHOLE existing
ball product, including unequal sphere endpoints. The genuine tested
and retained maps exchange cohomology pullbacks. In particular wrapped
tested transgression plus forward tested transgression is remaining.
No full supported-cap value or global square gluing is claimed here. -/
@[expose] public section
namespace Finsler.LocalNativeWrappedBallCut
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def cutParameters {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.space P v₀ ⟶ SelfCutThomCocycle.parameters n :=
  LocalNativeBallCut.cutParameters P v₀ b ≫ WholeSelfCutComplement.complement n

theorem self_evaluation {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : LocalNativeBallCut.space P v₀) :
    SelfCutThomCocycle.selfEvaluation n (cutParameters P v₀ b z) = (z.2.1.val, z.1.val) := by
  have he := ConcreteCategory.congr_hom (WholeSelfCutComplement.selfEvaluation_exchange n)
    (LocalNativeBallCut.cutParameters P v₀ b z)
  exact he.trans (congrArg Prod.swap (LocalNativeBallCut.self_evaluation P v₀ b z))

theorem distance_eq {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : LocalNativeBallCut.space P v₀) :
    SupportedSelfCut.distance n (cutParameters P v₀ b z) =
      SupportedSelfCut.distance n (LocalNativeBallCut.cutParameters P v₀ b z) :=
  WholeSelfCutComplement.distance_complement n _

def toTube {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.space P v₀ ⟶ TopCat.of (H1SelfCutNeighborhood.tube n) :=
  LocalNativeBallCut.toTube P v₀ b ≫ NeighborhoodComplementCutLoops.tubeMap n

def testedH1 {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.space P v₀ ⟶ TopCat.of (SphereLoop n) :=
  toTube P v₀ b ≫ TopCat.ofHom ⟨H1SelfCutNeighborhood.left, H1SelfCutNeighborhood.continuous_left⟩

def retainedH1 {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.space P v₀ ⟶ TopCat.of (SphereLoop n) :=
  toTube P v₀ b ≫ TopCat.ofHom ⟨H1SelfCutNeighborhood.right, H1SelfCutNeighborhood.continuous_right⟩

theorem tested_half_shift {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : LocalNativeBallCut.space P v₀) :
    SobolevShift.shiftSphere (LocalNativeBallCut.retainedH1 P v₀ b z) (1 / 2) = testedH1 P v₀ b z :=
  NeighborhoodComplementCutLoops.retained_half_shift (LocalNativeBallCut.toTube P v₀ b z)

theorem retained_half_shift {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : LocalNativeBallCut.space P v₀) :
    SobolevShift.shiftSphere (LocalNativeBallCut.testedH1 P v₀ b z) (1 / 2) = retainedH1 P v₀ b z :=
  NeighborhoodComplementCutLoops.tested_half_shift (LocalNativeBallCut.toTube P v₀ b z)

def toNeighborhood {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (r : ℝ) :
    TopCat.of (LocalNativeBallCut.near P v₀ b r) ⟶ TopCat.of (SupportedSelfCut.neighborhood n r) :=
  LocalNativeBallCut.toNeighborhood P v₀ b r ≫ WholeSelfCutComplement.neighborhoodMap n r

theorem tested_restrict {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {r : ℝ} (hr : r ≤ 1) :
    SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (LocalNativeBallCut.near P v₀ b r) ≫ testedH1 P v₀ b =
      toNeighborhood P v₀ b r ≫ TopCat.ofHom (SupportedSelfCut.tested n hr) := by
  apply TopCat.ext
  intro z
  rfl

theorem retained_restrict {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {r : ℝ} (hr : r ≤ 1) :
    SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (LocalNativeBallCut.near P v₀ b r) ≫ retainedH1 P v₀ b =
      toNeighborhood P v₀ b r ≫ TopCat.ofHom (SupportedSelfCut.retained n hr) := by
  apply TopCat.ext
  intro z
  rfl

def tested {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.space P v₀ ⟶ ContinuousLoopModel.space n := testedH1 P v₀ b ≫ ContinuousLoopModel.inclusion n

def retained {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.space P v₀ ⟶ ContinuousLoopModel.space n := retainedH1 P v₀ b ≫ ContinuousLoopModel.inclusion n

theorem tested_cohomology_swap {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (tested P v₀ b) q).hom a = (cohPullback (LocalNativeBallCut.retained P v₀ b) q).hom a := by
  have he := congrArg (cohPullback (LocalNativeBallCut.toTube P v₀ b) q).hom
    (NeighborhoodComplementCutLoops.tested_cohomology_swap n q a)
  rw [← NativeMatchingTransgression.pullback_comp, ← NativeMatchingTransgression.pullback_comp] at he
  exact he

theorem retained_cohomology_swap {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (retained P v₀ b) q).hom a = (cohPullback (LocalNativeBallCut.tested P v₀ b) q).hom a := by
  have he := congrArg (cohPullback (LocalNativeBallCut.toTube P v₀ b) q).hom
    (NeighborhoodComplementCutLoops.retained_cohomology_swap n q a)
  rw [← NativeMatchingTransgression.pullback_comp, ← NativeMatchingTransgression.pullback_comp] at he
  exact he

theorem paired_transgression {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (LocalNativeBallCut.tested P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (tested P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))) q).hom
        ((cohPullback (ordinary P v₀) q).hom (ContinuousLoopSweep.transgression n q a)) := by
  rw [tested_cohomology_swap]
  exact LocalNativeBallPairSum.whole_ball_sum P v₀ b q a

end
end Finsler.LocalNativeWrappedBallCut
