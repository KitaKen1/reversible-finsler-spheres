module

public import Finsler.Loop.FirstInputRotationTimeTrim
public import Finsler.Topology.FirstHalfInteriorNative

/-! The original native first-half cut domain maps into the genuine
rotation-one proper cut domain. Tested loops and the deformed retained
output agree exactly, with distinct open/closed tube radii explicit. -/

@[expose] public section
namespace Finsler.FirstInputRotationNativeDomain

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.H1SelfCutNeighborhood
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r₀ r₁ : ℝ)
  (hR : R ≤ 1 / 2) (hr₀ : r₀ < 1) (hr₁ : r₁ ≤ 1) (hr : r₁ ≤ r₀)
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

def toProper :
    C(FirstHalfInteriorFamily.domain (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))
      a ha ha1 r₁, FirstInputRotatingCut.source α β R r₀) := by
  refine ⟨fun z => ⟨(InteriorTimeSlide.trimTime a ha.le ha1.le z.val.1, z.val.2), ?_⟩, ?_⟩
  · have hd := FirstInputRotationFamily.time_distance α β R (hR.trans_lt (by norm_num))
      (InteriorTimeSlide.trimTime a ha.le ha1.le z.val.1) 1 z.val.2
    change distance n (InteriorTimeSlide.trimTime a ha.le ha1.le z.val.1,
      FirstInputRotationFamily.family α β R (hR.trans_lt (by norm_num)) (1, z.val.2)) = _ at hd
    rw [FirstInputRotationFamily.family_one] at hd
    change distance n (InteriorTimeSlide.trimTime a ha.le ha1.le z.val.1, α z.val.2.val.1) ≤ r₀
    rw [← hd]
    exact (show distance n (FirstHalfInteriorFamily.firstParameters
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 z.val) < r₁
        from z.property).le.trans hr
  · fun_prop

def intoRotation :
    TopCat.of (FirstHalfInteriorFamily.domain
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 r₁) ⟶
      FirstInputRotationCochains.space α β R r₀ :=
  TopCat.ofHom ⟨fun z => (1, toProper α β R r₀ r₁ hR hr a ha ha1 z),
    continuous_const.prodMk (toProper α β R r₀ r₁ hR hr a ha ha1).continuous⟩

theorem cut_agreement
    (z : FirstHalfInteriorFamily.domain
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 r₁) :
    FirstInputRotatingCut.rotation α β R r₀ hR hr₀
      (1, toProper α β R r₀ r₁ hR hr a ha ha1 z) =
      (FirstHalfInteriorFamily.input
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ z).val.1 := by
  apply Subtype.ext
  rw [FirstInputRotatingCut.rotation_parameters α β R r₀ hR hr₀ (hR.trans_lt (by norm_num)),
    FirstInputRotationFamily.family_one]
  rfl

theorem tested_map :
    FirstHalfInteriorTested.sourceMap
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ =
      intoRotation α β R r₀ r₁ hR hr a ha ha1 ≫ FirstInputRotationCochains.testedMap α β R r₀ hR hr₀ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change (FirstHalfInteriorFamily.family
    (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ (0, z)).1 =
      left (FirstInputRotatingCut.rotation α β R r₀ hR hr₀
        (1, toProper α β R r₀ r₁ hR hr a ha ha1 z))
  rw [FirstHalfInteriorFamily.tested_fixed, cut_agreement]

theorem retained_eq
    (z : FirstHalfInteriorFamily.domain
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 r₁) :
    (FirstHalfInteriorFamily.family
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ (1, z)).2 =
      FirstInputRotatingFixedOutput.output α β R r₀ hR hr₀
        (toProper α β R r₀ r₁ hR hr a ha ha1 z) := by
  rw [FirstHalfInteriorFamily.family_one]
  change FirstHalfRetainedHomotopy.targetMap
    (FirstHalfInteriorFamily.input
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ z) =
        (H1JoinContinuity.joinMap (1 / 2) (by norm_num) (by norm_num))
          (FirstInputRotatingFixedOutput.endPair α β R r₀ hR hr₀
            (toProper α β R r₀ r₁ hR hr a ha ha1 z))
  apply congrArg (H1JoinContinuity.joinMap (1 / 2) (by norm_num) (by norm_num))
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg right (cut_agreement α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 z).symm
  · rfl

theorem tested_cochain (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback (intoRotation α β R r₀ r₁ hR hr a ha ha1) p
      (FirstInputRotationCochains.tested α β R r₀ hR hr₀ p T) =
      cochainPullback (FirstHalfInteriorTested.sourceMap
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁) p T := by
  rw [FirstInputRotationCochains.tested, ← pullback_comp, ← tested_map α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1]

end
end Finsler.FirstInputRotationNativeDomain
