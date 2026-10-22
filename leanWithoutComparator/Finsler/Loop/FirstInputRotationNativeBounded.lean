module

public import Finsler.Loop.FirstInputRotationNativeDomain
public import Finsler.Topology.FirstHalfAnnularTimeDomain

/-! Map the original bounded first-half cut domain into the actual
bounded rotation domain. Its deformed retained map and source square
agree exactly, inside the same length threshold. -/

@[expose] public section
namespace Finsler.FirstInputRotationNativeBounded

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality
open Finsler.FirstInputRotationCutCylinder Finsler.FirstInputRotationTimeTrim

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r₀ r₁ : ℝ)
  (hR : R ≤ 1 / 2) (hr₀ : r₀ < 1) (hr₁ : r₁ ≤ 1) (hr : r₁ ≤ r₀)
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2) (F : ReversibleMetric n) (B : ℝ)

local instance : CompactSpace (CompactNearJoinParameters.tube α β R) :=
  isCompact_iff_compactSpace.mp (CompactNearJoinParameters.compact α β R)

def fromInterior :
    TopCat.of (FirstHalfInteriorFamily.filteredDomain
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B) ⟶
      TopCat.of (FirstInputRotationFilteredCap.domain α β R r₀ hR hr₀ F B) := by
  refine TopCat.ofHom ⟨fun z => ⟨(1,
    FirstInputRotationNativeDomain.toProper α β R r₀ r₁ hR hr a ha ha1 z.val), ?_⟩, ?_⟩
  · change SobolevLength.length F (FirstInputRotatingFixedOutput.output α β R r₀ hR hr₀
      (FirstInputRotationNativeDomain.toProper α β R r₀ r₁ hR hr a ha ha1 z.val)) < B
    rw [← FirstInputRotationNativeDomain.retained_eq α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1,
      FirstHalfInteriorFamily.retained_length]
    exact z.property
  · exact (continuous_const.prodMk
      ((FirstInputRotationNativeDomain.toProper α β R r₀ r₁ hR hr a ha ha1).continuous.comp
        continuous_subtype_val)).subtype_mk _

theorem fromInterior_retained :
    fromInterior α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B ≫
      FirstInputRotationFilteredCap.retained α β R r₀ hR hr₀ F B =
      TopCat.ofHom (FirstHalfInteriorPrism.endpoint
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B 1) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact (FirstInputRotationNativeDomain.retained_eq α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 z.val).symm

def boundedMap :
    FirstHalfBoundedCapDeformation.boundedCut
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B ⟶
      TopCat.of (FirstInputRotationFilteredCap.domain α β R r₀ hR hr₀ F B) :=
  FirstHalfBoundedCapDeformation.toInterior
    (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B ≫
      fromInterior α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B

theorem retained_square :
    boundedMap α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B ≫
      FirstInputRotationFilteredCap.retained α β R r₀ hR hr₀ F B =
      FirstHalfBoundedCapDeformation.endpoint
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B 1 := by
  rw [boundedMap, Category.assoc, fromInterior_retained]
  rfl

theorem source_square :
    boundedMap α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B ≫
      FirstInputRotationTimeCap.source α β R r₀ hR hr₀ F B =
      FirstHalfAnnularTimeInputs.projection
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B ≫
          (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

end
end Finsler.FirstInputRotationNativeBounded
