module

public import Finsler.Loop.CompactJoinCocycle
public import Finsler.Topology.OriginalSecondHalfCompactTube
public import Finsler.Topology.JoinedTimeSplit
public import Finsler.Topology.OriginalSecondHalfTimeOperation

/-! The actual compact near-pair source for the original first-corrected
join. Its product with the time interval is literally isomorphic to
the old second-half tube, and the actual native second-half family and
join Thom cochain agree under the proved coordinate diagrams. -/

@[expose] public section
namespace Finsler.CompactNearJoinParameters

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))

def tube (R : ℝ) : Set (P × Q) :=
  {z | dist (basepoint (α z.1)) (basepoint (β z.2)) ≤ R}

theorem compact [CompactSpace P] [CompactSpace Q] (R : ℝ) : IsCompact (tube α β R) := by
  apply IsClosed.isCompact
  exact isClosed_le
    ((H1AlignmentHomotopy.basepoint_continuous.comp (α.continuous.comp continuous_fst)).dist
      (H1AlignmentHomotopy.basepoint_continuous.comp (β.continuous.comp continuous_snd))) continuous_const

def nearMap (R : ℝ) (hR : R < 1) : C(tube α β R, JoinDirectionComparison.nearPairs n) :=
  ⟨fun z => ⟨(α z.val.1, β z.val.2), z.property.trans_lt hR⟩,
    ((α.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (β.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _⟩

def inputs (R : ℝ) (hR : R < 1) : C(tube α β R, H1JoinContinuity.composable n) :=
  JoinDirectionComparison.firstPair.comp (nearMap α β R hR)

def timeMap (R : ℝ) : TopCat.of (ClosedInterval × tube α β R) ⟶
    TopCat.of (OriginalSecondHalfCompactTube.tube α β R) :=
  TopCat.ofHom ⟨fun z => ⟨(z.2.val.1, (z.1, z.2.val.2)), z.2.property⟩,
    (((continuous_fst.comp continuous_subtype_val).comp continuous_snd).prodMk
      (continuous_fst.prodMk ((continuous_snd.comp continuous_subtype_val).comp continuous_snd))).subtype_mk _⟩

def timeInv (R : ℝ) : TopCat.of (OriginalSecondHalfCompactTube.tube α β R) ⟶
    TopCat.of (ClosedInterval × tube α β R) :=
  TopCat.ofHom ⟨fun z => (z.val.2.1, ⟨(z.val.1, z.val.2.2), z.property⟩),
    (continuous_fst.comp (continuous_snd.comp continuous_subtype_val)).prodMk
      (((continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _)⟩

theorem timeMap_timeInv (R : ℝ) : timeMap α β R ≫ timeInv α β R = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem timeInv_timeMap (R : ℝ) : timeInv α β R ≫ timeMap α β R = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

def timeIso (R : ℝ) : TopCat.of (ClosedInterval × tube α β R) ≅
    TopCat.of (OriginalSecondHalfCompactTube.tube α β R) where
  hom := timeMap α β R
  inv := timeInv α β R
  hom_inv_id := timeMap_timeInv α β R
  inv_hom_id := timeInv_timeMap α β R

theorem spatial_square (R : ℝ) :
    timeMap α β R ≫ SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
      (OriginalSecondHalfCompactTube.tube α β R) ≫
        CompactJoinCocycle.timeProjection (P := P) (Q := Q) =
      CartesianMonoidalCategory.snd (TopCat.of ClosedInterval) (TopCat.of (tube α β R)) ≫
        SupportedCap.subspaceMap (TopCat.of (P × Q)) (tube α β R) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem second_family (R : ℝ) (hR : R < 1) :
    timeMap α β R ≫ OriginalSecondHalfFamily.family α β
      (OriginalSecondHalfCompactTube.tube α β R) (OriginalSecondHalfCompactTube.near α β R hR) =
        JoinedHalfCollars.secondFamily (inputs α β R hR) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem join_cochain_square (R : ℝ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (timeMap α β R ≫ SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
      (OriginalSecondHalfCompactTube.tube α β R)) n (CompactJoinCocycle.timeCocycle α β hn hρ) =
      cochainPullback (CartesianMonoidalCategory.snd (TopCat.of ClosedInterval) (TopCat.of (tube α β R))) n
        (cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × Q)) (tube α β R)) n
          (CompactJoinCocycle.cocycle α β hn hρ)) := by
  rw [CompactJoinCocycle.timeCocycle, ← pullback_comp, Category.assoc, spatial_square, pullback_comp]

theorem exists_length_tube [CompactSpace P] (F : ReversibleMetric n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R > 0, ∃ hR : R < 1, ∀ z : tube α β R,
      SobolevLength.length F (JoinedTimeSplit.loopFamily (inputs α β R hR) z) <
        SobolevLength.length F (α z.val.1) + SobolevLength.length F (β z.val.2) + ε := by
  obtain ⟨R, hR, hR1, hb⟩ := OriginalSecondHalfCompactTube.exists_length_tube F α β hε
  refine ⟨R, hR, hR1, ?_⟩
  intro z
  have hz := hb (timeMap α β R (0, z))
  exact hz

end
end Finsler.CompactNearJoinParameters
