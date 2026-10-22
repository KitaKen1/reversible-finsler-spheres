module

public import Finsler.Loop.SmallHomotopyCover
public import Finsler.Loop.CoarseJoinTimeCap
public import Finsler.Loop.CompactJoinCapLocalization

/-! The actual spatial join cover pulled back to the entire original
time cylinder. Its genuine small prism, fine-cover refinement and native
near-tube cylinder source diagrams retain the full time interval. -/

@[expose] public section
namespace Finsler.WholeIntervalJoinCover

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (κ : ℝ)

theorem spatial_square : (SingularTimeCylinderMaps.cylinder (TopCat.of P) (TopCat.of Q)).h ≫
    CompactJoinCocycle.timeProjection (P := P) (Q := Q) =
      CartesianMonoidalCategory.fst (TopCat.of (P × Q)) TopCat.I := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

def cover : (P × Q) → Set (P × (ClosedInterval × Q)) :=
  SmallHomotopyCover.cover (CompactJoinCocycle.timeProjection (P := P) (Q := Q))
    (CompactJoinCapLocalization.cover α β κ)

theorem cover_open (i : P × Q) : IsOpen (cover α β κ i) :=
  SmallHomotopyCover.cover_open _ _ (CompactJoinCapLocalization.cover_open α β κ) i

theorem cover_univ (hκ : 0 < κ) : ⋃ i, cover α β κ i = Set.univ :=
  SmallHomotopyCover.cover_univ _ _ (CompactJoinCapLocalization.cover_univ α β hκ)

def prism (q : ℕ) : (small (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).X q ⟶
    (small (TopCat.of (P × (ClosedInterval × Q))) (cover α β κ)).X (q + 1) :=
  SmallHomotopyCover.prism (SingularTimeCylinderMaps.cylinder (TopCat.of P) (TopCat.of Q))
    (CompactJoinCocycle.timeProjection (P := P) (Q := Q)) (spatial_square (P := P) (Q := Q))
    (CompactJoinCapLocalization.cover α β κ) q

theorem prism_inclusion (q : ℕ) :
    (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f q ≫
      (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom q (q + 1) =
      prism α β κ q ≫ (inclusion (TopCat.of (P × (ClosedInterval × Q))) (cover α β κ)).f (q + 1) := by
  rw [← SingularTimeCylinderMaps.product_original q]
  exact SmallHomotopyCover.prism_inclusion (SingularTimeCylinderMaps.cylinder (TopCat.of P) (TopCat.of Q))
    (CompactJoinCocycle.timeProjection (P := P) (Q := Q)) (spatial_square (P := P) (Q := Q))
    (CompactJoinCapLocalization.cover α β κ) q

def refinement (R η σ : ℝ) :
    small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ) ⟶
      small (TopCat.of (P × (ClosedInterval × Q))) (cover α β κ) :=
  SmallRefinementComparison.refinement (X := TopCat.of (P × (ClosedInterval × Q)))
    (OriginalNativeCommonCover.cover α β R η σ κ) (cover α β κ)
    (fun c => (c.2.1, c.2.2.2)) (fun _ _ hz => ⟨hz.2.1.2, hz.2.2.2⟩)

theorem refinement_inclusion (R η σ : ℝ) : refinement α β κ R η σ ≫
    inclusion (TopCat.of (P × (ClosedInterval × Q))) (cover α β κ) =
      inclusion (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ) :=
  SmallRefinementComparison.refinement_inclusion (X := TopCat.of (P × (ClosedInterval × Q)))
    (OriginalNativeCommonCover.cover α β R η σ κ) (cover α β κ)
    (fun c => (c.2.1, c.2.2.2)) (fun _ _ hz => ⟨hz.2.1.2, hz.2.2.2⟩)

theorem native_prism_source (R : ℝ) (q : ℕ) :
    AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) q ≫
      (push (JoinTimeCommonRefinement.source α β R)).f (q + 1) =
      (push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R))).f q ≫
        (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom q (q + 1) := by
  let X : TopCat.{0} := TopCat.of (CompactNearJoinParameters.tube α β R)
  let j := SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R)
  let H := TopCat.Homotopy.comp (TopCat.Homotopy.refl (JoinTimeCommonRefinement.source α β R))
    (AnnularTimeTrim.cylinder X)
  let K := (SingularTimeCylinderMaps.cylinder (TopCat.of P) (TopCat.of Q)).comp (TopCat.Homotopy.refl j)
  have he : H.h = K.h := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  have hp := TimePrismNaturality.prism_post (AnnularTimeTrim.cylinder X) (JoinTimeCommonRefinement.source α β R) q
  have hc := TimePrismNaturality.prism_congr H K he q
  have hpre := TimePrismNaturality.prism_pre (SingularTimeCylinderMaps.cylinder (TopCat.of P) (TopCat.of Q)) j q
  rw [← SingularTimeCylinderMaps.product_original q]
  exact hp.trans (hc.trans hpre.symm)

end
end Finsler.WholeIntervalJoinCover
