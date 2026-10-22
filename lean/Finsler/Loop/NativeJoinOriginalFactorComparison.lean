module

public import Finsler.Loop.NativeJoinOriginalTimeComparison
public import Finsler.Loop.DegreeRegradedHomology
import all Finsler.Topology.OriginalSecondHalfTimeOperation

/-! Compare the genuine native join-first retained operation with
any actual original factor-cover bounded cap on the same tube.
All-input homology equality preserves the exact length sublevel. -/

@[expose] public section
namespace Finsler.NativeJoinOriginalFactorComparison

open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R : ℝ) (hR : R < 1)
  (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric (m + 1)) (B η σ κ : ℝ)
  (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hη : 0 < η) (hσ : 0 < σ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
    (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X ((m + 1) + (p + q)) ⟶
      (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded
        (CompactNearJoinParameters.inputs α β R hR) hr F B))).X q)
  (hc : ∀ q, c (q + 1) ≫ (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded
      (CompactNearJoinParameters.inputs α β R hR) hr F B))).d (q + 1) q =
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q)

variable (w : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
    (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded
      (CompactNearJoinParameters.inputs α β R hR) hr F B))) (m + p))
  (hw : ∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
    ClosedCapDegreeTransport.align m p
      (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
        (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη) _ m p c) q)

variable (hi : CommonOriginalTimeOperation.NativeSource α β R hR r hr F B η h p T c)
  (u : DegreeLoweringHomology.Map
    (small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.oldCover α β σ κ))
    (chains (TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B))) ((m + 1) + (m + 1) + p))
  (hu : OriginalTimeCapRefinement.Source α β (OriginalSecondHalfCompactTube.tube α β R)
    (OriginalSecondHalfCompactTube.near α β R hR) r hr F B h (m + 1) p
    (CompactJoinCocycle.timeCocycle α β (by omega) hκ) T (OriginalNativeCommonCover.oldCover α β σ κ) u)

def original : DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
    (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) ((m + 1) + (m + p)) :=
  DegreeLoweringRegrade.regrade
    (OriginalSecondHalfTimeOperation.output α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B
      (OriginalNativeCommonCover.oldCover α β σ κ) (OriginalNativeCommonCover.oldCover_open α β σ κ)
      (OriginalNativeCommonCover.oldCover_univ α β σ κ hσ hκ) h (m + 1) p
      (CompactJoinCocycle.timeCocycle α β (by omega) hκ) T u hu)
    ((m + 1) + (m + p)) (Nat.add_assoc (m + 1) m p).symm

include hc hw hi in
theorem homology_eq (q : ℕ) :
    (FullSecondHalfJoinTimeOperation.joined α β (by omega) hκ hκR hR hr F B (m + p) w).homology q =
      (original α β R hR r hr F B σ κ hκ hσ h p T u hu).homology q := by
  rw [NativeJoinOriginalTimeComparison.retained_homology_eq α β R hR r hr F B η σ κ hκ hκR hη hσ h p T c hc w hw hi q]
  simp only [DegreeLoweringHomology.Map.post_homology, CommonOriginalTimeNormalForm.operation,
    original, DegreeRegradedHomology.homology, OriginalSecondHalfTimeOperation.output, JoinedFilteredCap.sublevel]
  rw [CommonOriginalTimeOperation.homology_eq α β R hR r hr F B η σ κ hκ (by linarith) hη hσ h p T c hc hi u hu q]
  simp only [Category.assoc]

end
end Finsler.NativeJoinOriginalFactorComparison
