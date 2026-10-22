module

public import Finsler.Loop.LocalizedSupportedCapComparison
public import Finsler.Loop.CompactJoinCapLocalization
public import Finsler.Loop.StrictLengthProductFamilies

/-! The actual normalized rectangle-localized join cap, after a genuine
closed-tube to open-tube inclusion, equals the specified diagonal Thom
cut in that open tube's homology. Comparison uses real common covers and
a far-supported primitive; no filtered homology injectivity is assumed. -/

@[expose] public section
namespace Finsler.CompactNormalizedJoinCapComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))

def far (ρ : ℝ) : Set (TopCat.of (P × Q)) := {z | ρ < dist (basepoint (α z.1)) (basepoint (β z.2))}
def near (S : ℝ) : Set (TopCat.of (P × Q)) := {z | dist (basepoint (α z.1)) (basepoint (β z.2)) < S}

theorem far_open (ρ : ℝ) : IsOpen (far α β ρ) :=
  isOpen_lt continuous_const
    ((H1AlignmentHomotopy.basepoint_continuous.comp (α.continuous.comp continuous_fst)).dist
      (H1AlignmentHomotopy.basepoint_continuous.comp (β.continuous.comp continuous_snd)))

theorem near_open (S : ℝ) : IsOpen (near α β S) :=
  isOpen_lt
    ((H1AlignmentHomotopy.basepoint_continuous.comp (α.continuous.comp continuous_fst)).dist
      (H1AlignmentHomotopy.basepoint_continuous.comp (β.continuous.comp continuous_snd))) continuous_const

variable {ρ : ℝ} (hρ : 0 < ρ) (R S : ℝ) (hρR : 2 * ρ ≤ R) (hRS : R < S)

include hρ hρR hRS in
theorem covers : far α β ρ ∪ near α β S = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  change ρ < dist (basepoint (α z.1)) (basepoint (β z.2)) ∨ dist (basepoint (α z.1)) (basepoint (β z.2)) < S
  by_cases hz : ρ < dist (basepoint (α z.1)) (basepoint (β z.2))
  · exact Or.inl hz
  · exact Or.inr (by linarith [not_lt.mp hz])

theorem far_maps : Set.MapsTo (DiagonalPullbackCut.pairEvaluation
    (StrictLengthProductFamilies.leftEvaluation α (Q := Q)) (StrictLengthProductFamilies.rightEvaluation β (P := P)))
    (far α β ρ) (DiagonalAvoidanceCocycle.far (m + 1) ρ) := by
  intro z hz
  change ρ ≤ ‖basepoint (β z.2) - basepoint (α z.1)‖
  have he : ρ < dist (basepoint (α z.1)) (basepoint (β z.2)) := hz
  simpa only [dist_eq_norm, norm_sub_rev] using he.le

def toNear : TopCat.of (CompactNearJoinParameters.tube α β R) ⟶ TopCat.of (near α β S) :=
  TopCat.ofHom ⟨fun z => ⟨z.val, z.property.trans_lt hRS⟩, continuous_subtype_val.subtype_mk _⟩

theorem toNear_source : toNear α β R S hRS ≫ SupportedCap.subspaceMap (TopCat.of (P × Q)) (near α β S) =
    SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R) := rfl

theorem cocycle_eq : FarNormalizedDiagonalCap.cocycle m
    (StrictLengthProductFamilies.leftEvaluation α (Q := Q)) (StrictLengthProductFamilies.rightEvaluation β (P := P)) hρ =
    CompactJoinCocycle.cocycle α β (dim_pos m) hρ := rfl

def localized := (CompactJoinCapLocalization.localized α β (dim_pos m) hρ hρR).post (push (toNear α β R S hRS))

theorem source (q : ℕ) : (localized α β hρ R S hρR hRS).component q ≫
    (push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (near α β S))).f q =
    (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β ρ)).f ((m + 1) + q) ≫
      RelativeCapAssociativity.absoluteChain (TopCat.of (P × Q)) (m + 1) q ((m + 1) + q) rfl
        (FarNormalizedDiagonalCap.cocycle m (StrictLengthProductFamilies.leftEvaluation α)
          (StrictLengthProductFamilies.rightEvaluation β) hρ) := by
  have hj : push (toNear α β R S hRS) ≫ push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (near α β S)) =
      push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R)) := by
    rw [← push_comp, toNear_source]
  change ((CompactJoinCapLocalization.localized α β (dim_pos m) hρ hρR).component q ≫
    (push (toNear α β R S hRS)).f q) ≫ _ = _
  rw [Category.assoc, ← HomologicalComplex.comp_f, hj, cocycle_eq]
  exact CompactJoinCapLocalization.source α β (dim_pos m) hρ hρR q

def unrefined := (localized α β hρ R S hρR hRS).pre
  (smallSingularRetraction (X := TopCat.of (P × Q)) coeff (CompactJoinCapLocalization.cover α β ρ)
    (CompactJoinCapLocalization.cover_open α β ρ) (CompactJoinCapLocalization.cover_univ α β hρ))

theorem existing_unrefined (q : ℕ) :
    ((CompactJoinCapLocalization.unrefined α β (dim_pos m) hρ hρR).post (push (toNear α β R S hRS))).homology q =
    (unrefined α β hρ R S hρR hRS).homology q := by
  rw [DegreeLoweringHomology.Map.post_homology, CompactJoinCapLocalization.unrefined,
    DegreeLoweringHomology.Map.pre_homology, unrefined, DegreeLoweringHomology.Map.pre_homology,
    localized, DegreeLoweringHomology.Map.post_homology, Category.assoc]

theorem normalized_homology (q : ℕ) : (unrefined α β hρ R S hρR hRS).homology q =
    (FarNormalizedDiagonalCap.operation m (StrictLengthProductFamilies.leftEvaluation α)
      (StrictLengthProductFamilies.rightEvaluation β) hρ (far α β ρ) (near α β S)
      (far_open α β ρ) (near_open α β S) (covers α β hρ R S hρR hRS) (far_maps α β)).homology q := by
  exact LocalizedSupportedCapComparison.homology_eq (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β ρ)
    (far α β ρ) (near α β S) (far_open α β ρ) (near_open α β S) (covers α β hρ R S hρR hRS)
    (m + 1) _ (FarNormalizedDiagonalCap.cocycle_supported m _ _ hρ _ (far_maps α β))
    (FarNormalizedDiagonalCap.cocycle_closed m _ _ hρ) (localized α β hρ R S hρR hRS)
    (source α β hρ R S hρR hRS) (CompactJoinCapLocalization.cover_open α β ρ)
    (CompactJoinCapLocalization.cover_univ α β hρ) q

theorem specified_homology (hm : 1 ≤ m) (hρ2 : ρ ≤ 2) (q : ℕ) :
    (unrefined α β hρ R S hρR hRS).homology q =
    (DiagonalCutNaturality.operation (dim_pos m) (StrictLengthProductFamilies.leftEvaluation α)
      (StrictLengthProductFamilies.rightEvaluation β) (near α β S) (near_open α β S)
      (FarDiagonalCutComparison.diagonal_in_near m _ _ hρ (far α β ρ) (near α β S)
        (covers α β hρ R S hρR hRS) (far_maps α β))).homology q := by
  rw [normalized_homology]
  exact FarDiagonalCutComparison.normalized_homology m _ _ hρ (far α β ρ) (near α β S)
    (far_open α β ρ) (near_open α β S) (covers α β hρ R S hρR hRS) (far_maps α β) hm hρ2 q

end
end Finsler.CompactNormalizedJoinCapComparison
