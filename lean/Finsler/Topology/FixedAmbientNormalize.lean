module

public import Finsler.Topology.AmbientNormalizeK
public import Finsler.Topology.FixedSampleK

/-! normalization on the half-fixed ambient polygons and its
compatibility with the actual pair restrictions. -/

@[expose] public section

namespace Finsler.FixedAmbientNormalize

open CategoryTheory Set Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonDescent
open Finsler.AmbientPenalty Finsler.AmbientK Finsler.AmbientNormalizeK Finsler.SampleK
open Finsler.FixedSampleK Finsler.InvPairs Finsler.FlowLens Finsler.LensFamily
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.BorelDeformation
open Finsler.BorelIterate

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (M : ℕ) [NeZero M]

def fixOm : Set (Om n (2 * M)) := {Q | (ambK M).σ Q = Q}

theorem fixOm_invariant : Inv (ambK M) (fixOm (n := n) M) where
  ρ_mem Q hQ := by
    change (ambK M).σ ((ambK M).ρ Q) = (ambK M).ρ Q
    rw [← (ambK M).ρσ, hQ]
  σ_mem Q hQ := by
    change (ambK M).σ ((ambK M).σ Q) = (ambK M).σ Q
    rw [hQ, hQ]

theorem normalize_fixed {Q : Om n (2 * M)} (hQ : Q ∈ fixOm M) :
    normalizeP Q ∈ fixP n M := by
  change (kPoly n M).σ (normalizeP Q) = normalizeP Q
  rw [← normalize_σ]
  exact congrArg normalizeP hQ

theorem incl_fixed {q : Poly n (2 * M)} (hq : q ∈ fixP n M) : incl q ∈ fixOm M := by
  change (ambK M).σ (incl q) = incl q
  rw [← incl_σ]
  exact congrArg incl hq

theorem scal_fixed (t : ℝ) {Q : Om n (2 * M)} (hQ : Q ∈ fixOm M) : scal t Q ∈ fixOm M := by
  change (ambK M).σ (scal t Q) = scal t Q
  rw [← scal_σ]
  exact congrArg (scal t) hQ

variable (F : ReversibleMetric n) {lam : ℝ}

abbrev fixSubOm (c : ℝ) : Set (Om n (2 * M)) := sub (penW F (2 * M) lam) c ∩ fixOm M

def normalizeFix (hlam : 0 ≤ lam) (b : ℝ) : C(fixSubOm M F (lam := lam) b, fixSub F M b) :=
  ⟨fun Q => ⟨normalizeP Q.1, lt_of_le_of_lt (energy_le_penW F hlam Q.1) Q.2.1,
      normalize_fixed M Q.2.2⟩,
    (normalizeP.continuous.comp continuous_subtype_val).subtype_mk _⟩

def inclFix (lam b : ℝ) : C(fixSub F M b, fixSubOm M F (lam := lam) b) :=
  ⟨fun q => ⟨incl q.1, lt_of_eq_of_lt (penW_incl F lam q.1) q.2.1, incl_fixed M q.2.2⟩,
    (incl.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem normalize_inclFix (hlam : 0 ≤ lam) (b : ℝ) :
    (normalizeFix M F hlam b).comp (inclFix M F lam b) = ContinuousMap.id (fixSub F M b) :=
  ContinuousMap.ext fun q => Subtype.ext (normalizeP_incl q.1)

def scalFixHomotopy (hlam : 0 ≤ lam) (b : ℝ) :
    ((inclFix M F lam b).comp (normalizeFix M F hlam b)).Homotopy
      (ContinuousMap.id (fixSubOm M F (lam := lam) b)) where
  toFun p := ⟨scal (p.1 : ℝ) p.2.1,
    lt_of_le_of_lt (penW_scal_le F hlam p.1.2.1 p.1.2.2 p.2.1) p.2.2.1,
    scal_fixed M _ p.2.2.2⟩
  continuous_toFun := (scal_continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left Q := Subtype.ext (by
    change scal ((0 : unitInterval) : ℝ) Q.1 = incl (normalizeP Q.1)
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, scal_zero])
  map_one_left Q := Subtype.ext (by
    change scal ((1 : unitInterval) : ℝ) Q.1 = Q.1
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, scal_one])

def normalizeFixPair (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) :
    pairOf (inter_subset_inter_left (fixOm M) (sub_mono (penW F (2 * M) lam) hab)) ⟶
      pairOf (inter_subset_inter_left (fixP n M) (sub_mono (energy F (2 * M)) hab)) :=
  pairMapX _ _ (normalizeFix M F hlam b) fun Q hQ =>
    ⟨lt_of_le_of_lt (energy_le_penW F hlam Q.1) hQ.1, normalize_fixed M hQ.2⟩

theorem normalizeFix_bijective (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    Function.Bijective (Hmap (trivHom (normalizeFixPair M F hlam hab)) q) := by
  refine bijective_Hmap_of_section _ _ (normalizeFix M F hlam b) (inclFix M F lam b) _ ?_
    (normalize_inclFix M F hlam b) (scalFixHomotopy M F hlam b) ?_ q
  · intro q hq
    exact ⟨lt_of_eq_of_lt (penW_incl F lam q.1) hq.1, incl_fixed M hq.2⟩
  · intro τ Q hQ
    exact ⟨lt_of_le_of_lt (penW_scal_le F hlam τ.2.1 τ.2.2 Q.1) hQ.1, scal_fixed M _ hQ.2⟩

theorem normalize_restriction_square (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) :
    normalizeFixPair M F hlam hab ≫
      inclPair (inter_subset_inter_left (fixP n M) (sub_mono (energy F (2 * M)) hab))
        (sub_mono (energy F (2 * M)) hab) inter_subset_left inter_subset_left =
    inclPair (inter_subset_inter_left (fixOm M) (sub_mono (penW F (2 * M) lam) hab))
        (sub_mono (penW F (2 * M) lam) hab) inter_subset_left inter_subset_left ≫
      normalizePair M F hlam hab := by
  ext Q <;> rfl

theorem inv_fixSubOm (c : ℝ) : Inv (ambK M) (fixSubOm M F (lam := lam) c) :=
  inv_inter (inv_subAmbient M F c) (fixOm_invariant M)

theorem normalizeFixPair_ρ (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) :
    normalizeFixPair M F hlam hab ≫ restrictPair (kPoly n M).ρ
      (inter_subset_inter_left (fixP n M) (sub_mono (energy F (2 * M)) hab))
      (inv_fixSub (F := F) (M := M) a).ρ_mem (inv_fixSub (F := F) (M := M) b).ρ_mem =
    restrictPair (ambK M).ρ
      (inter_subset_inter_left (fixOm M) (sub_mono (penW F (2 * M) lam) hab))
      (inv_fixSubOm M F a).ρ_mem (inv_fixSubOm M F b).ρ_mem ≫ normalizeFixPair M F hlam hab := by
  ext Q
  · exact Subtype.ext (normalize_ρ M Q.1)
  · exact Subtype.ext (normalize_ρ M Q.1)

theorem normalizeFixPair_σ (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) :
    normalizeFixPair M F hlam hab ≫ restrictPair (kPoly n M).σ
      (inter_subset_inter_left (fixP n M) (sub_mono (energy F (2 * M)) hab))
      (inv_fixSub (F := F) (M := M) a).σ_mem (inv_fixSub (F := F) (M := M) b).σ_mem =
    restrictPair (ambK M).σ
      (inter_subset_inter_left (fixOm M) (sub_mono (penW F (2 * M) lam) hab))
      (inv_fixSubOm M F a).σ_mem (inv_fixSubOm M F b).σ_mem ≫ normalizeFixPair M F hlam hab := by
  ext Q
  · exact Subtype.ext (normalize_σ M Q.1)
  · exact Subtype.ext (normalize_σ M Q.1)

def normalizeFixHom (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) :
    CommHom
      (gCommuting (kPoly n M) (inter_subset_inter_left (fixP n M) (sub_mono (energy F (2 * M)) hab))
        (inv_fixSub (F := F) (M := M) a) (inv_fixSub (F := F) (M := M) b))
      (gCommuting (ambK M) (inter_subset_inter_left (fixOm M) (sub_mono (penW F (2 * M) lam) hab))
        (inv_fixSubOm M F a) (inv_fixSubOm M F b)) :=
  BorelInvariance.commHom
    (restrictPair_sq (ambK M).ρ (ambK M).ρρ _
      (inv_fixSubOm M F a).ρ_mem (inv_fixSubOm M F b).ρ_mem)
    (restrictPair_sq (kPoly n M).ρ (kPoly n M).ρρ _
      (inv_fixSub (F := F) (M := M) a).ρ_mem (inv_fixSub (F := F) (M := M) b).ρ_mem)
    (normalizeFixPair M F hlam hab) (normalizeFixPair_ρ M F hlam hab)
    (restrictPair_sq (ambK M).σ (ambK M).σσ _
      (inv_fixSubOm M F a).σ_mem (inv_fixSubOm M F b).σ_mem)
    (restrictPair_sq (kPoly n M).σ (kPoly n M).σσ _
      (inv_fixSub (F := F) (M := M) a).σ_mem (inv_fixSub (F := F) (M := M) b).σ_mem)
    (restrictPair_comm (ambK M).ρ (ambK M).σ (ambK M).ρσ _
      (inv_fixSubOm M F a).ρ_mem (inv_fixSubOm M F b).ρ_mem
      (inv_fixSubOm M F a).σ_mem (inv_fixSubOm M F b).σ_mem)
    (restrictPair_comm (kPoly n M).ρ (kPoly n M).σ (kPoly n M).ρσ _
      (inv_fixSub (F := F) (M := M) a).ρ_mem (inv_fixSub (F := F) (M := M) b).ρ_mem
      (inv_fixSub (F := F) (M := M) a).σ_mem (inv_fixSub (F := F) (M := M) b).σ_mem)
    (normalizeFixPair_σ M F hlam hab)

theorem HK_normalizeFix_bijective (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    Function.Bijective (HRmap (borelHom (normalizeFixHom M F hlam hab)) q) := by
  exact BorelInvariance.bijective_iterated _ _ _ _ _ _ _ _ _
    (fun j => Finsler.LensK.nativePull_bijective_of_Hmap _ j
      (normalizeFix_bijective M F hlam hab j)) q

theorem HR_normalizeFix_bijective (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    Function.Bijective (HRmap (normalizeFixHom M F hlam hab).φ q) := by
  exact BorelInvariance.bijective_HRmap _ _ (normalizeFixPair M F hlam hab)
    (normalizeFixPair_ρ M F hlam hab)
    (fun j => Finsler.LensK.nativePull_bijective_of_Hmap _ j
      (normalizeFix_bijective M F hlam hab j)) q

end

end Finsler.FixedAmbientNormalize
