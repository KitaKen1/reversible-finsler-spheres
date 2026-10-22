module

public import Finsler.Topology.AmbientK

/-! Normalization, inclusion and radial homotopy commute with the actual K action. The existing ordinary normalization isomorphism and Borel comparison principle give the K-Borel isomorphism of sublevel pairs. Fixed-part restriction compatibility is separate. -/

@[expose] public section

namespace Finsler.AmbientNormalizeK

open Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientPenalty
open Finsler.AmbientK Finsler.SampleK
open CategoryTheory Set Finsler.InvPairs Finsler.BorelLoop Finsler.BorelPair Finsler.BorelCochain
open Finsler.BorelIterate Finsler.PairTriple Finsler.FlowLens Finsler.BorelDeformation Finsler.LensFamily
noncomputable section

variable {n : ℕ} (M : ℕ)

theorem normalize_ρ (Q : Om n (2 * M)) :
    normalizeP ((ambK M).ρ Q) = (kPoly n M).ρ (normalizeP Q) := rfl

theorem normalize_σ (Q : Om n (2 * M)) :
    normalizeP ((ambK M).σ Q) = (kPoly n M).σ (normalizeP Q) := rfl

theorem incl_ρ (q : Finsler.PolygonDescent.Poly n (2 * M)) :
    incl ((kPoly n M).ρ q) = (ambK M).ρ (incl q) := rfl

theorem incl_σ (q : Finsler.PolygonDescent.Poly n (2 * M)) :
    incl ((kPoly n M).σ q) = (ambK M).σ (incl q) := rfl

theorem scal_ρ (t : ℝ) (Q : Om n (2 * M)) :
    scal t ((ambK M).ρ Q) = (ambK M).ρ (scal t Q) := rfl

theorem scal_σ (t : ℝ) (Q : Om n (2 * M)) :
    scal t ((ambK M).σ Q) = (ambK M).σ (scal t Q) := rfl

variable [NeZero M] (F : ReversibleMetric n) {lam : ℝ}

theorem inv_subAmbient (c : ℝ) : Inv (ambK M) (sub (penW F (2 * M) lam) c) :=
  Finsler.LensK.inv_sub (ambK M) (pen_ρ M F lam) (pen_σ M F lam) c

def normalizePair (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) :
    pairOf (sub_mono (penW F (2 * M) lam) hab) ⟶
      pairOf (sub_mono (Finsler.PolygonDescent.energy F (2 * M)) hab) :=
  pairMapX (sub_mono (penW F (2 * M) lam) hab)
    (sub_mono (Finsler.PolygonDescent.energy F (2 * M)) hab) (normalizeMap F hlam b)
    (fun Q hQ => lt_of_le_of_lt (energy_le_penW F hlam Q.1) hQ)

theorem normalizePair_ρ (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) :
    normalizePair M F hlam hab ≫ restrictPair (kPoly n M).ρ
      (sub_mono (Finsler.PolygonDescent.energy F (2 * M)) hab)
      (inv_subPoly (F := F) (M := M) a).ρ_mem (inv_subPoly (F := F) (M := M) b).ρ_mem =
    restrictPair (ambK M).ρ (sub_mono (penW F (2 * M) lam) hab)
      (inv_subAmbient M F a).ρ_mem (inv_subAmbient M F b).ρ_mem ≫ normalizePair M F hlam hab := by
  ext Q
  · exact Subtype.ext (normalize_ρ M Q.1)
  · exact Subtype.ext (normalize_ρ M Q.1)

theorem normalizePair_σ (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) :
    normalizePair M F hlam hab ≫ restrictPair (kPoly n M).σ
      (sub_mono (Finsler.PolygonDescent.energy F (2 * M)) hab)
      (inv_subPoly (F := F) (M := M) a).σ_mem (inv_subPoly (F := F) (M := M) b).σ_mem =
    restrictPair (ambK M).σ (sub_mono (penW F (2 * M) lam) hab)
      (inv_subAmbient M F a).σ_mem (inv_subAmbient M F b).σ_mem ≫ normalizePair M F hlam hab := by
  ext Q
  · exact Subtype.ext (normalize_σ M Q.1)
  · exact Subtype.ext (normalize_σ M Q.1)

def normalizeHom (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) :
    CommHom
      (gCommuting (kPoly n M) (sub_mono (Finsler.PolygonDescent.energy F (2 * M)) hab)
        (inv_subPoly (F := F) (M := M) a) (inv_subPoly (F := F) (M := M) b))
      (gCommuting (ambK M) (sub_mono (penW F (2 * M) lam) hab)
        (inv_subAmbient M F a) (inv_subAmbient M F b)) :=
  BorelInvariance.commHom
    (restrictPair_sq (ambK M).ρ (ambK M).ρρ _
      (inv_subAmbient M F a).ρ_mem (inv_subAmbient M F b).ρ_mem)
    (restrictPair_sq (kPoly n M).ρ (kPoly n M).ρρ _
      (inv_subPoly (F := F) (M := M) a).ρ_mem (inv_subPoly (F := F) (M := M) b).ρ_mem)
    (normalizePair M F hlam hab) (normalizePair_ρ M F hlam hab)
    (restrictPair_sq (ambK M).σ (ambK M).σσ _
      (inv_subAmbient M F a).σ_mem (inv_subAmbient M F b).σ_mem)
    (restrictPair_sq (kPoly n M).σ (kPoly n M).σσ _
      (inv_subPoly (F := F) (M := M) a).σ_mem (inv_subPoly (F := F) (M := M) b).σ_mem)
    (restrictPair_comm (ambK M).ρ (ambK M).σ (ambK M).ρσ _
      (inv_subAmbient M F a).ρ_mem (inv_subAmbient M F b).ρ_mem
      (inv_subAmbient M F a).σ_mem (inv_subAmbient M F b).σ_mem)
    (restrictPair_comm (kPoly n M).ρ (kPoly n M).σ (kPoly n M).ρσ _
      (inv_subPoly (F := F) (M := M) a).ρ_mem (inv_subPoly (F := F) (M := M) b).ρ_mem
      (inv_subPoly (F := F) (M := M) a).σ_mem (inv_subPoly (F := F) (M := M) b).σ_mem)
    (normalizePair_σ M F hlam hab)

theorem HK_normalize_bijective (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    Function.Bijective (HRmap (borelHom (normalizeHom M F hlam hab)) q) := by
  exact BorelInvariance.bijective_iterated _ _ _ _ _ _ _ _ _
    (fun k => Finsler.LensK.nativePull_bijective_of_Hmap _ k
      (normalize_bijective F hlam hab k)) q

end

end Finsler.AmbientNormalizeK

