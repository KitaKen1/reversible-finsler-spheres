module

public import Finsler.Topology.FixedAmbientNormalize
public import Finsler.Topology.PolyPieces
public import Finsler.Topology.StripK

/-! inclusion of unit polygons in the ambient crossing pairs,
including the half-fixed parts, in the direction needed to compare ambient lenses to loops. -/

@[expose] public section

namespace Finsler.AmbientInclusionK

open CategoryTheory Set Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonDescent
open Finsler.AmbientPenalty Finsler.AmbientK Finsler.AmbientNormalizeK Finsler.SampleK
open Finsler.FixedSampleK Finsler.FixedAmbientNormalize Finsler.InvPairs Finsler.FlowLens
open Finsler.LensFamily Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.BorelDeformation Finsler.BorelIterate Finsler.BorelComparison
open Finsler.BorelLens Finsler.StripK Finsler.PolyPieces
open Finsler.OrbitAssembly Finsler.BorelCrossingK Finsler.BorelFixed
open Finsler.FixedLadder Finsler.CutPotential Finsler.AvoidPoint
open Finsler.LocalCoverK

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- An actual section of a cohomology isomorphism is its inverse, so no new homotopy is needed. -/
theorem nativePull_section_bijective {P Q : TopPair.{0}} (f : P ⟶ Q) (i : Q ⟶ P)
    (hif : i ≫ f = 𝟙 Q) (q : ℕ) (hf : Function.Bijective (nativePull f q)) :
    Function.Bijective (nativePull i q) := by
  have hi : ∀ x, nativePull i q (nativePull f q x) = x := by
    intro x
    rw [← nativePull_comp, hif, nativePull_id]
  constructor
  · intro x y hxy
    obtain ⟨x', rfl⟩ := hf.2 x
    obtain ⟨y', rfl⟩ := hf.2 y
    rw [hi, hi] at hxy
    exact congrArg (nativePull f q) hxy
  · exact fun y => ⟨nativePull f q y, hi y⟩

def equivPairHom {X Y : TopCat.{0}} (kX : KAct X) (kY : KAct Y)
    {s t : Set X} {s' t' : Set Y} (hst : s ⊆ t) (hs : Inv kX s) (ht : Inv kX t)
    (hst' : s' ⊆ t') (hs' : Inv kY s') (ht' : Inv kY t') (f : pairOf hst ⟶ pairOf hst')
    (hρ : f ≫ restrictPair kY.ρ hst' hs'.ρ_mem ht'.ρ_mem =
      restrictPair kX.ρ hst hs.ρ_mem ht.ρ_mem ≫ f)
    (hσ : f ≫ restrictPair kY.σ hst' hs'.σ_mem ht'.σ_mem =
      restrictPair kX.σ hst hs.σ_mem ht.σ_mem ≫ f) :
    CommHom (gCommuting kY hst' hs' ht') (gCommuting kX hst hs ht) :=
  BorelInvariance.commHom
    (restrictPair_sq kX.ρ kX.ρρ _ hs.ρ_mem ht.ρ_mem)
    (restrictPair_sq kY.ρ kY.ρρ _ hs'.ρ_mem ht'.ρ_mem) f hρ
    (restrictPair_sq kX.σ kX.σσ _ hs.σ_mem ht.σ_mem)
    (restrictPair_sq kY.σ kY.σσ _ hs'.σ_mem ht'.σ_mem)
    (restrictPair_comm kX.ρ kX.σ kX.ρσ _ hs.ρ_mem ht.ρ_mem hs.σ_mem ht.σ_mem)
    (restrictPair_comm kY.ρ kY.σ kY.ρσ _ hs'.ρ_mem ht'.ρ_mem hs'.σ_mem ht'.σ_mem) hσ

variable {n : ℕ} (M : ℕ) [NeZero M] (F : ReversibleMetric n) {lam : ℝ}

def inclEnergyPair (lam : ℝ) {a b : ℝ} (hab : a ≤ b) :
    pairOf (sub_mono (energy F (2 * M)) hab) ⟶ pairOf (sub_mono (penW F (2 * M) lam) hab) :=
  pairMapX _ _ (inclMap F lam b) fun q hq => lt_of_eq_of_lt (penW_incl F lam q.1) hq

theorem incl_normalize (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) :
    inclEnergyPair M F lam hab ≫ normalizePair M F hlam hab =
      𝟙 (pairOf (sub_mono (energy F (2 * M)) hab)) := by
  ext q <;> exact Subtype.ext (normalizeP_incl q.1)

theorem incl_native_bijective (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    Function.Bijective (nativePull (inclEnergyPair M F lam hab) q) :=
  nativePull_section_bijective (normalizePair M F hlam hab) (inclEnergyPair M F lam hab)
    (incl_normalize M F hlam hab) q (Finsler.LensK.nativePull_bijective_of_Hmap _ q
      (normalize_bijective F hlam hab q))

def inclEnergyHom (lam : ℝ) {a b : ℝ} (hab : a ≤ b) : CommHom
    (gCommuting (ambK M) (sub_mono (penW F (2 * M) lam) hab)
      (inv_subAmbient M F a) (inv_subAmbient M F b))
    (gCommuting (kPoly n M) (sub_mono (energy F (2 * M)) hab)
      (inv_subPoly (F := F) a) (inv_subPoly (F := F) b)) :=
  equivPairHom (kPoly n M) (ambK M) _ _ _ _ _ _ (inclEnergyPair M F lam hab)
    (by ext q <;> rfl) (by ext q <;> rfl)

theorem HK_incl_bijective (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    Function.Bijective (HRmap (borelHom (inclEnergyHom M F lam hab)) q) :=
  BorelInvariance.bijective_iterated _ _ (inclEnergyPair M F lam hab) (by ext q <;> rfl)
    _ _ _ _ (by ext q <;> rfl) (incl_native_bijective M F hlam hab) q

theorem HR_incl_bijective (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    Function.Bijective (HRmap (inclEnergyHom M F lam hab).φ q) :=
  BorelInvariance.bijective_HRmap _ _ (inclEnergyPair M F lam hab)
    (by ext q <;> rfl) (incl_native_bijective M F hlam hab) q

def inclFixedPair (lam : ℝ) {a b : ℝ} (hab : a ≤ b) :
    pairOf (inter_subset_inter_left (fixP n M) (sub_mono (energy F (2 * M)) hab)) ⟶
      pairOf (inter_subset_inter_left (fixOm M) (sub_mono (penW F (2 * M) lam) hab)) :=
  pairMapX _ _ (inclFix M F lam b) fun q hq =>
    ⟨lt_of_eq_of_lt (penW_incl F lam q.1) hq.1, incl_fixed M hq.2⟩

theorem inclFixed_normalize (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) :
    inclFixedPair M F lam hab ≫ normalizeFixPair M F hlam hab =
      𝟙 (pairOf (inter_subset_inter_left (fixP n M) (sub_mono (energy F (2 * M)) hab))) := by
  ext q <;> exact Subtype.ext (normalizeP_incl q.1)

theorem inclFixed_native_bijective (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    Function.Bijective (nativePull (inclFixedPair M F lam hab) q) :=
  nativePull_section_bijective (normalizeFixPair M F hlam hab) (inclFixedPair M F lam hab)
    (inclFixed_normalize M F hlam hab) q (Finsler.LensK.nativePull_bijective_of_Hmap _ q
      (normalizeFix_bijective M F hlam hab q))

def inclFixedHom (lam : ℝ) {a b : ℝ} (hab : a ≤ b) : CommHom
    (gCommuting (ambK M) (inter_subset_inter_left (fixOm M) (sub_mono (penW F (2 * M) lam) hab))
      (inv_fixSubOm M F a) (inv_fixSubOm M F b))
    (gCommuting (kPoly n M) (inter_subset_inter_left (fixP n M) (sub_mono (energy F (2 * M)) hab))
      (inv_fixSub (F := F) a) (inv_fixSub (F := F) b)) :=
  equivPairHom (kPoly n M) (ambK M) _ _ _ _ _ _ (inclFixedPair M F lam hab)
    (by ext q <;> rfl) (by ext q <;> rfl)

theorem HK_inclFixed_bijective (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    Function.Bijective (HRmap (borelHom (inclFixedHom M F lam hab)) q) :=
  BorelInvariance.bijective_iterated _ _ (inclFixedPair M F lam hab) (by ext q <;> rfl)
    _ _ _ _ (by ext q <;> rfl) (inclFixed_native_bijective M F hlam hab) q

theorem HR_inclFixed_bijective (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    Function.Bijective (HRmap (inclFixedHom M F lam hab).φ q) :=
  BorelInvariance.bijective_HRmap _ _ (inclFixedPair M F lam hab)
    (by ext q <;> rfl) (inclFixed_native_bijective M F hlam hab) q

theorem incl_restriction_square (lam : ℝ) {a b : ℝ} (hab : a ≤ b) :
    inclFixedPair M F lam hab ≫
      inclPair (inter_subset_inter_left (fixOm M) (sub_mono (penW F (2 * M) lam) hab))
        (sub_mono (penW F (2 * M) lam) hab) inter_subset_left inter_subset_left =
    inclPair (inter_subset_inter_left (fixP n M) (sub_mono (energy F (2 * M)) hab))
        (sub_mono (energy F (2 * M)) hab) inter_subset_left inter_subset_left ≫
      inclEnergyPair M F lam hab := by
  ext q <;> rfl

abbrev ambientRestriction (lam : ℝ) {a b : ℝ} (hab : a ≤ b) :=
  gHom (ambK M) (inter_subset_inter_left (fixOm M) (sub_mono (penW F (2 * M) lam) hab))
    (inv_fixSubOm M F a) (inv_fixSubOm M F b) (sub_mono (penW F (2 * M) lam) hab)
    (inv_subAmbient M F a) (inv_subAmbient M F b) inter_subset_left inter_subset_left

abbrev toCross (lam : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :=
  commComp (inclEnergyHom M F lam (pow_le_pow_left₀ ha.le hab 2))
    (sampleHom (F := F) (M := M) ha hab)

abbrev toFixCross (lam : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :=
  commComp (inclFixedHom M F lam (pow_le_pow_left₀ ha.le hab 2))
    (sampleFixHom (F := F) (M := M) ha hab)

theorem sample_square (lam : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    inclPair (fixLev_mono F hab) (lev_mono F hab) (fixLev_subset_lev F a) (fixLev_subset_lev F b) ≫
      samplePair (M := M) ha hab ≫ inclEnergyPair M F lam (pow_le_pow_left₀ ha.le hab 2) =
    samplePairFix (M := M) ha hab ≫ inclFixedPair M F lam (pow_le_pow_left₀ ha.le hab 2) ≫
      inclPair (inter_subset_inter_left (fixOm M)
        (sub_mono (penW F (2 * M) lam) (pow_le_pow_left₀ ha.le hab 2)))
        (sub_mono (penW F (2 * M) lam) (pow_le_pow_left₀ ha.le hab 2))
        inter_subset_left inter_subset_left := by
  ext q <;> rfl

theorem toCross_comm (lam : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (i : ℕ)
    (x : (cochains (pairOf (sub_mono (penW F (2 * M) lam)
      (pow_le_pow_left₀ ha.le hab 2)))).X i) :
    (crossHom F hab).φ.f i ((toCross M F lam ha hab).φ.f i x) =
      (toFixCross M F lam ha hab).φ.f i
        ((ambientRestriction M F lam (pow_le_pow_left₀ ha.le hab 2)).φ.f i x) := by
  exact pull_comp3 _ _ _ _ _ _ (sample_square M F lam ha hab) i x

theorem toCross_bijective (hlam : 0 ≤ lam) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (q : ℕ)
    (hs : Function.Bijective (HRmap (borelHom (sampleHom (F := F) (M := M) ha hab)) q)) :
    Function.Bijective (HRmap (borelHom (toCross M F lam ha hab)) q) :=
  HK_commComp_bijective _ _ q (HK_incl_bijective M F hlam (pow_le_pow_left₀ ha.le hab 2) q) hs

theorem toFixCross_bijective (hlam : 0 ≤ lam) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (q : ℕ)
    (hs : Function.Bijective (HRmap (borelHom (sampleFixHom (F := F) (M := M) ha hab)) q)) :
    Function.Bijective (HRmap (borelHom (toFixCross M F lam ha hab)) q) :=
  HK_commComp_bijective _ _ q (HK_inclFixed_bijective M F hlam (pow_le_pow_left₀ ha.le hab 2) q) hs

theorem toFixCross_bijective_R (hlam : 0 ≤ lam) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (q : ℕ)
    (hs : Function.Bijective (HRmap (sampleFixHom (F := F) (M := M) ha hab).φ q)) :
    Function.Bijective (HRmap (toFixCross M F lam ha hab).φ q) :=
  HR_commComp_bijective _ _ q (HR_inclFixed_bijective M F hlam (pow_le_pow_left₀ ha.le hab 2) q) hs

end

end Finsler.AmbientInclusionK
