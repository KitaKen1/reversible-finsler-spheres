module

public import Finsler.Geometry.PolygonRefineIterateNullity
public import Finsler.Geometry.GeodesicShift

/-! Samples of the rotations of a closed geodesic. The facts on the polygon of K samples of a
loop which enter the refinement theorems (the polygon is short, has no zero edges, lies in the
domains of segment packages, has the twist condition, is stationary, and its broken geodesic is
the loop) hold for the rotations of a closed geodesic by all phases in [0, 1] as soon as K is
larger than a bound which does not depend on the phase: the energy is invariant under rotation
and the rotated loops have a common arc scale. The doubling theorem for the nullities of the
iterates only uses these facts for N, 2 N and 4 N samples; hence for N large and every phase
the d-fold iterates of the polygons of 4 N and of 2 N samples of the rotated closed geodesic
have the same nullity. -/

@[expose] public section

namespace Finsler.SamplePhase

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SobolevEnergy
open Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.PolygonRefine Finsler.PolygonChart Finsler.PolygonModel Finsler.SegmentAtlas
open Finsler.PolygonRefineIndex Finsler.PolygonHessian Finsler.PolygonIterate
open Finsler.PolygonIterateReduction Finsler.PolygonNullity Finsler.PolygonMonodromy
open Finsler.PolygonRefineIterate Finsler.PolygonRefineNullity Finsler.EnergySphereSmooth
open Finsler.PolygonRefineIterateNullity
open Finsler.PolygonConverse
open Finsler.SmoothSobolev Finsler.PolygonGeodesic Finsler.GeodesicArcs Finsler.GeodesicShift
open Set Filter
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n}

/-- The facts on the polygon of K samples of a loop which are used by the refinement
theorems. -/
def SampleFacts (M : SegmentData F) (u : SphereLoop n) (K : ℕ) [NeZero K] : Prop :=
  ShortPolygon M.δ (samplePoly K u) ∧
  (∀ i, samplePoly K u (i + 1) ≠ samplePoly K u i) ∧
  (∀ j : ZMod K, ∃ T : SegChart F, samplePoly K u j ∈ segDom T ∧
    ‖(samplePoly K u (j + 1) : Ambient n) - samplePoly K u j‖ < T.δ) ∧
  Twist F (samplePoly K u) ∧ PolyCritical F K (samplePoly K u) ∧
  fderiv ℝ (energy F (samplePoly K u)) (base (samplePoly K u)) = 0 ∧
  ∀ hq : ShortPolygon M.δ (samplePoly K u), polySphereLoop F M.seg hq = u

/-- **The sample facts hold for all rotations of a closed geodesic, uniformly.** There is a
bound K₀ such that for every phase in [0, 1] and every K ≥ K₀ the polygon of K samples of the
rotated closed geodesic has the sample facts. -/
theorem exists_sample_facts (M : SegmentData F) (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ K₀ : ℕ, ∀ a ∈ Icc (0 : ℝ) 1, ∀ K : ℕ, K₀ ≤ K → ∀ [NeZero K],
      SampleFacts M (ofSmooth (Finsler.Loops.shift g.loop a)) K := by
  obtain ⟨δa, hδa, ι, S, hcover, hδS, -⟩ := exists_segment_atlas F
  obtain ⟨δt, hδt, htw⟩ := PolygonTwist.exists_twist F
  obtain ⟨h₀, hh₀, hscale⟩ := exists_arc_scale_shift (F := F) g.loop
  have hδpos : 0 < min M.δ (min δa δt) := lt_min M.pos (lt_min hδa hδt)
  have hE0 : 0 ≤ energy F (ofSmooth g.loop) := energy_nonneg F _
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := min M.δ (min δa δt))
    (a := energy F (ofSmooth g.loop) + 1) hδpos
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (1 / h₀)
  refine ⟨max N₁ (N₂ + 1), fun a ha K hK _ => ?_⟩
  have hKpos := Nat.pos_of_neZero K
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hscale' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ h ∈ Ioo (0 : ℝ) h₀,
      ∃ S : SegChart F, ArcGood (shiftGeodesic g a).loop S t h := hscale a ha
  have hEu : energy F (ofSmooth (shiftGeodesic g a).loop) <
      (energy F (ofSmooth g.loop) + 1) ^ 2 := by
    rw [shiftGeodesic_loop, energy_ofSmooth_shift]
    nlinarith
  have hshort : ShortPolygon (min M.δ (min δa δt))
      (samplePoly K (ofSmooth (shiftGeodesic g a).loop)) :=
    shortPolygon_samplePoly F (fun u hu s t hs ht hst =>
      hN₁ K ((le_max_left _ _).trans hK) hKpos u hu s t hs ht hst) hEu
  have h1K : 1 / (K : ℝ) < h₀ := by
    have h2 : (N₂ : ℝ) + 1 ≤ K := by exact_mod_cast (le_max_right _ _).trans hK
    rw [div_lt_iff₀ hK']
    have h3 : 1 / h₀ < K := by linarith
    rw [div_lt_iff₀ hh₀] at h3
    linarith
  have hE := polyEnergy_ofSmooth_eq (shiftGeodesic g a) hscale' h1K
  have hne := samplePoly_ofSmooth_ne (shiftGeodesic g a) hscale' h1K
  have hsm : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < min M.δ (min δa δt) →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)) :=
    fun P Q hPQ h => M.smooth P Q hPQ (h.trans_le (min_le_left _ _))
  have hc : PolyCritical F K (samplePoly K (ofSmooth (shiftGeodesic g a).loop)) :=
    polyCritical_of_tangentCritical F hsm
      (Finsler.SobolevGeodesicCritical.tangentCritical_of_closedGeodesic F (shiftGeodesic g a))
      hshort hne hE
  have hq : ShortPolygon M.δ (samplePoly K (ofSmooth (shiftGeodesic g a).loop)) := fun i =>
    (hshort i).trans_le (min_le_left _ _)
  have hqa : ShortPolygon δa (samplePoly K (ofSmooth (shiftGeodesic g a).loop)) := fun i =>
    (hshort i).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hqt : ShortPolygon δt (samplePoly K (ofSmooth (shiftGeodesic g a).loop)) := fun i =>
    (hshort i).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨hq, hne, fun j => ?_, htw K _ hqt hne, hc,
    fderiv_energy_eq_zero_of_polyCritical F M.smooth hq hne hc,
    fun hq' => polySphereLoop_samples M.seg M.pkg (shiftGeodesic g a) hscale' h1K hq'⟩
  obtain ⟨P₀, hP₀, hP⟩ := hcover (samplePoly K (ofSmooth (shiftGeodesic g a).loop) j)
  exact ⟨S P₀, hP, (hqa j).trans_le (hδS P₀ hP₀)⟩

/-- **Doubling from the sample facts.** If the polygons of N, 2 N and 4 N samples of a loop have
the sample facts, the d-fold iterates of the polygons of 4 N and of 2 N samples have the same
nullity. -/
theorem nullity_iterate_double_of_facts (M : SegmentData F) (u : SphereLoop n) (N : ℕ) [NeZero N]
    (h₀ : SampleFacts M u N) (h₁ : SampleFacts M u (2 * N))
    (h₂ : SampleFacts M u (2 * (2 * N))) (h₄ : SampleFacts M u (4 * N)) (d : ℕ) [NeZero d] :
    nullity F (iterate d (2 * (2 * N)) (samplePoly (2 * (2 * N)) u)) =
      nullity F (iterate d (2 * N) (samplePoly (2 * N) u)) := by
  obtain ⟨hq₀, hne₀, hpk₀, -, -, hcrit₀, hbr₀⟩ := h₀
  obtain ⟨hq₁, hne₁, hpk₁, -, -, hcrit₁, hbr₁⟩ := h₁
  obtain ⟨hq₂, hne₂, -, htw₂, -, -, -⟩ := h₂
  obtain ⟨hq₄, hne₄, -, -, -, -, -⟩ := h₄
  have he₁ : refine 2 (2 * N) F M.seg hq₁ = samplePoly (2 * (2 * N)) u := by
    unfold refine
    rw [hbr₁ hq₁]
  have he₄ : refine 4 N F M.seg hq₀ = samplePoly (4 * N) u := by
    unfold refine
    rw [hbr₀ hq₀]
  have hpsd₄ : ∀ z : Model n (4 * N), (∀ i : ZMod (4 * N), i.val % 4 = 0 → z i = 0) →
      0 ≤ ⟪hessian F (samplePoly (4 * N) u) z, z⟫ := fun z hz =>
    hessian_nonneg_of_coarse M 4 N hq₀ hne₀ hpk₀ he₄ hq₄ hne₄ hcrit₀ (coarseL_eq_zero 4 N hz)
  have hpsd₂ := nonneg_congr u (show 4 * N = 2 * (2 * N) by ring) hpsd₄
  have h4 : 4 ∣ 2 * (2 * N) := ⟨N, by ring⟩
  have h := nullity_iterate_refine_two M (2 * N) hq₁ hne₁ hpk₁ (by rw [he₁]; exact hq₂)
    (by rw [he₁]; exact hne₂) hcrit₁
    (by
      rw [he₁]
      exact fun i hi a ha => Amap_pos_of_nonneg F M.smooth hq₂ hne₂ h4 htw₂ hpsd₂ hi ha) d
  rw [he₁] at h
  exact h

/-- **The nullities of the iterates of the samples of the rotations of a closed geodesic do not
change when the number of samples is doubled, uniformly in the phase.** For N large, every
phase in [0, 1] and every d ≥ 1, the d-fold iterates of the polygons of 4 N and of 2 N samples
of the rotated closed geodesic have the same nullity. -/
theorem exists_nullity_iterate_shift_double (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ N₀ : ℕ, ∀ a ∈ Icc (0 : ℝ) 1, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] (d : ℕ) [NeZero d],
      nullity F (iterate d (2 * (2 * N))
          (samplePoly (2 * (2 * N)) (ofSmooth (Finsler.Loops.shift g.loop a)))) =
        nullity F (iterate d (2 * N)
          (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) := by
  obtain ⟨M⟩ := exists_segmentData F
  obtain ⟨K₀, hK₀⟩ := exists_sample_facts M g
  refine ⟨K₀, fun a ha N hN _ d _ => ?_⟩
  have hN1 : K₀ ≤ 2 * N := hN.trans (Nat.le_mul_of_pos_left N two_pos)
  have hN2 : K₀ ≤ 2 * (2 * N) := hN1.trans (Nat.le_mul_of_pos_left (2 * N) two_pos)
  have hN4 : K₀ ≤ 4 * N := hN.trans (Nat.le_mul_of_pos_left N (by norm_num))
  exact nullity_iterate_double_of_facts M _ N (hK₀ a ha N hN) (hK₀ a ha (2 * N) hN1)
    (hK₀ a ha (2 * (2 * N)) hN2) (hK₀ a ha (4 * N) hN4) d

end

end Finsler.SamplePhase
