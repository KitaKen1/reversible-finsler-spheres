module

public import Finsler.Geometry.GeodesicArcs
public import Finsler.Geometry.PolygonConverse
public import Finsler.Analysis.IntervalH1GeodesicCritical

/-! Samples of closed geodesics are critical polygons. For a closed geodesic and N large, every
arc between consecutive samples at spacing 1/N is the short segment between its ends, so the
polygon energy of the samples equals the energy, consecutive samples are distinct (a constant
segment would stop the geodesic), the samples form a short polygon, and by the abstract converse
the polygon of samples is critical. -/

@[expose] public section

namespace Finsler.PolygonGeodesic

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevEnergy Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.SegmentAtlas Finsler.SegmentContinuity Finsler.GeodesicArcs Finsler.PolygonConverse
open Finsler.SmoothSobolev Finsler.Loops Finsler.SphereCoordinateEuler
open Finsler.AmbientEnergyRegularity Finsler.ChartTransfer Finsler.SobolevOfPrimitive
open Set Filter Metric
open scoped Topology Manifold

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

theorem sampleN_ofSmooth_natCast (γ : SmoothLoop n) {N : ℕ} [NeZero N] {k : ℕ} (hk : k < N) :
    sampleN N (ofSmooth γ) (k : ZMod N) = (γ ((k : ℝ) / N) : Ambient n) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  rw [sampleN_natCast _ hk]
  exact representative_graphData γ (piece_mem_Icc' hk hN')
where
  piece_mem_Icc' {k : ℕ} (hk : k < N) (hN' : (0 : ℝ) < N) : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hN']; exact_mod_cast hk.le⟩

theorem sampleN_ofSmooth_natCast_succ (γ : SmoothLoop n) {N : ℕ} [NeZero N] {k : ℕ}
    (hk : k < N) :
    sampleN N (ofSmooth γ) ((k : ZMod N) + 1) = (γ (((k : ℝ) + 1) / N) : Ambient n) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  rw [sampleN_natCast_succ _ hk]
  exact representative_graphData γ ⟨by positivity, by rw [div_le_one hN']; exact_mod_cast hk⟩

section Geodesic

variable {F} (g : Finsler.Geodesics.ClosedGeodesic F) {h₀ : ℝ}
  (hscale : ∀ a ∈ Icc (0 : ℝ) 1, ∀ h ∈ Ioo (0 : ℝ) h₀, ∃ S : SegChart F, ArcGood g.loop S a h)

theorem coordinateEuler_of_closedGeodesic : CoordinateEuler F g.loop :=
  (Finsler.OrdinaryGeodesics.toOrdinary g).coordinateEuler

include hscale in
/-- For N large the polygon energy of the samples of a closed geodesic is its energy. -/
theorem polyEnergy_ofSmooth_eq {N : ℕ} [NeZero N] (hN : 1 / (N : ℝ) < h₀) :
    polyEnergy F N (sampleN N (ofSmooth g.loop)) = energy F (ofSmooth g.loop) := by
  have hNpos := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have he := coordinateEuler_of_closedGeodesic g
  have hpiece : ∀ k ∈ Finset.range N,
      (N : ℝ) * Finsler.SphereDistance.minEnergy F (sampleN N (ofSmooth g.loop) k)
        (sampleN N (ofSmooth g.loop) ((k : ZMod N) + 1)) =
      ∫ t in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N),
        Finsler.AmbientLagrangian.lagrangian F (Finsler.AmbientLagrangian.loopJet g.loop t) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have ha : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, by rw [div_le_one hN']; exact_mod_cast hk'.le⟩
    obtain ⟨S, hP, hQ, hsrc, hsmall⟩ := hscale _ ha (1 / N) ⟨by positivity, hN⟩
    have hE := arc_energy g.regular he S (by positivity) hP hQ hsrc hsmall
    have hend : (k : ℝ) / N + 1 / N = ((k : ℝ) + 1) / N := by ring
    rw [hend] at hE
    rw [sampleN_ofSmooth_natCast _ hk', sampleN_ofSmooth_natCast_succ _ hk', ← hE]
    push_cast
    field_simp
  have hint : ∀ k < N, IntervalIntegrable (fun t => Finsler.AmbientLagrangian.lagrangian F
      (Finsler.AmbientLagrangian.loopJet g.loop t)) MeasureTheory.volume ((k : ℝ) / N)
        (((k + 1 : ℕ) : ℝ) / N) := by
    intro k _
    have h := Finsler.LoopEnergy.density_intervalIntegrable F g.loop ((k : ℝ) / N)
      (((k + 1 : ℕ) : ℝ) / N)
    exact h.congr (fun t _ => (Finsler.EnergyConservation.density_eq F g.loop t).symm)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) / N)
    (n := N) hint
  simp only [Nat.cast_zero, zero_div, div_self hN'.ne'] at hsum
  unfold polyEnergy
  rw [Finset.mul_sum, Finset.sum_congr rfl hpiece, hsum, energy_ofSmooth]
  unfold Finsler.LoopEnergy.energy
  exact intervalIntegral.integral_congr (fun t _ => Finsler.EnergyConservation.density_eq F g.loop t)

include hscale in
/-- For N large consecutive samples of a closed geodesic are distinct. -/
theorem samplePoly_ofSmooth_ne {N : ℕ} [NeZero N] (hN : 1 / (N : ℝ) < h₀) (i : ZMod N) :
    samplePoly N (ofSmooth g.loop) (i + 1) ≠ samplePoly N (ofSmooth g.loop) i := by
  have hNpos := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have he := coordinateEuler_of_closedGeodesic g
  have hk : i.val < N := ZMod.val_lt i
  have hi : ((i.val : ℕ) : ZMod N) = i := ZMod.natCast_zmod_val i
  have ha : (i.val : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hN']; exact_mod_cast hk.le⟩
  obtain ⟨S, hP, hQ, hsrc, hsmall⟩ := hscale _ ha (1 / N) ⟨by positivity, hN⟩
  have harc := arc_eq_segCurve g.regular he S (by positivity) hP hQ hsrc hsmall
  intro heq
  have hval : g.loop ((i.val : ℝ) / N + 1 / N) = g.loop ((i.val : ℝ) / N) := by
    apply Subtype.ext
    have h1 := sampleN_ofSmooth_natCast_succ g.loop hk
    have h2 := sampleN_ofSmooth_natCast g.loop hk
    rw [hi] at h1 h2
    have h3 : sampleN N (ofSmooth g.loop) (i + 1) = sampleN N (ofSmooth g.loop) i :=
      congrArg Subtype.val heq
    rw [h1, h2] at h3
    rw [show (i.val : ℝ) / N + 1 / N = ((i.val : ℝ) + 1) / N by ring]
    exact h3
  have hconst : ∀ s ∈ Icc (0 : ℝ) 1,
      Finsler.EnergyConservation.position g.loop ((i.val : ℝ) / N + s * (1 / N)) =
        (g.loop ((i.val : ℝ) / N) : Ambient n) := by
    intro s hs
    change (g.loop ((i.val : ℝ) / N + s * (1 / N)) : Ambient n) = _
    rw [harc s hs, hval]
    unfold segCurve
    rw [chartNormalize_sphere, geo_self S.D (chart_mem_closedBall S hP)]
    exact inverseAmbient_chart_of_dom S hP
  set m : ℝ := (i.val : ℝ) / N + (1 / 2) * (1 / N) with hm
  have hev : Finsler.EnergyConservation.position g.loop =ᶠ[𝓝 m]
      fun _ => (g.loop ((i.val : ℝ) / N) : Ambient n) := by
    have hpos : (0 : ℝ) < 1 / N := by positivity
    have hlo : (i.val : ℝ) / N < m := by
      rw [hm]
      linarith
    have hhi : m < (i.val : ℝ) / N + 1 / N := by
      rw [hm]
      linarith
    filter_upwards [Ioo_mem_nhds hlo hhi] with t ht
    have hs : (t - (i.val : ℝ) / N) * N ∈ Icc (0 : ℝ) 1 := by
      constructor
      · have := ht.1
        nlinarith
      · have := ht.2
        have h1 : (t - (i.val : ℝ) / N) < 1 / N := by linarith
        rw [lt_div_iff₀ hN'] at h1
        nlinarith
    have := hconst _ hs
    rwa [show (i.val : ℝ) / N + (t - (i.val : ℝ) / N) * N * (1 / N) = t by field_simp; ring] at this
  have hd : HasDerivAt (Finsler.EnergyConservation.position g.loop) 0 m :=
    (hasDerivAt_const m _).congr_of_eventuallyEq hev
  exact deriv_position_ne_zero g.loop g.regular m hd.deriv

end Geodesic

/-- Samples of closed geodesics at fine spacing are critical polygons with the energy of the
geodesic. -/
theorem polyCritical_of_closedGeodesic {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (Finsler.EnergySphereSmooth.ambientMinEnergy F)
        ((P : Ambient n), (Q : Ambient n)))
    (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      ShortPolygon δ (samplePoly N (ofSmooth g.loop)) ∧
      PolyCritical F N (samplePoly N (ofSmooth g.loop)) ∧
      polyEnergy F N (sampleN N (ofSmooth g.loop)) = energy F (ofSmooth g.loop) := by
  obtain ⟨h₀, hh₀, hscale⟩ := exists_arc_scale (F := F) (γ := g.loop)
  set E := energy F (ofSmooth g.loop) with hEdef
  have hE0 : 0 ≤ E := (energy_nonneg F _)
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := δ) (a := E + 1) hδpos
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (1 / h₀)
  refine ⟨max N₁ (N₂ + 1), fun N hN _ => ?_⟩
  have hNpos := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hEu : E < (E + 1) ^ 2 := by nlinarith
  have hq : ShortPolygon δ (samplePoly N (ofSmooth g.loop)) :=
    shortPolygon_samplePoly F (fun u hu s t hs ht hst =>
      hN₁ N ((le_max_left _ _).trans hN) hNpos u hu s t hs ht hst) hEu
  have h1N : 1 / (N : ℝ) < h₀ := by
    have h2 : (N₂ : ℝ) + 1 ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
    rw [div_lt_iff₀ hN']
    have h3 : 1 / h₀ < N := by linarith
    rw [div_lt_iff₀ hh₀] at h3
    linarith
  have hE := polyEnergy_ofSmooth_eq g hscale h1N
  have hne := samplePoly_ofSmooth_ne g hscale h1N
  exact ⟨hq, polyCritical_of_tangentCritical F hδ
    (Finsler.SobolevGeodesicCritical.tangentCritical_of_closedGeodesic F g) hq hne hE, hE⟩

section Broken

variable {F} {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F (sc P Q t, sv P Q t) =
      Finsler.SphereDistance.minEnergy F P Q)
  (hpkg : ∀ (T : SegChart F) (P Q : Sphere n), P ∈ segDom T → ‖(Q : Ambient n) - P‖ < δ →
    ‖(Q : Ambient n) - P‖ < T.δ → ∀ t ∈ Icc (0 : ℝ) 1, sc P Q t = segCurve T P Q t)
  (g : Finsler.Geodesics.ClosedGeodesic F) {h₀ : ℝ}
  (hscale : ∀ a ∈ Icc (0 : ℝ) 1, ∀ h ∈ Ioo (0 : ℝ) h₀, ∃ S : SegChart F, ArcGood g.loop S a h)

theorem samplePoly_ofSmooth_natCast {N : ℕ} [NeZero N] {k : ℕ} (hk : k < N) :
    samplePoly N (ofSmooth g.loop) (k : ZMod N) = g.loop ((k : ℝ) / N) :=
  Subtype.ext (sampleN_ofSmooth_natCast g.loop hk)

theorem samplePoly_ofSmooth_natCast_succ {N : ℕ} [NeZero N] {k : ℕ} (hk : k < N) :
    samplePoly N (ofSmooth g.loop) ((k : ZMod N) + 1) = g.loop (((k : ℝ) + 1) / N) :=
  Subtype.ext (sampleN_ofSmooth_natCast_succ g.loop hk)

include hpkg hscale in
/-- For N large the broken geodesic of the samples of a closed geodesic is the geodesic. -/
theorem polySphereLoop_samples {N : ℕ} [NeZero N] (hN : 1 / (N : ℝ) < h₀)
    (hq : ShortPolygon δ (samplePoly N (ofSmooth g.loop))) :
    polySphereLoop F hseg hq = ofSmooth g.loop := by
  have hNpos := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have he := coordinateEuler_of_closedGeodesic g
  apply Finsler.SobolevEnergy.sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  change continuousRepresentative (polyLoop F hseg hq) t =
    continuousRepresentative (graphData g.loop) t
  rw [representative_polyLoop F hseg hq t.2, representative_graphData g.loop t.2]
  have hk := Finsler.PiecewiseC1.pieceIdx_lt hNpos (t : ℝ)
  have hpiece := Finsler.PiecewiseC1.mem_piece hNpos t.2
  set k := Finsler.PiecewiseC1.pieceIdx N (t : ℝ) with hkdef
  have ha : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hN']; exact_mod_cast hk.le⟩
  obtain ⟨S, hP, hQ, hsrc, hsmall⟩ := hscale _ ha (1 / N) ⟨by positivity, hN⟩
  have harc := arc_eq_segCurve g.regular he S (by positivity) hP hQ hsrc hsmall
  have hloc : (N : ℝ) * t - k ∈ Icc (0 : ℝ) 1 := by
    have h1 := hpiece.1
    have h2 := hpiece.2
    rw [div_le_iff₀ hN'] at h1
    rw [le_div_iff₀ hN'] at h2
    constructor <;> linarith
  have hend : (k : ℝ) / N + 1 / N = ((k : ℝ) + 1) / N := by ring
  have hshort : ‖(g.loop ((k : ℝ) / N + 1 / N) : Ambient n) - g.loop ((k : ℝ) / N)‖ < δ := by
    have h := hq (k : ZMod N)
    rw [samplePoly_ofSmooth_natCast_succ g hk, samplePoly_ofSmooth_natCast g hk] at h
    rwa [hend]
  unfold polyCurve
  rw [Finsler.PiecewiseC1.glue_eq_of_mem_Icc hk (fun j _ => edge_match F hseg hq j) hpiece]
  unfold edgeCurve
  rw [samplePoly_ofSmooth_natCast g hk, samplePoly_ofSmooth_natCast_succ g hk, ← hend,
    hpkg S _ _ hP hshort hQ _ hloc, ← harc _ hloc]
  congr 2
  field_simp
  ring

end Broken

end

end Finsler.PolygonGeodesic
