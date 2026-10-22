module

public import Finsler.Geometry.GeodesicArcs

/-! Uniqueness of geodesics and closed geodesics with the same image. In a chart an affinely
reparametrized arc of a regular loop satisfying the coordinate Euler–Lagrange equation is an
integral curve of the jet field (velocity, spray), which is C¹ along it, so two such arcs with
the same position and velocity at one time agree for nearby later times; the set of times at
which the positions and the velocities of two arcs agree is closed and open, so the arcs agree
for all times. Two regular loops such that the image of the first is contained in the image of
the second have a common point with linearly dependent velocities: the set of coincidences
in the unit square is compact and infinite, and a coincidence with independent velocities is
isolated. Hence a prime closed geodesic is determined by its image up to a rotation and the
reversal, and two prime closed geodesics with the same image have the same energy. The reversal
of a regular loop is never a rotation of it, so each closed geodesic has two orientations. -/

@[expose] public section

namespace Finsler.GeodesicUnique

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.ChartTransfer Finsler.GeodesicArcs Finsler.Loops Finsler.EnergyConservation
open Finsler.Geodesics Finsler.OdeUnique
open Function Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n}

/-- The ambient velocity of a loop is the chart differential of its coordinate velocity. -/
theorem deriv_position_eq (p : Sphere n) (γ : SmoothLoop n) {t : ℝ}
    (ht : γ t ∈ (extChartAt (𝓡 n) p).source) :
    deriv (position γ) t =
      fderiv ℝ (inverseAmbient p) (coordinateCurve p γ t) (deriv (coordinateCurve p γ) t) := by
  have hy := (extChartAt (𝓡 n) p).map_source ht
  have hc := (coordinateCurve_smoothAt p γ ht).differentiableAt (by simp)
  have hφ := (inverseAmbient_smoothAt p hy).differentiableAt (by simp)
  have hcomp : HasDerivAt (inverseAmbient p ∘ coordinateCurve p γ)
      (fderiv ℝ (inverseAmbient p) (coordinateCurve p γ t) (deriv (coordinateCurve p γ) t)) t :=
    hφ.hasFDerivAt.comp_hasDerivAt t hc.hasDerivAt
  exact (hcomp.congr_of_eventuallyEq
    (inverseAmbient_coordinateCurve_eventually p γ ht).symm).deriv

section Single

variable {γ : SmoothLoop n} (hreg : Finsler.Geodesics.Regular γ) (he : CoordinateEuler F γ) (p : Sphere n)
  {a h : ℝ}

theorem arc_contDiffAt {s : ℝ} (hs : γ (a + s * h) ∈ (extChartAt (𝓡 n) p).source) :
    ContDiffAt ℝ 2 (fun s => coordinateCurve p γ (a + s * h)) s := by
  have hc : ContDiffAt ℝ 2 (coordinateCurve p γ) (a + s * h) :=
    (coordinateCurve_smoothAt p γ hs).of_le (by simp)
  have hl : ContDiffAt ℝ 2 (fun s : ℝ => a + s * h) s :=
    (contDiff_const.add (contDiff_id.mul contDiff_const)).contDiffAt
  exact ContDiffAt.comp (g := coordinateCurve p γ) (f := fun s : ℝ => a + s * h) s hc hl

theorem arc_jet {s : ℝ} (hs : γ (a + s * h) ∈ (extChartAt (𝓡 n) p).source) :
    curveJet (fun s => coordinateCurve p γ (a + s * h)) s =
      (coordinateCurve p γ (a + s * h), h • deriv (coordinateCurve p γ) (a + s * h)) := by
  unfold curveJet
  rw [(arc_hasDerivAt p hs).deriv]

include hreg he in
/-- The jet of an affinely reparametrized arc is an integral curve of the jet field. -/
theorem arc_jet_hasDerivAt (hh : h ≠ 0) {s : ℝ}
    (hs : γ (a + s * h) ∈ (extChartAt (𝓡 n) p).source) :
    HasDerivAt (curveJet (fun s => coordinateCurve p γ (a + s * h)))
      ((curveJet (fun s => coordinateCurve p γ (a + s * h)) s).2,
        spray (coordinateLagrangian F p)
          (curveJet (fun s => coordinateCurve p γ (a + s * h)) s)) s := by
  have h1 := curveJet_hasDerivAt (arc_contDiffAt p hs)
  rw [arc_spray hreg he p hh hs] at h1
  exact h1

include hreg in
/-- The jet field is C¹ along an affinely reparametrized arc. -/
theorem arc_field_contDiffAt (F : ReversibleMetric n) (hh : h ≠ 0) {s : ℝ}
    (hs : γ (a + s * h) ∈ (extChartAt (𝓡 n) p).source) :
    ContDiffAt ℝ 1 (fun z : Coordinates n × Coordinates n =>
        (z.2, spray (coordinateLagrangian F p) z))
      (curveJet (fun s => coordinateCurve p γ (a + s * h)) s) := by
  rw [arc_jet p hs]
  have hy : coordinateCurve p γ (a + s * h) ∈ (extChartAt (𝓡 n) p).target :=
    (extChartAt (𝓡 n) p).map_source hs
  have hv : h • deriv (coordinateCurve p γ) (a + s * h) ≠ 0 :=
    smul_ne_zero hh (deriv_coordinateCurve_ne_zero hreg p hs)
  have hsp := coordinate_spray_contDiffAt F p hy hv 1
  rw [Nat.cast_one] at hsp
  exact contDiffAt_snd.prodMk hsp

end Single

section Pair

variable {γ₁ γ₂ : SmoothLoop n} (hr₁ : Finsler.Geodesics.Regular γ₁) (he₁ : CoordinateEuler F γ₁)
  (hr₂ : Finsler.Geodesics.Regular γ₂) (he₂ : CoordinateEuler F γ₂) {a₁ a₂ h₁ h₂ : ℝ}

include hr₁ he₁ hr₂ he₂ in
/-- Local forward uniqueness in a chart. -/
theorem exists_forward_eq_chart (p : Sphere n) (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0)
    (hsrc : γ₁ a₁ ∈ (extChartAt (𝓡 n) p).source) (hpos : γ₁ a₁ = γ₂ a₂)
    (hvel : h₁ • deriv (position γ₁) a₁ = h₂ • deriv (position γ₂) a₂) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Icc (0 : ℝ) ε, γ₁ (a₁ + s * h₁) = γ₂ (a₂ + s * h₂) := by
  have hsrc₂ : γ₂ a₂ ∈ (extChartAt (𝓡 n) p).source := hpos ▸ hsrc
  have hc₁ : ContinuousAt (fun s : ℝ => γ₁ (a₁ + s * h₁)) 0 :=
    γ₁.smooth.continuous.continuousAt.comp
      ((continuous_const.add (continuous_id.mul continuous_const)).continuousAt)
  have hc₂ : ContinuousAt (fun s : ℝ => γ₂ (a₂ + s * h₂)) 0 :=
    γ₂.smooth.continuous.continuousAt.comp
      ((continuous_const.add (continuous_id.mul continuous_const)).continuousAt)
  have hs₁ : γ₁ (a₁ + 0 * h₁) ∈ (extChartAt (𝓡 n) p).source := by
    rw [zero_mul, add_zero]
    exact hsrc
  have hs₂ : γ₂ (a₂ + 0 * h₂) ∈ (extChartAt (𝓡 n) p).source := by
    rw [zero_mul, add_zero]
    exact hsrc₂
  have hev₁ := hc₁.preimage_mem_nhds ((isOpen_extChartAt_source p).mem_nhds hs₁)
  have hev₂ := hc₂.preimage_mem_nhds ((isOpen_extChartAt_source p).mem_nhds hs₂)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hev₁ hev₂)
  refine ⟨ε / 2, by positivity, ?_⟩
  have hsrcs : ∀ s ∈ Icc (0 : ℝ) (ε / 2),
      γ₁ (a₁ + s * h₁) ∈ (extChartAt (𝓡 n) p).source ∧
        γ₂ (a₂ + s * h₂) ∈ (extChartAt (𝓡 n) p).source := by
    intro s hs
    have hsb : s ∈ ball (0 : ℝ) ε := by
      rw [Real.ball_eq_Ioo]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact hball hsb
  have hy : coordinateCurve p γ₁ a₁ = coordinateCurve p γ₂ a₂ :=
    congrArg (extChartAt (𝓡 n) p) hpos
  have hyt : coordinateCurve p γ₁ a₁ ∈ (extChartAt (𝓡 n) p).target :=
    (extChartAt (𝓡 n) p).map_source hsrc
  have hd : h₁ • deriv (coordinateCurve p γ₁) a₁ = h₂ • deriv (coordinateCurve p γ₂) a₂ := by
    apply fderiv_inverseAmbient_injective p hyt
    rw [map_smul, map_smul, ← deriv_position_eq p γ₁ hsrc, hy, ← deriv_position_eq p γ₂ hsrc₂]
    exact hvel
  have hinit : curveJet (fun s => coordinateCurve p γ₁ (a₁ + s * h₁)) 0 =
      curveJet (fun s => coordinateCurve p γ₂ (a₂ + s * h₂)) 0 := by
    rw [arc_jet p hs₁, arc_jet p hs₂]
    simp only [zero_mul, add_zero]
    rw [hy, hd]
  have heq : EqOn (curveJet (fun s => coordinateCurve p γ₁ (a₁ + s * h₁)))
      (curveJet (fun s => coordinateCurve p γ₂ (a₂ + s * h₂))) (Icc 0 (ε / 2)) := by
    apply eqOn_of_contDiffAt
      (v := fun z : Coordinates n × Coordinates n => (z.2, spray (coordinateLagrangian F p) z))
    · intro t ht
      exact arc_field_contDiffAt hr₁ p F hh₁ (hsrcs t ht).1
    · intro t ht
      exact arc_jet_hasDerivAt hr₁ he₁ p hh₁ (hsrcs t ht).1
    · intro t ht
      exact arc_jet_hasDerivAt hr₂ he₂ p hh₂ (hsrcs t ht).2
    · exact hinit
  intro s hs
  have h1 : coordinateCurve p γ₁ (a₁ + s * h₁) = coordinateCurve p γ₂ (a₂ + s * h₂) :=
    congrArg Prod.fst (heq hs)
  exact (extChartAt (𝓡 n) p).injOn (hsrcs s hs).1 (hsrcs s hs).2 h1

include hr₁ he₁ hr₂ he₂ in
/-- Local forward uniqueness. -/
theorem exists_forward_eq (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) (hpos : γ₁ a₁ = γ₂ a₂)
    (hvel : h₁ • deriv (position γ₁) a₁ = h₂ • deriv (position γ₂) a₂) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Icc (0 : ℝ) ε, γ₁ (a₁ + s * h₁) = γ₂ (a₂ + s * h₂) :=
  exists_forward_eq_chart hr₁ he₁ hr₂ he₂ (γ₁ a₁) hh₁ hh₂ (mem_extChartAt_source (γ₁ a₁)) hpos
    hvel

/-- The derivative of the ambient position along an affinely reparametrized loop. -/
theorem affine_position_hasDerivAt (γ : SmoothLoop n) (a h s : ℝ) :
    HasDerivAt (fun r : ℝ => position γ (a + r * h)) (h • deriv (position γ) (a + s * h)) s := by
  have hc : HasDerivAt (position γ) (deriv (position γ) (a + s * h)) (a + s * h) :=
    ((position_smooth γ).differentiable (by simp) (a + s * h)).hasDerivAt
  have hl : HasDerivAt (fun r : ℝ => a + r * h) h s := by
    have := ((hasDerivAt_id' s).mul_const h).const_add a
    rwa [one_mul] at this
  exact hc.scomp s hl

include hr₁ he₁ hr₂ he₂ in
/-- Uniqueness of geodesics: two affinely reparametrized closed geodesics with the same
position and the same velocity at one time agree at all times. -/
theorem eq_of_jet_eq (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) (hpos : γ₁ a₁ = γ₂ a₂)
    (hvel : h₁ • deriv (position γ₁) a₁ = h₂ • deriv (position γ₂) a₂) (s : ℝ) :
    γ₁ (a₁ + s * h₁) = γ₂ (a₂ + s * h₂) := by
  have hl₁ : Continuous (fun s : ℝ => a₁ + s * h₁) :=
    continuous_const.add (continuous_id.mul continuous_const)
  have hl₂ : Continuous (fun s : ℝ => a₂ + s * h₂) :=
    continuous_const.add (continuous_id.mul continuous_const)
  have key : {s : ℝ | γ₁ (a₁ + s * h₁) = γ₂ (a₂ + s * h₂) ∧
      h₁ • deriv (position γ₁) (a₁ + s * h₁) = h₂ • deriv (position γ₂) (a₂ + s * h₂)} =
        univ := by
    apply IsClopen.eq_univ ⟨?_, ?_⟩ ⟨0, ?_⟩
    · have hA : IsClosed {s : ℝ | γ₁ (a₁ + s * h₁) = γ₂ (a₂ + s * h₂)} :=
        isClosed_eq (γ₁.smooth.continuous.comp hl₁) (γ₂.smooth.continuous.comp hl₂)
      have hB : IsClosed {s : ℝ | h₁ • deriv (position γ₁) (a₁ + s * h₁) =
          h₂ • deriv (position γ₂) (a₂ + s * h₂)} :=
        isClosed_eq
          ((((position_smooth γ₁).continuous_deriv (by simp)).comp hl₁).const_smul h₁)
          ((((position_smooth γ₂).continuous_deriv (by simp)).comp hl₂).const_smul h₂)
      exact hA.inter hB
    · rw [isOpen_iff_mem_nhds]
      rintro s₁ ⟨hp₁, hv₁⟩
      obtain ⟨ε, hε, hfwd⟩ := exists_forward_eq hr₁ he₁ hr₂ he₂ hh₁ hh₂ hp₁ hv₁
      obtain ⟨ε', hε', hbwd⟩ := exists_forward_eq hr₁ he₁ hr₂ he₂ (neg_ne_zero.mpr hh₁)
        (neg_ne_zero.mpr hh₂) hp₁ (by rw [neg_smul, neg_smul, hv₁])
      have hagree : ∀ s ∈ Ioo (s₁ - ε') (s₁ + ε), γ₁ (a₁ + s * h₁) = γ₂ (a₂ + s * h₂) := by
        intro s hs
        rcases le_total s₁ s with h | h
        · have h3 := hfwd (s - s₁) ⟨by linarith, by linarith [hs.2]⟩
          rw [show a₁ + s₁ * h₁ + (s - s₁) * h₁ = a₁ + s * h₁ by ring,
            show a₂ + s₁ * h₂ + (s - s₁) * h₂ = a₂ + s * h₂ by ring] at h3
          exact h3
        · have h3 := hbwd (s₁ - s) ⟨by linarith, by linarith [hs.1]⟩
          rw [show a₁ + s₁ * h₁ + (s₁ - s) * -h₁ = a₁ + s * h₁ by ring,
            show a₂ + s₁ * h₂ + (s₁ - s) * -h₂ = a₂ + s * h₂ by ring] at h3
          exact h3
      have hmem : Ioo (s₁ - ε') (s₁ + ε) ∈ 𝓝 s₁ := Ioo_mem_nhds (by linarith) (by linarith)
      refine Filter.mem_of_superset hmem fun s hs => ⟨hagree s hs, ?_⟩
      have hev : (fun r : ℝ => position γ₁ (a₁ + r * h₁)) =ᶠ[𝓝 s]
          fun r => position γ₂ (a₂ + r * h₂) := by
        filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
        exact congrArg Subtype.val (hagree r hr)
      exact (affine_position_hasDerivAt γ₁ a₁ h₁ s).unique
        ((affine_position_hasDerivAt γ₂ a₂ h₂ s).congr_of_eventuallyEq hev)
    · change γ₁ (a₁ + 0 * h₁) = γ₂ (a₂ + 0 * h₂) ∧
        h₁ • deriv (position γ₁) (a₁ + 0 * h₁) = h₂ • deriv (position γ₂) (a₂ + 0 * h₂)
      rw [zero_mul, zero_mul, add_zero, add_zero]
      exact ⟨hpos, hvel⟩
  have hs : s ∈ {s : ℝ | γ₁ (a₁ + s * h₁) = γ₂ (a₂ + s * h₂) ∧
      h₁ • deriv (position γ₁) (a₁ + s * h₁) = h₂ • deriv (position γ₂) (a₂ + s * h₂)} := by
    rw [key]
    exact mem_univ s
  exact hs.1

end Pair

/-- The reversal of a regular loop is not a rotation of it: at a fixed time of the parameter
reflection the velocity would vanish. -/
theorem reverse_ne_shift {γ : SmoothLoop n} (hreg : Finsler.Geodesics.Regular γ) (a : ℝ) :
    reverse γ ≠ shift γ a := by
  intro h
  have hpos : ∀ t : ℝ, position γ (-t) = position γ (t + a) := fun t =>
    congrArg Subtype.val (congrArg (fun σ : SmoothLoop n => σ t) h)
  have h1 := affine_position_hasDerivAt γ 0 (-1) (-a / 2)
  have h2 := affine_position_hasDerivAt γ a 1 (-a / 2)
  have e1 : (0 : ℝ) + -a / 2 * -1 = a / 2 := by ring
  have e2 : a + -a / 2 * 1 = a / 2 := by ring
  rw [e1] at h1
  rw [e2] at h2
  have hfun : (fun r : ℝ => position γ (0 + r * -1)) = fun r => position γ (a + r * 1) := by
    funext r
    rw [show (0 : ℝ) + r * -1 = -r by ring, show a + r * 1 = r + a by ring]
    exact hpos r
  rw [hfun] at h1
  have heq := h1.unique h2
  rw [neg_one_smul, one_smul] at heq
  have h3 : (2 : ℝ) • deriv (position γ) (a / 2) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← heq]
    exact neg_add_cancel _
  exact Finsler.PolygonCritical.deriv_position_ne_zero γ hreg (a / 2)
    ((smul_eq_zero.mp h3).resolve_left two_ne_zero)

/-- Two regular loops such that the image of the first is contained in the image of the second
have a common point at which their velocities are proportional. -/
theorem exists_tangent {γ₁ γ₂ : SmoothLoop n} (hr₁ : Finsler.Geodesics.Regular γ₁) (hr₂ : Finsler.Geodesics.Regular γ₂)
    (himg : Finsler.Loops.image γ₁ ⊆ Finsler.Loops.image γ₂) :
    ∃ s₀ t₀ : ℝ, γ₁ s₀ = γ₂ t₀ ∧ ∃ c : ℝ, c ≠ 0 ∧
      deriv (position γ₂) t₀ = c • deriv (position γ₁) s₀ := by
  by_contra hcon
  push Not at hcon
  have hclosed : IsClosed {z : ℝ × ℝ | position γ₁ z.1 = position γ₂ z.2} :=
    isClosed_eq ((position_smooth γ₁).continuous.comp continuous_fst)
      ((position_smooth γ₂).continuous.comp continuous_snd)
  have hcompact : IsCompact ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩
      {z : ℝ × ℝ | position γ₁ z.1 = position γ₂ z.2}) :=
    (isCompact_Icc.prod isCompact_Icc).inter_right hclosed
  have hsub : Icc (0 : ℝ) 1 ⊆ Prod.fst '' ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩
      {z : ℝ × ℝ | position γ₁ z.1 = position γ₂ z.2}) := by
    intro s hs
    have hmem : γ₁ s ∈ Finsler.Loops.image γ₂ := himg ⟨s, rfl⟩
    have hrange : Finsler.Loops.image γ₂ = γ₂.curve '' Icc (0 : ℝ) (0 + 1) :=
      (γ₂.periodic.image_Icc one_pos 0).symm
    rw [hrange, zero_add] at hmem
    obtain ⟨t, ht, hγ⟩ := hmem
    exact ⟨(s, t), ⟨⟨hs, ht⟩, (congrArg Subtype.val hγ).symm⟩, rfl⟩
  have hinf : ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩
      {z : ℝ × ℝ | position γ₁ z.1 = position γ₂ z.2}).Infinite :=
    Set.Infinite.of_image Prod.fst ((Icc_infinite (zero_lt_one' ℝ)).mono hsub)
  obtain ⟨z₀, hz₀, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hcompact Subset.rfl
  have hfreq := accPt_iff_frequently_nhdsNE.mp hacc
  have hp₀ : γ₁ z₀.1 = γ₂ z₀.2 := Subtype.ext hz₀.2
  have hv₁ : deriv (position γ₁) z₀.1 ≠ 0 :=
    Finsler.PolygonCritical.deriv_position_ne_zero γ₁ hr₁ z₀.1
  have hv₂ : deriv (position γ₂) z₀.2 ≠ 0 :=
    Finsler.PolygonCritical.deriv_position_ne_zero γ₂ hr₂ z₀.2
  have hd₁ : HasFDerivAt (fun z : ℝ × ℝ => position γ₁ z.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv (position γ₁) z₀.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) z₀ :=
    (((position_smooth γ₁).differentiable (by simp) z₀.1).hasDerivAt.hasFDerivAt).comp z₀
      hasFDerivAt_fst
  have hd₂ : HasFDerivAt (fun z : ℝ × ℝ => position γ₂ z.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv (position γ₂) z₀.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) z₀ :=
    (((position_smooth γ₂).differentiable (by simp) z₀.2).hasDerivAt.hasFDerivAt).comp z₀
      hasFDerivAt_snd
  have hd := hd₁.sub hd₂
  have hker : LinearMap.ker
      (((ContinuousLinearMap.toSpanSingleton ℝ (deriv (position γ₁) z₀.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ) -
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv (position γ₂) z₀.2)).comp
          (ContinuousLinearMap.snd ℝ ℝ ℝ) : ℝ × ℝ →L[ℝ] Ambient n) :
            ℝ × ℝ →ₗ[ℝ] Ambient n) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ hxy
    have hxy' : x • deriv (position γ₁) z₀.1 - y • deriv (position γ₂) z₀.2 = 0 := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply] using hxy
    have hy0 : y = 0 := by
      by_contra hy
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [zero_smul, zero_sub, neg_eq_zero] at hxy'
        exact hv₂ ((smul_eq_zero.mp hxy').resolve_left hy)
      refine hcon z₀.1 z₀.2 hp₀ (y⁻¹ * x) (mul_ne_zero (inv_ne_zero hy) hx0) ?_
      rw [mul_smul, sub_eq_zero.mp hxy', inv_smul_smul₀ hy]
    subst hy0
    rw [zero_smul, sub_zero] at hxy'
    have hx0 : x = 0 := (smul_eq_zero.mp hxy').resolve_right hv₁
    rw [hx0]
    rfl
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith _ hker
  have hne : ∀ᶠ z in 𝓝[≠] z₀, position γ₁ z.1 - position γ₂ z.2 ≠ 0 :=
    hd.eventually_ne ⟨K, hK⟩
  obtain ⟨z, hz, hzne⟩ := (hfreq.and_eventually hne).exists
  exact hzne (sub_eq_zero.mpr hz.2)

/-- A prime closed geodesic is determined by its image up to a rotation and the reversal. -/
theorem shift_or_reverse_of_image_eq (γ₁ γ₂ : ClosedGeodesic F)
    (hp₁ : Finsler.Geodesics.Prime γ₁) (hp₂ : Finsler.Geodesics.Prime γ₂)
    (himg : Finsler.Loops.image γ₁.loop = Finsler.Loops.image γ₂.loop) :
    ∃ a : ℝ, γ₂.loop = shift γ₁.loop a ∨ γ₂.loop = reverse (shift γ₁.loop a) := by
  have he₁ : CoordinateEuler F γ₁.loop :=
    (stationary_iff_coordinateEuler F γ₁.regular).mp γ₁.stationary
  have he₂ : CoordinateEuler F γ₂.loop :=
    (stationary_iff_coordinateEuler F γ₂.regular).mp γ₂.stationary
  obtain ⟨s₀, t₀, hp, c, hc, hv⟩ := exists_tangent γ₁.regular γ₂.regular himg.subset
  have huniq : ∀ s : ℝ, γ₁.loop (s₀ + s * c) = γ₂.loop (t₀ + s * 1) := fun s =>
    eq_of_jet_eq γ₁.regular he₁ γ₂.regular he₂ hc one_ne_zero hp (by rw [one_smul, hv]) s
  -- c is a period of the first loop
  have hper₁ : Periodic γ₁.loop c := by
    intro x
    have e1 := huniq ((x - s₀) / c + 1)
    have e2 := huniq ((x - s₀) / c)
    rw [show s₀ + ((x - s₀) / c + 1) * c = x + c by field_simp; ring] at e1
    rw [show s₀ + (x - s₀) / c * c = x by field_simp; ring] at e2
    rw [e1, e2, show t₀ + ((x - s₀) / c + 1) * 1 = t₀ + (x - s₀) / c * 1 + 1 by ring]
    exact γ₂.loop.periodic _
  -- 1/c is a period of the second loop
  have hper₂ : Periodic γ₂.loop (1 / c) := by
    intro y
    have e1 := huniq (y - t₀ + 1 / c)
    have e2 := huniq (y - t₀)
    rw [show t₀ + (y - t₀ + 1 / c) * 1 = y + 1 / c by ring] at e1
    rw [show t₀ + (y - t₀) * 1 = y by ring] at e2
    rw [← e1, ← e2, show s₀ + (y - t₀ + 1 / c) * c = s₀ + (y - t₀) * c + 1 by field_simp; ring]
    exact γ₁.loop.periodic _
  have habs₁ : 1 ≤ |c| := by
    rcases abs_choice c with h | h
    · rw [h]
      exact hp₁ c (by rw [← h]; exact abs_pos.mpr hc) hper₁
    · rw [h]
      exact hp₁ (-c) (by rw [← h]; exact abs_pos.mpr hc) hper₁.neg
  have habs₂ : 1 ≤ |1 / c| := by
    have hc' : (1 : ℝ) / c ≠ 0 := one_div_ne_zero hc
    rcases abs_choice (1 / c) with h | h
    · rw [h]
      exact hp₂ (1 / c) (by rw [← h]; exact abs_pos.mpr hc') hper₂
    · rw [h]
      exact hp₂ (-(1 / c)) (by rw [← h]; exact abs_pos.mpr hc') hper₂.neg
  have habs : |c| = 1 := by
    rw [abs_div, abs_one, le_div_iff₀ (abs_pos.mpr hc), one_mul] at habs₂
    exact le_antisymm habs₂ habs₁
  rcases abs_choice c with h | h
  · -- c = 1
    have hc1 : c = 1 := by rw [← h, habs]
    subst hc1
    refine ⟨s₀ - t₀, Or.inl ?_⟩
    apply loop_ext
    intro t
    have e := huniq (t - t₀)
    rw [show t₀ + (t - t₀) * 1 = t by ring] at e
    rw [← e]
    change γ₁.loop (s₀ + (t - t₀) * 1) = γ₁.loop (t + (s₀ - t₀))
    congr 1
    ring
  · -- c = -1
    have hc1 : c = -1 := by
      have : -c = 1 := by rw [← h, habs]
      linarith
    subst hc1
    refine ⟨s₀ + t₀, Or.inr ?_⟩
    apply loop_ext
    intro t
    have e := huniq (t - t₀)
    rw [show t₀ + (t - t₀) * 1 = t by ring] at e
    rw [← e]
    change γ₁.loop (s₀ + (t - t₀) * -1) = γ₁.loop (-t + (s₀ + t₀))
    congr 1
    ring

/-- Two prime closed geodesics with the same image have the same energy. -/
theorem energy_eq_of_image_eq (γ₁ γ₂ : ClosedGeodesic F)
    (hp₁ : Finsler.Geodesics.Prime γ₁) (hp₂ : Finsler.Geodesics.Prime γ₂)
    (himg : Finsler.Loops.image γ₁.loop = Finsler.Loops.image γ₂.loop) :
    Finsler.LoopEnergy.energy F γ₂.loop = Finsler.LoopEnergy.energy F γ₁.loop := by
  obtain ⟨a, h | h⟩ := shift_or_reverse_of_image_eq γ₁ γ₂ hp₁ hp₂ himg
  · rw [h, Finsler.LoopEnergy.energy_shift]
  · rw [h, Finsler.LoopEnergy.energy_reverse, Finsler.LoopEnergy.energy_shift]

end

end Finsler.GeodesicUnique
