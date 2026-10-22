module

public import Finsler.Geometry.SegmentContinuity
public import Finsler.Geometry.SegmentReverse

/-! The curve-level short-segment map. For endpoints within a uniform δ the segment from P to Q is a
C¹ curve on the unit sphere from P to Q whose energy integral is e(P,Q), and the segments and
their velocities converge uniformly on [0,1] as the endpoints converge. On overlaps of chart
packages the velocities agree on the whole closed interval by uniqueness of derivatives within
[0,1]. Choosing δ below a Lebesgue number of the packages, P and Q lie in a common package, and
the segment from Q to P is the reversed segment from P to Q, since the transported endpoint
velocity has F² = e(P,Q). -/

@[expose] public section

namespace Finsler.SegmentCurves

open Finsler.SphereGeometry Finsler.Geometry Finsler.SegmentAtlas Finsler.SegmentContinuity
open Finsler.SobolevC1Continuity Finsler.AmbientLagrangian Finsler.SphereCoordinateEuler
open Finsler.CoordinateExpInverse Finsler.ChartTransfer Finsler.SegmentReverse Finsler.EikonalChart
open Finsler.AmbientCalibrator
open Finsler.SphereDistance (minEnergy)
open Set Filter
open scoped Topology Manifold

noncomputable section

variable {n : ℕ}

/-- The velocities of two packages agree on [0,1] where both apply. -/
theorem segVel_eq {F : ReversibleMetric n} {S T : SegChart F} {P Q : Sphere n}
    (hPS : P ∈ segDom S) (hPT : P ∈ segDom T) (hQS : ‖(Q : Ambient n) - P‖ < S.δ)
    (hQT : ‖(Q : Ambient n) - P‖ < T.δ)
    (heq : ∀ t ∈ Icc (0 : ℝ) 1, segCurve S P Q t = segCurve T P Q t) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : segVel S P Q t = segVel T P Q t := by
  have h1 := (segCurve_hasDerivAt S hPS hQS ht).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  have h2 := (segCurve_hasDerivAt T hPT hQT ht).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  have h2' : HasDerivWithinAt (segCurve S P Q) (segVel T P Q t) (Icc (0 : ℝ) 1) t :=
    h2.congr heq (heq t ht)
  exact (uniqueDiffOn_Icc_zero_one t ht).eq_deriv _ h1 h2'

/-- In a common package the segment from Q to P is the reversed segment from P to Q. -/
theorem segCurve_reverse {F : ReversibleMetric n} (S : SegChart F) {P Q : Sphere n}
    (hP : P ∈ segDom S) (hQ : Q ∈ segDom S) (hQP : ‖(Q : Ambient n) - P‖ < S.δ) {C : ℝ}
    (hup : minEnergy F P Q ≤ C * ‖(Q : Ambient n) - P‖ ^ 2)
    (hρ : C * ‖(Q : Ambient n) - P‖ ^ 2 < S.c * S.D.ρ ^ 2) :
    ∀ s ∈ Icc (0 : ℝ) 1, segCurve S Q P s = segCurve S P Q (1 - s) := by
  have hy := chart_mem_closedBall S hP
  have hz := chart_mem_closedBall S hQ
  have hyz := chart_dist_lt S hP hQP
  rw [chartNormalize_sphere S Q] at hyz
  intro s hs
  unfold segCurve
  rw [chartNormalize_sphere S P, chartNormalize_sphere S Q]
  by_cases hzy : extChartAt (𝓡 n) S.p Q = extChartAt (𝓡 n) S.p P
  · rw [hzy, geo_self S.D hy, geo_self S.D hy]
  · have hsmall : ‖deriv (geo F S.D (extChartAt (𝓡 n) S.p P) (extChartAt (𝓡 n) S.p Q)) 1‖ <
        S.D.ρ := by
      have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
      have hE := geo_energy_const S.D hy (z := extChartAt (𝓡 n) S.p Q) hyz h1mem
      have hvel : geoVel S.D (extChartAt (𝓡 n) S.p P) (extChartAt (𝓡 n) S.p Q) 1 =
          deriv (geo F S.D (extChartAt (𝓡 n) S.p P) (extChartAt (𝓡 n) S.p Q)) 1 :=
        (geo_hasDerivAt S.D _ _ 1).deriv.symm
      have hend : geo F S.D (extChartAt (𝓡 n) S.p P) (extChartAt (𝓡 n) S.p Q) 1 =
          extChartAt (𝓡 n) S.p Q := geodesic_endpoint S.D hy hyz.le hzy
      rw [hvel, hend] at hE
      have hmin : coordinateLagrangian F S.p (extChartAt (𝓡 n) S.p P,
          expInv S.D (extChartAt (𝓡 n) S.p P) (extChartAt (𝓡 n) S.p Q)) = minEnergy F P Q := by
        rw [minE_of_dom S hP hQP]
        unfold ambientEnergy Finsler.EikonalChart.energyFn
        rw [chartNormalize_sphere S Q]
      rw [hmin] at hE
      have hlow := S.lower _ hz
        (deriv (geo F S.D (extChartAt (𝓡 n) S.p P) (extChartAt (𝓡 n) S.p Q)) 1)
      rw [hE] at hlow
      have h3 : S.c * ‖deriv (geo F S.D (extChartAt (𝓡 n) S.p P)
          (extChartAt (𝓡 n) S.p Q)) 1‖ ^ 2 < S.c * S.D.ρ ^ 2 := by linarith
      exact lt_of_pow_lt_pow_left₀ 2 S.D.ρ_pos.le (lt_of_mul_lt_mul_left h3 S.hc.le)
    rw [geo_reverse S.D hy hz hyz hzy hsmall s hs]

/-- The global curve-level short-segment map, with reversal symmetry. -/
theorem exists_segment_curves (F : ReversibleMetric n) :
    ∃ δ > 0, ∃ sc sv : Sphere n → Sphere n → ℝ → Ambient n,
      (∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
        ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
        (∀ t, ‖sc P Q t‖ = 1) ∧
        ∫ t in (0 : ℝ)..1, lagrangian F (sc P Q t, sv P Q t) = minEnergy F P Q) ∧
      (∀ P₀ Q₀ : Sphere n, ‖(Q₀ : Ambient n) - P₀‖ < δ → ∀ ε > 0,
        ∀ᶠ x : Sphere n × Sphere n in 𝓝 (P₀, Q₀), ∀ t ∈ Icc (0 : ℝ) 1,
          ‖sc x.1 x.2 t - sc P₀ Q₀ t‖ < ε ∧ ‖sv x.1 x.2 t - sv P₀ Q₀ t‖ < ε) ∧
      (∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
        sc Q P s = sc P Q (1 - s) ∧ sv Q P s = -sv P Q (1 - s)) ∧
      (∀ P : Sphere n, ∀ t, sc P P t = P) ∧
      ∀ (T : SegChart F) (P Q : Sphere n), P ∈ segDom T → ‖(Q : Ambient n) - P‖ < δ →
        ‖(Q : Ambient n) - P‖ < T.δ → ∀ t ∈ Icc (0 : ℝ) 1, sc P Q t = segCurve T P Q t := by
  obtain ⟨δ, hδ, ι, S, hcover, hδS, hcons⟩ := exists_segment_atlas F
  choose idx hidx hPidx using hcover
  obtain ⟨C, hC, hup⟩ := Finsler.SphereDistance.exists_minEnergy_upper F
  -- a Lebesgue number of the packages
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric (s := (univ : Set (Sphere n)))
    (c := fun i : ι => segDom (S i)) isCompact_univ (fun i => segDom_isOpen F (S i))
    (fun P _ => mem_iUnion.mpr ⟨⟨idx P, hidx P⟩, hPidx P⟩)
  -- thresholds for the reversal
  obtain ⟨c₀, C₀, hc₀, -, hb⟩ := Finsler.MetricComparison.exists_squared_bounds F
  have hthr : ∀ P₀ : Sphere n, ∃ τ > 0, ∀ x : ℝ, 0 ≤ x → x < τ →
      C * x ^ 2 < (S P₀).c * (S P₀).D.ρ ^ 2 ∧ C * x ^ 2 < c₀ * (S P₀).η ^ 2 := by
    intro P₀
    obtain ⟨τ₁, hτ₁, h₁⟩ := exists_threshold hC (mul_pos (S P₀).hc (pow_pos (S P₀).D.ρ_pos 2))
    obtain ⟨τ₂, hτ₂, h₂⟩ := exists_threshold hC (mul_pos hc₀ (pow_pos (S P₀).hη 2))
    exact ⟨min τ₁ τ₂, lt_min hτ₁ hτ₂, fun x hx hxτ =>
      ⟨h₁ x hx (hxτ.trans_le (min_le_left _ _)), h₂ x hx (hxτ.trans_le (min_le_right _ _))⟩⟩
  choose τ hτ hτC using hthr
  have hne : ι.Nonempty := ⟨idx (Finsler.SphereRetraction.northPole n), hidx _⟩
  set τ₀ := ι.inf' hne τ with hτ₀
  have hτ₀pos : 0 < τ₀ := (Finset.lt_inf'_iff hne).mpr fun P₀ _ => hτ P₀
  set δ' := min δ (min lam τ₀) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ (lt_min hlam hτ₀pos)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  refine ⟨δ', hδ'pos, fun P Q => segCurve (S (idx P)) P Q, fun P Q => segVel (S (idx P)) P Q,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q hQ
    have hQS := (hQ.trans_le hδ'δ).trans_le (hδS _ (hidx P))
    refine ⟨fun t ht => segCurve_hasDerivAt _ (hPidx P) hQS ht, fun t ht => ?_,
      segCurve_zero _ (hPidx P) Q, segCurve_one _ (hPidx P) hQS,
      fun t => mem_sphere_zero_iff_norm.mp (inverseSphere _ _).2,
      segCurve_energy _ (hPidx P) hQS⟩
    have h := (segCurve_continuousAt _ (hPidx P) hQS ht).2
    have h' : ContinuousAt (segVel (S (idx P)) P Q) t :=
      ContinuousAt.comp (g := fun q : (Sphere n × Sphere n) × ℝ =>
        segVel (S (idx P)) q.1.1 q.1.2 q.2) (f := fun s : ℝ => ((P, Q), s)) (x := t) h
        (continuousAt_const.prodMk continuousAt_id)
    exact h'.continuousWithinAt
  · intro P₀ Q₀ hQ₀' ε hε
    have hQ₀ := hQ₀'.trans_le hδ'δ
    have hP₀T : P₀ ∈ segDom (S (idx P₀)) := hPidx P₀
    have hQ₀T := hQ₀.trans_le (hδS _ (hidx P₀))
    have hev1 : ∀ᶠ x : Sphere n × Sphere n in 𝓝 (P₀, Q₀), x.1 ∈ segDom (S (idx P₀)) :=
      continuousAt_fst.preimage_mem_nhds ((segDom_isOpen F (S (idx P₀))).mem_nhds hP₀T)
    have hev2 : ∀ᶠ x : Sphere n × Sphere n in 𝓝 (P₀, Q₀), ‖(x.2 : Ambient n) - x.1‖ < δ :=
      (continuous_norm.comp ((continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp continuous_fst))).continuousAt.eventually (gt_mem_nhds hQ₀)
    have h1 := eventually_uniform (x₀ := (P₀, Q₀))
      (f := fun x t => segCurve (S (idx P₀)) x.1 x.2 t)
      (fun t ht => (segCurve_continuousAt _ hP₀T hQ₀T ht).1) hε
    have h2 := eventually_uniform (x₀ := (P₀, Q₀))
      (f := fun x t => segVel (S (idx P₀)) x.1 x.2 t)
      (fun t ht => (segCurve_continuousAt _ hP₀T hQ₀T ht).2) hε
    filter_upwards [hev1, hev2, h1, h2] with x hx1 hx2 hx3 hx4 t ht
    have hQT := hx2.trans_le (hδS _ (hidx P₀))
    have hQI := hx2.trans_le (hδS _ (hidx x.1))
    have hc : ∀ s ∈ Icc (0 : ℝ) 1,
        segCurve (S (idx x.1)) x.1 x.2 s = segCurve (S (idx P₀)) x.1 x.2 s :=
      fun s hs => hcons (idx P₀) (hidx P₀) (idx x.1) (hidx x.1) x.1 x.2 hx1 (hPidx x.1) hx2 s hs
    have hv := segVel_eq (hPidx x.1) hx1 hQI hQT hc ht
    have hc0 := hc t ht
    show ‖segCurve (S (idx x.1)) x.1 x.2 t - segCurve (S (idx P₀)) P₀ Q₀ t‖ < ε ∧
      ‖segVel (S (idx x.1)) x.1 x.2 t - segVel (S (idx P₀)) P₀ Q₀ t‖ < ε
    rw [hc0, hv]
    exact ⟨hx3 t ht, hx4 t ht⟩
  · intro P Q hQ
    -- a common package
    obtain ⟨i, hi⟩ := hleb P (mem_univ P)
    have hPi : P ∈ segDom (S i) := hi (Metric.mem_ball_self hlam)
    have hQi : Q ∈ segDom (S i) := by
      apply hi
      rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
      exact hQ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hQδ : ‖(Q : Ambient n) - P‖ < δ := hQ.trans_le hδ'δ
    have hPδ : ‖(P : Ambient n) - Q‖ < δ := by rwa [norm_sub_rev]
    have hQSi : ‖(Q : Ambient n) - P‖ < (S i).δ := hQδ.trans_le (hδS _ i.2)
    have hQ1 : ‖(Q : Ambient n) - P‖ ≤ 1 := hQSi.le.trans (S i).hδ1
    have hmin := (hup P Q (Finsler.ShortSegments.norm_sphere P)
      (Finsler.ShortSegments.norm_sphere Q) hQ1).2
    have hτi : ‖(Q : Ambient n) - P‖ < τ i :=
      hQ.trans_le (((min_le_right _ _).trans (min_le_right _ _)).trans (Finset.inf'_le _ i.2))
    have hρi := (hτC i _ (norm_nonneg _) hτi).1
    have hrev := segCurve_reverse (S i) hPi hQi hQSi hmin hρi
    -- the global segments are those of the common package
    have hPQ : ∀ s ∈ Icc (0 : ℝ) 1, segCurve (S (idx P)) P Q s = segCurve (S i) P Q s :=
      fun s hs => hcons i i.2 (idx P) (hidx P) P Q hPi (hPidx P) hQδ s hs
    have hQP : ∀ s ∈ Icc (0 : ℝ) 1, segCurve (S (idx Q)) Q P s = segCurve (S i) Q P s :=
      fun s hs => hcons i i.2 (idx Q) (hidx Q) Q P hQi (hPidx Q) hPδ s hs
    have hmem : ∀ s ∈ Icc (0 : ℝ) 1, 1 - s ∈ Icc (0 : ℝ) 1 :=
      fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hcurve : ∀ s ∈ Icc (0 : ℝ) 1,
        segCurve (S (idx Q)) Q P s = segCurve (S (idx P)) P Q (1 - s) := by
      intro s hs
      rw [hQP s hs, hrev s hs, hPQ (1 - s) (hmem s hs)]
    intro s hs
    refine ⟨hcurve s hs, ?_⟩
    -- velocities by uniqueness of derivatives within [0,1]
    have hPSi := hQδ.trans_le (hδS _ (hidx P))
    have hQSi' := hPδ.trans_le (hδS _ (hidx Q))
    have h1 := (segCurve_hasDerivAt _ (hPidx Q) hQSi' hs).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
    have h2 : HasDerivAt (fun s => segCurve (S (idx P)) P Q (1 - s))
        (-segVel (S (idx P)) P Q (1 - s)) s := by
      have hd := segCurve_hasDerivAt _ (hPidx P) hPSi (hmem s hs)
      exact HasDerivAt.comp_const_sub (1 : ℝ) s hd
    have h2' : HasDerivWithinAt (segCurve (S (idx Q)) Q P) (-segVel (S (idx P)) P Q (1 - s))
        (Icc (0 : ℝ) 1) s :=
      h2.hasDerivWithinAt.congr (fun x hx => hcurve x hx) (hcurve s hs)
    exact (uniqueDiffOn_Icc_zero_one s hs).eq_deriv _ h1 h2'
  · intro P t
    have hy := chart_mem_closedBall (S (idx P)) (hPidx P)
    show segCurve (S (idx P)) P P t = P
    unfold segCurve
    rw [chartNormalize_sphere, geo_self (S (idx P)).D hy]
    exact inverseAmbient_chart_of_dom (S (idx P)) (hPidx P)
  · intro T P Q hPT hQδ hQT t ht
    show segCurve (S (idx P)) P Q t = segCurve T P Q t
    have hQS : ‖(Q : Ambient n) - P‖ < (S (idx P)).δ :=
      (hQδ.trans_le hδ'δ).trans_le (hδS _ (hidx P))
    have hQ1 : ‖(Q : Ambient n) - P‖ ≤ 1 := hQT.le.trans T.hδ1
    have hmin := (hup P Q (Finsler.ShortSegments.norm_sphere P)
      (Finsler.ShortSegments.norm_sphere Q) hQ1).2
    have hτP : ‖(Q : Ambient n) - P‖ < τ (idx P) :=
      hQδ.trans_le (((min_le_right _ _).trans (min_le_right _ _)).trans
        (Finset.inf'_le _ (hidx P)))
    obtain ⟨hρ, hη⟩ := hτC (idx P) _ (norm_nonneg _) hτP
    exact seg_eq hPT (hPidx P) hQT hQS hc₀ (fun q => (hb q).1) hmin hη hρ t ht

end

end Finsler.SegmentCurves
