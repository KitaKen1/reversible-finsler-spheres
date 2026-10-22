module

public import Finsler.Geometry.MilnorHomotopy
public import Mathlib.MeasureTheory.Function.Floor

/-! Continuity of the straightening homotopy. Convergence in the graph space follows from
convergence of the value at 0 and of the velocity in L². The velocity of the homotopy at (τ, u)
differs from the mixed velocity, which uses the velocity of the limit loop u₀ off the straightened
parts, by at most the difference of the velocities of u and u₀. For τ₀ > 0 the mixed velocities
converge by dominated convergence, since the segment velocities are bounded and converge off the
finitely many ends of the straightened parts. For τ₀ = 0 the straightened parts shrink to the
midpoints and the energy comparison bounds the squared velocity of the segments by the squared
velocity of the loop on these parts. -/

@[expose] public section

namespace Finsler.MilnorContinuity

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevEnergy Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.PiecewiseC1 Finsler.SobolevCircleRepresentative Finsler.SobolevOfPrimitive
open Finsler.MilnorHomotopy Finsler.AmbientLagrangian Finsler.SobolevCurveRealization
open Finsler.SobolevEnergyDifferential
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

/-- Convergence in the graph space from convergence of the value at 0 and of the velocity. -/
theorem tendsto_of_trace_velocity {X : Type*} {l : Filter X} {w : X → Space n} {w₀ : Space n}
    (h0 : Tendsto (fun x => continuousRepresentative (w x) 0) l
      (𝓝 (continuousRepresentative w₀ 0)))
    (hv : Tendsto (fun x => velocity (w x)) l (𝓝 (velocity w₀))) : Tendsto w l (𝓝 w₀) := by
  rw [tendsto_iff_value_velocity]
  refine ⟨?_, hv⟩
  rw [tendsto_iff_norm_sub_tendsto_zero] at h0 hv ⊢
  have hsum := h0.add hv
  rw [add_zero] at hsum
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) hsum
  have hval : value (w x) - value w₀ = value (w x - w₀) := ((valueL n).map_sub _ _).symm
  have hvel : velocity (w x) - velocity w₀ = velocity (w x - w₀) :=
    ((velocityL n).map_sub _ _).symm
  have htr : continuousRepresentative (w x) 0 - continuousRepresentative w₀ 0 =
      continuousRepresentative (w x - w₀) 0 := by
    have h := (traceZeroL n).map_sub (w x) w₀
    rw [traceZeroL_apply, traceZeroL_apply, traceZeroL_apply] at h
    unfold traceZero at h
    exact h.symm
  calc ‖value (w x) - value w₀‖ = ‖value (w x - w₀)‖ := congrArg norm hval
    _ ≤ ‖continuousRepresentative (w x - w₀) 0‖ + ‖velocity (w x - w₀)‖ := by
        apply valueLp_norm_le_of_ae_bound (by positivity)
        filter_upwards [value_ae_continuousRepresentative (w x - w₀),
          ae_restrict_mem measurableSet_Ioo] with t h1 ht
        refine (congrArg norm h1).trans_le ?_
        calc ‖continuousRepresentative (w x - w₀) t‖
            ≤ ‖continuousRepresentative (w x - w₀) 0‖ +
              ‖continuousRepresentative (w x - w₀) t - continuousRepresentative (w x - w₀) 0‖ :=
              norm_le_insert' _ _
          _ ≤ _ := add_le_add le_rfl (continuousRepresentative_increment_norm_le _ (by norm_num)
              (Ioo_subset_Icc_self ht))
    _ = _ := congrArg₂ (fun a b => ‖a‖ + ‖b‖) htr.symm hvel.symm

/-- Convergence of velocities from convergence of the integrals of the squared differences of
almost everywhere representatives. -/
theorem tendsto_velocity_of_integral {X : Type*} {l : Filter X} {w : X → Space n}
    {w₀ : Space n} {c : X → ℝ → Ambient n} {c₀ : ℝ → Ambient n}
    (hc : ∀ᶠ x in l, velocity (w x) =ᵐ[intervalMeasure] c x)
    (hc₀ : velocity w₀ =ᵐ[intervalMeasure] c₀)
    (hI : Tendsto (fun x => ∫ t, ‖c x t - c₀ t‖ ^ 2 ∂intervalMeasure) l (𝓝 0)) :
    Tendsto (fun x => velocity (w x)) l (𝓝 (velocity w₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : ∀ᶠ x in l, Real.sqrt (∫ t, ‖c x t - c₀ t‖ ^ 2 ∂intervalMeasure) =
      ‖velocity (w x) - velocity w₀‖ := by
    filter_upwards [hc] with x hx
    rw [lp_two_norm_eq_sqrt_integral_norm_sq]
    congr 1
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (velocity (w x)) (velocity w₀), hx, hc₀] with t h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hs := (Real.continuous_sqrt.tendsto 0).comp hI
  rw [Real.sqrt_zero] at hs
  exact hs.congr' h

/-- The squared L² distance of the velocities of two loops. -/
theorem integral_velocity_sub_sq (u v : Space n) :
    ∫ t, ‖velocity u t - velocity v t‖ ^ 2 ∂intervalMeasure = ‖velocity u - velocity v‖ ^ 2 := by
  rw [lp_two_norm_eq_sqrt_integral_norm_sq, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (velocity u) (velocity v)] with t h1
  rw [h1, Pi.sub_apply]

theorem integrable_velocity_sub_sq (u v : Space n) :
    Integrable (fun t => ‖velocity u t - velocity v t‖ ^ 2) intervalMeasure := by
  have h := (memLp_two_iff_integrable_sq_norm
    ((Lp.memLp (velocity u)).sub (Lp.memLp (velocity v))).aestronglyMeasurable).mp
    ((Lp.memLp (velocity u)).sub (Lp.memLp (velocity v)))
  exact h

theorem measurable_pieceIdx (N : ℕ) : Measurable (fun t : ℝ => (pieceIdx N t : ℝ)) := by
  have h1 : Measurable (fun t : ℝ => ⌊(N : ℝ) * t⌋₊) :=
    (Nat.measurable_floor (R := ℝ)).comp (measurable_const.mul measurable_id)
  have h2 : Measurable (fun k : ℕ => ((min k (N - 1) : ℕ) : ℝ)) := measurable_from_nat
  exact h2.comp h1

theorem measurable_pieceLoc (N : ℕ) : Measurable (pieceLoc N) :=
  (measurable_const.mul measurable_id).sub (measurable_pieceIdx N)

/-- The open straightened set. -/
def straight (N : ℕ) (τ : ℝ) : Set ℝ := {t | |pieceLoc N t - 1 / 2| < τ / 2}

theorem measurableSet_straight (N : ℕ) (τ : ℝ) : MeasurableSet (straight N τ) :=
  measurableSet_lt (continuous_abs.measurable.comp ((measurable_pieceLoc N).sub_const _))
    measurable_const

/-- The velocity of the homotopy of u with the velocity of w off the straightened parts. -/
def mixVel (sv : Sphere n → Sphere n → ℝ → Ambient n) (N : ℕ) (τ : ℝ) (u w : SphereLoop n)
    (t : ℝ) : Ambient n :=
  if |pieceLoc N t - 1 / 2| < τ / 2 then
    ((N : ℝ) / τ) •
      sv (pt u (leftEnd N τ (pieceIdx N t))) (pt u (rightEnd N τ (pieceIdx N t))) (segParam N τ t)
  else velocity (w.data : Space n) t

section Mix

variable {sv : Sphere n → Sphere n → ℝ → Ambient n} {N : ℕ} {τ : ℝ} {u w : SphereLoop n}

theorem mixVel_self : mixVel sv N τ u u = homVel sv N τ u := rfl

theorem homVel_of_lt (t : ℝ) (h : |pieceLoc N t - 1 / 2| < τ / 2) :
    homVel sv N τ u t = ((N : ℝ) / τ) •
      sv (pt u (leftEnd N τ (pieceIdx N t))) (pt u (rightEnd N τ (pieceIdx N t))) (segParam N τ t) := by
  unfold homVel
  exact ite_eq_left h

theorem homVel_of_not (t : ℝ) (h : ¬ |pieceLoc N t - 1 / 2| < τ / 2) :
    homVel sv N τ u t = velocity (u.data : Space n) t := by
  unfold homVel
  exact ite_eq_right h

theorem mixVel_of_not (t : ℝ) (h : ¬ |pieceLoc N t - 1 / 2| < τ / 2) :
    mixVel sv N τ u w t = velocity (w.data : Space n) t := by
  unfold mixVel
  exact ite_eq_right h

theorem mixVel_of_lt (t : ℝ) (h : |pieceLoc N t - 1 / 2| < τ / 2) :
    mixVel sv N τ u w t = ((N : ℝ) / τ) •
      sv (pt u (leftEnd N τ (pieceIdx N t))) (pt u (rightEnd N τ (pieceIdx N t))) (segParam N τ t) := by
  unfold mixVel
  exact ite_eq_left h

theorem mixVel_eq : mixVel sv N τ u w = homVel sv N τ u + (straight N τ)ᶜ.indicator
    (fun t => velocity (w.data : Space n) t - velocity (u.data : Space n) t) := by
  funext t
  show mixVel sv N τ u w t = homVel sv N τ u t + (straight N τ)ᶜ.indicator
    (fun t => velocity (w.data : Space n) t - velocity (u.data : Space n) t) t
  by_cases h : |pieceLoc N t - 1 / 2| < τ / 2
  · have hn : t ∉ (straight N τ)ᶜ := fun h' => h' h
    simp only [mixVel_of_lt (sv := sv) (u := u) (w := w) t h,
      homVel_of_lt (sv := sv) (u := u) t h, Set.indicator_of_notMem hn, add_zero]
  · have hm : t ∈ (straight N τ)ᶜ := h
    simp only [mixVel_of_not (sv := sv) (u := u) (w := w) t h,
      homVel_of_not (sv := sv) (u := u) t h, Set.indicator_of_mem hm, add_sub_cancel]

theorem norm_homVel_sub_mixVel_le (t : ℝ) :
    ‖homVel sv N τ u t - mixVel sv N τ u w t‖ ≤
      ‖velocity (u.data : Space n) t - velocity (w.data : Space n) t‖ := by
  by_cases h : |pieceLoc N t - 1 / 2| < τ / 2
  · simp only [mixVel_of_lt (sv := sv) (u := u) (w := w) t h,
      homVel_of_lt (sv := sv) (u := u) t h, sub_self, norm_zero]
    exact norm_nonneg _
  · exact (congrArg₂ (fun a b => ‖a - b‖) (homVel_of_not (sv := sv) (u := u) t h)
      (mixVel_of_not (sv := sv) (u := u) (w := w) t h)).le

theorem mixVel_zero (t : ℝ) : mixVel sv N 0 u w t = velocity (w.data : Space n) t := by
  apply mixVel_of_not
  rw [zero_div]
  exact not_lt.mpr (abs_nonneg _)

end Mix

theorem segParam_mem {N : ℕ} {τ t : ℝ} (hτ : 0 < τ) (h : |pieceLoc N t - 1 / 2| ≤ τ / 2) :
    segParam N τ t ∈ Icc (0 : ℝ) 1 := by
  rw [abs_le] at h
  unfold segParam
  constructor
  · apply div_nonneg _ hτ.le
    linarith
  · rw [div_le_one hτ]
    linarith

/-- Points where the straightened set of τ₀ has its boundary are ends of straightened parts. -/
theorem boundary_countable (N : ℕ) [NeZero N] (τ₀ : ℝ) :
    ({t : ℝ | |pieceLoc N t - 1 / 2| = τ₀ / 2}).Countable := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  apply ((countable_range (fun k : ℕ => leftEnd N τ₀ k)).union
    (countable_range (fun k : ℕ => rightEnd N τ₀ k))).mono
  intro t ht
  rcases (abs_eq (by
      have := abs_nonneg (pieceLoc N t - 1 / 2)
      rw [ht] at this
      exact this : (0 : ℝ) ≤ τ₀ / 2)).mp ht with h | h
  · exact Or.inr ⟨pieceIdx N t, (time_eq_rightEnd hN' h).symm⟩
  · exact Or.inl ⟨pieceIdx N t, (time_eq_leftEnd hN' h).symm⟩

/-- The midpoints of the pieces. -/
theorem midpoints_countable (N : ℕ) [NeZero N] :
    ({t : ℝ | pieceLoc N t = 1 / 2}).Countable := by
  have h := boundary_countable N 0
  apply h.mono
  intro t ht
  change pieceLoc N t = 1 / 2 at ht
  change |pieceLoc N t - 1 / 2| = 0 / 2
  rw [ht]
  norm_num

/-- Composition with a family converging uniformly on a set to a function continuous within it. -/
theorem tendsto_of_unif {X E : Type*} [TopologicalSpace X] [SeminormedAddCommGroup E]
    {f : X → ℝ → E} {g : ℝ → E} {x₀ : X} {s : X → ℝ} {s₀ : ℝ} {I : Set ℝ}
    (hunif : ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ∀ r ∈ I, ‖f x r - g r‖ < ε)
    (hg : ContinuousWithinAt g I s₀) (hs : Tendsto s (𝓝 x₀) (𝓝 s₀))
    (hsI : ∀ᶠ x in 𝓝 x₀, s x ∈ I) : Tendsto (fun x => f x (s x)) (𝓝 x₀) (𝓝 (g s₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hs' : Tendsto s (𝓝 x₀) (𝓝[I] s₀) := tendsto_nhdsWithin_iff.mpr ⟨hs, hsI⟩
  have h1 := (hg.tendsto.comp hs').eventually (Metric.ball_mem_nhds (g s₀) (half_pos hε))
  filter_upwards [h1, hunif (ε / 2) (half_pos hε), hsI] with x hx1 hx2 hx3
  have h2 := hx2 (s x) hx3
  have h3 : ‖g (s x) - g s₀‖ < ε / 2 := by
    have := Metric.mem_ball.mp hx1
    rwa [Function.comp_apply, dist_eq_norm] at this
  rw [dist_eq_norm]
  calc ‖f x (s x) - g s₀‖ = ‖(f x (s x) - g (s x)) + (g (s x) - g s₀)‖ := by
        congr 1
        abel
    _ ≤ ‖f x (s x) - g (s x)‖ + ‖g (s x) - g s₀‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h2 h3
    _ = ε := add_halves ε

/-- The ends of the straightened part of piece k as a pair of sphere points. -/
def ends (N k : ℕ) (p : ℝ × SphereLoop n) : Sphere n × Sphere n :=
  (pt p.2 (leftEnd N p.1 k), pt p.2 (rightEnd N p.1 k))

theorem pt_val (u : SphereLoop n) (x : ℝ) : (pt u x : Ambient n) = realMap u.data x := rfl

theorem pt_continuous {g : ℝ × SphereLoop n → ℝ} (hg : Continuous g) :
    Continuous (fun p : ℝ × SphereLoop n => pt p.2 (g p)) := by
  apply continuous_induced_rng.mpr
  have e : (Subtype.val ∘ fun p : ℝ × SphereLoop n => pt p.2 (g p)) =
      fun p => realMap p.2.data (g p) := funext fun p => pt_val _ _
  rw [e]
  have h1 := (realEvaluation_continuous n).comp
    (((sphereLoop_periodicData_continuous n).comp continuous_snd).prodMk hg)
  exact h1

theorem leftEnd_continuous (N k : ℕ) : Continuous (fun τ : ℝ => leftEnd N τ k) := by
  have hl : (fun τ : ℝ => leftEnd N τ k) = fun τ => ((k : ℝ) + 1 / 2 - τ / 2) / N := by
    funext τ
    unfold leftEnd
    rfl
  rw [hl]
  fun_prop

theorem rightEnd_continuous (N k : ℕ) : Continuous (fun τ : ℝ => rightEnd N τ k) := by
  have hr : (fun τ : ℝ => rightEnd N τ k) = fun τ => ((k : ℝ) + 1 / 2 + τ / 2) / N := by
    funext τ
    unfold rightEnd
    rfl
  rw [hr]
  fun_prop

theorem ends_continuous (N k : ℕ) : Continuous (ends (n := n) N k) :=
  (pt_continuous ((leftEnd_continuous N k).comp continuous_fst)).prodMk
    (pt_continuous ((rightEnd_continuous N k).comp continuous_fst))

theorem segParam_continuousAt {N : ℕ} (t : ℝ) {τ₀ : ℝ} (hτ₀ : τ₀ ≠ 0) :
    ContinuousAt (fun τ : ℝ => segParam N τ t) τ₀ := by
  have h : (fun τ : ℝ => segParam N τ t) = fun τ => (pieceLoc N t - (1 / 2 - τ / 2)) / τ := rfl
  rw [h]
  exact ((continuous_const.sub (continuous_const.sub (continuous_id.div_const 2))).continuousAt).div
    continuousAt_id hτ₀

/-- A bound of the mixed velocity from a bound of the segment velocities. -/
theorem norm_mixVel_le {sv : Sphere n → Sphere n → ℝ → Ambient n} {N : ℕ} [NeZero N] {τ M : ℝ}
    {u w : SphereLoop n} (hτ : 0 < τ) (hM0 : 0 ≤ M)
    (hM : ∀ k < N, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖sv (pt u (leftEnd N τ k)) (pt u (rightEnd N τ k)) s‖ ≤ M) (t : ℝ) :
    ‖mixVel sv N τ u w t‖ ≤ N / τ * M + ‖velocity (w.data : Space n) t‖ := by
  have hN := Nat.pos_of_neZero N
  by_cases h : |pieceLoc N t - 1 / 2| < τ / 2
  · have e := mixVel_of_lt (sv := sv) (u := u) (w := w) t h
    have hs := hM _ (pieceIdx_lt hN t) _ (segParam_mem hτ h.le)
    calc ‖mixVel sv N τ u w t‖ = ‖((N : ℝ) / τ) • sv (pt u (leftEnd N τ (pieceIdx N t)))
          (pt u (rightEnd N τ (pieceIdx N t))) (segParam N τ t)‖ := congrArg norm e
      _ = N / τ * ‖sv (pt u (leftEnd N τ (pieceIdx N t)))
          (pt u (rightEnd N τ (pieceIdx N t))) (segParam N τ t)‖ := by
          rw [norm_smul, Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hτ.le)]
      _ ≤ N / τ * M := mul_le_mul_of_nonneg_left hs (div_nonneg (Nat.cast_nonneg _) hτ.le)
      _ ≤ _ := le_add_of_nonneg_right (norm_nonneg _)
  · have e := mixVel_of_not (sv := sv) (u := u) (w := w) t h
    calc ‖mixVel sv N τ u w t‖ = ‖velocity (w.data : Space n) t‖ := congrArg norm e
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hτ.le) hM0)

section Positive

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F (sc P Q t, sv P Q t) =
      Finsler.SphereDistance.minEnergy F P Q)
  (hunif : ∀ P₀ Q₀ : Sphere n, ‖(Q₀ : Ambient n) - P₀‖ < δ → ∀ ε > 0,
    ∀ᶠ x : Sphere n × Sphere n in 𝓝 (P₀, Q₀), ∀ t ∈ Icc (0 : ℝ) 1,
      ‖sc x.1 x.2 t - sc P₀ Q₀ t‖ < ε ∧ ‖sv x.1 x.2 t - sv P₀ Q₀ t‖ < ε)
  {N : ℕ} [NeZero N] {a : ℝ}
  (hspace : ∀ u : SphereLoop n, energy F u < a ^ 2 →
    ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖continuousRepresentative (u.data : Space n) t -
        continuousRepresentative (u.data : Space n) s‖ < δ)
  {τ₀ : ℝ} {u₀ : SphereLoop n} (hu₀ : energy F u₀ < a ^ 2)

include hseg hunif hspace hu₀ in
/-- Inside the straightened set of τ₀ > 0 the mixed velocity converges. -/
theorem tendsto_mixVel_of_lt (hτ₀ : τ₀ ∈ Ioc (0 : ℝ) 1) {t : ℝ}
    (ht : |pieceLoc N t - 1 / 2| < τ₀ / 2) :
    Tendsto (fun p : ℝ × SphereLoop n => mixVel sv N p.1 p.2 u₀ t) (𝓝 (τ₀, u₀))
      (𝓝 (mixVel sv N τ₀ u₀ u₀ t)) := by
  have hN := Nat.pos_of_neZero N
  have hτI : τ₀ ∈ Icc (0 : ℝ) 1 := ⟨hτ₀.1.le, hτ₀.2⟩
  have hshort := chord_short F hspace hu₀ hτI (pieceIdx_lt hN t)
  have hev : ∀ᶠ p : ℝ × SphereLoop n in 𝓝 (τ₀, u₀), |pieceLoc N t - 1 / 2| < p.1 / 2 :=
    ((continuous_fst.div_const 2).tendsto (τ₀, u₀)).eventually (lt_mem_nhds ht)
  rw [mixVel_of_lt (sv := sv) (u := u₀) (w := u₀) t ht]
  refine Tendsto.congr' (f₁ := fun p : ℝ × SphereLoop n => ((N : ℝ) / p.1) •
    sv (ends N (pieceIdx N t) p).1 (ends N (pieceIdx N t) p).2 (segParam N p.1 t)) ?_ ?_
  · filter_upwards [hev] with p hp
    exact (mixVel_of_lt (sv := sv) (u := p.2) (w := u₀) t hp).symm
  · apply Tendsto.smul
    · have h : ContinuousAt (fun p : ℝ × SphereLoop n => (N : ℝ) / p.1) (τ₀, u₀) :=
        continuousAt_const.div continuous_fst.continuousAt hτ₀.1.ne'
      exact h.tendsto
    · apply tendsto_of_unif (I := Icc (0 : ℝ) 1)
      · intro ε hε
        have h := hunif _ _ hshort ε hε
        filter_upwards [((ends_continuous N (pieceIdx N t)).tendsto (τ₀, u₀)).eventually h]
          with p hp r hr
        exact (hp r hr).2
      · exact (hseg _ _ hshort).2.1 _ (segParam_mem hτ₀.1 ht.le)
      · exact (segParam_continuousAt t hτ₀.1.ne').tendsto.comp (continuous_fst.tendsto (τ₀, u₀))
      · filter_upwards [hev] with p hp
        have hp0 : 0 < p.1 := by
          have := abs_nonneg (pieceLoc N t - 1 / 2)
          linarith
        exact segParam_mem hp0 hp.le

include hseg hunif hspace hu₀ in
/-- Off the ends of the straightened parts the mixed velocity converges. -/
theorem ae_tendsto_mixVel (hτ₀ : τ₀ ∈ Ioc (0 : ℝ) 1) :
    ∀ᵐ t ∂intervalMeasure, Tendsto (fun p : ℝ × SphereLoop n => mixVel sv N p.1 p.2 u₀ t)
      (𝓝 (τ₀, u₀)) (𝓝 (mixVel sv N τ₀ u₀ u₀ t)) := by
  have hb := (boundary_countable N τ₀).ae_notMem volume
  filter_upwards [ae_restrict_of_ae hb] with t ht
  rcases lt_trichotomy (|pieceLoc N t - 1 / 2|) (τ₀ / 2) with h | h | h
  · exact tendsto_mixVel_of_lt F hseg hunif hspace hu₀ hτ₀ h
  · exact absurd h ht
  · have hev : ∀ᶠ p : ℝ × SphereLoop n in 𝓝 (τ₀, u₀), p.1 / 2 < |pieceLoc N t - 1 / 2| :=
      ((continuous_fst.div_const 2).tendsto (τ₀, u₀)).eventually (gt_mem_nhds h)
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := mixVel sv N τ₀ u₀ u₀ t))
    filter_upwards [hev] with p hp
    exact (mixVel_of_not (sv := sv) (u := u₀) (w := u₀) t (not_lt.mpr h.le)).trans
      (mixVel_of_not (sv := sv) (u := p.2) (w := u₀) t (not_lt.mpr hp.le)).symm

include hseg hspace in
theorem mixVel_aestronglyMeasurable {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) {u : SphereLoop n}
    (hu : energy F u < a ^ 2) (w : SphereLoop n) :
    AEStronglyMeasurable (mixVel sv N τ u w) intervalMeasure := by
  have h : AEStronglyMeasurable (homVel sv N τ u + (straight N τ)ᶜ.indicator
      (fun t => velocity (w.data : Space n) t - velocity (u.data : Space n) t)) intervalMeasure :=
    (homVel_memLp F hseg hspace hu hτ).aestronglyMeasurable.add
      (((Lp.aestronglyMeasurable (velocity (w.data : Space n))).sub
        (Lp.aestronglyMeasurable (velocity (u.data : Space n)))).indicator
        (measurableSet_straight N τ).compl)
  exact h.congr (mixVel_eq (sv := sv) (N := N) (τ := τ) (u := u) (w := w)).symm.eventuallyEq

include hseg hunif hspace hu₀ in
/-- For τ₀ > 0 the mixed velocities converge in L² by dominated convergence. -/
theorem tendsto_integral_mixVel_pos (hτ₀ : τ₀ ∈ Ioc (0 : ℝ) 1) :
    Tendsto (fun p : ℝ × SphereLoop n =>
      ∫ t, ‖mixVel sv N p.1 p.2 u₀ t - mixVel sv N τ₀ u₀ u₀ t‖ ^ 2 ∂intervalMeasure)
      (𝓝[Icc 0 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}] (τ₀, u₀)) (𝓝 0) := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hτI : τ₀ ∈ Icc (0 : ℝ) 1 := ⟨hτ₀.1.le, hτ₀.2⟩
  have hM : ∀ k ∈ Finset.range N, ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖sv (pt u₀ (leftEnd N τ₀ k)) (pt u₀ (rightEnd N τ₀ k)) s‖ ≤ M := fun k hk =>
    isCompact_Icc.exists_bound_of_continuousOn
      (hseg _ _ (chord_short F hspace hu₀ hτI (Finset.mem_range.mp hk))).2.1
  choose! M hM using hM
  obtain ⟨Mt, hMt⟩ : ∃ Mt : ℝ, Mt = ∑ k ∈ Finset.range N, |M k| + 1 := ⟨_, rfl⟩
  have hMt0 : 0 ≤ Mt := by
    rw [hMt]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) zero_le_one
  have hnear : ∀ᶠ p : ℝ × SphereLoop n in 𝓝 (τ₀, u₀), ∀ k ∈ Finset.range N,
      ∀ s ∈ Icc (0 : ℝ) 1, ‖sv (ends N k p).1 (ends N k p).2 s‖ ≤ Mt := by
    rw [Filter.eventually_all_finset]
    intro k hk
    have hshort := chord_short F hspace hu₀ hτI (Finset.mem_range.mp hk)
    filter_upwards [((ends_continuous N k).tendsto (τ₀, u₀)).eventually
      (hunif _ _ hshort 1 one_pos)] with p hp s hs
    have h1 := (hp s hs).2
    have h2 := hM k hk s hs
    have h3 : M k ≤ ∑ j ∈ Finset.range N, |M j| :=
      (le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |M j|) (fun _ _ => abs_nonneg _) hk)
    calc ‖sv (ends N k p).1 (ends N k p).2 s‖
        ≤ ‖sv (pt u₀ (leftEnd N τ₀ k)) (pt u₀ (rightEnd N τ₀ k)) s‖ +
          ‖sv (ends N k p).1 (ends N k p).2 s -
            sv (pt u₀ (leftEnd N τ₀ k)) (pt u₀ (rightEnd N τ₀ k)) s‖ := norm_le_insert' _ _
      _ ≤ M k + 1 := add_le_add h2 h1.le
      _ ≤ Mt := by rw [hMt]; linarith
  have hpos : ∀ᶠ p : ℝ × SphereLoop n in 𝓝 (τ₀, u₀), τ₀ / 2 < p.1 :=
    (continuous_fst.tendsto (τ₀, u₀)).eventually (lt_mem_nhds (half_lt_self hτ₀.1))
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * N / τ₀ * Mt := ⟨_, rfl⟩
  have hbd : ∀ p : ℝ × SphereLoop n, τ₀ / 2 < p.1 → (∀ k ∈ Finset.range N,
      ∀ s ∈ Icc (0 : ℝ) 1, ‖sv (ends N k p).1 (ends N k p).2 s‖ ≤ Mt) →
      ∀ t, ‖mixVel sv N p.1 p.2 u₀ t‖ ≤ B + ‖velocity (u₀.data : Space n) t‖ := by
    intro p hp hk t
    have hp0 : 0 < p.1 := by linarith [hτ₀.1]
    have h := norm_mixVel_le (sv := sv) (N := N) (u := p.2) (w := u₀) hp0 hMt0
      (fun k hk' s hs => hk k (Finset.mem_range.mpr hk') s hs) t
    have hle : (N : ℝ) / p.1 * Mt ≤ B := by
      rw [hB]
      apply mul_le_mul_of_nonneg_right _ hMt0
      rw [div_le_div_iff₀ hp0 hτ₀.1]
      nlinarith
    linarith
  have hD : ∀ᶠ p in 𝓝[Icc 0 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}] (τ₀, u₀),
      p ∈ Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2} := self_mem_nhdsWithin
  have key := tendsto_integral_filter_of_dominated_convergence (μ := intervalMeasure)
    (l := 𝓝[Icc 0 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}] (τ₀, u₀))
    (F := fun p t => ‖mixVel sv N p.1 p.2 u₀ t - mixVel sv N τ₀ u₀ u₀ t‖ ^ 2)
    (f := fun _ => (0 : ℝ))
    (fun t => 8 * B ^ 2 + 8 * ‖velocity (u₀.data : Space n) t‖ ^ 2) ?_ ?_ ?_ ?_
  · rwa [integral_zero] at key
  · filter_upwards [hD] with p hp
    exact (((mixVel_aestronglyMeasurable F hseg hspace hp.1 hp.2 u₀).sub
      (mixVel_aestronglyMeasurable F hseg hspace hτI hu₀ u₀)).norm).pow 2
  · filter_upwards [nhdsWithin_le_nhds hnear, nhdsWithin_le_nhds hpos] with p hp1 hp2
    refine Eventually.of_forall fun t => ?_
    have h1 := hbd p hp2 hp1 t
    have h2 := hbd (τ₀, u₀) (half_lt_self hτ₀.1) hnear.self_of_nhds t
    refine (Real.norm_of_nonneg (sq_nonneg _)).trans_le ?_
    have hv := norm_nonneg (velocity (u₀.data : Space n) t)
    calc ‖mixVel sv N p.1 p.2 u₀ t - mixVel sv N τ₀ u₀ u₀ t‖ ^ 2
        ≤ (‖mixVel sv N p.1 p.2 u₀ t‖ + ‖mixVel sv N τ₀ u₀ u₀ t‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      _ ≤ (2 * B + 2 * ‖velocity (u₀.data : Space n) t‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ ≤ 8 * B ^ 2 + 8 * ‖velocity (u₀.data : Space n) t‖ ^ 2 := by
          nlinarith [sq_nonneg (B - ‖velocity (u₀.data : Space n) t‖)]
  · exact (integrable_const _).add ((integrable_velocity_sq _).const_mul 8)
  · filter_upwards [ae_tendsto_mixVel F hseg hunif hspace hu₀ hτ₀] with t ht
    have ht' : Tendsto (fun p : ℝ × SphereLoop n => mixVel sv N p.1 p.2 u₀ t)
        (𝓝[Icc 0 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}] (τ₀, u₀))
        (𝓝 (mixVel sv N τ₀ u₀ u₀ t)) := ht.mono_left nhdsWithin_le_nhds
    have h := ((ht'.sub_const (mixVel sv N τ₀ u₀ u₀ t)).norm).pow 2
    have e : ‖mixVel sv N τ₀ u₀ u₀ t - mixVel sv N τ₀ u₀ u₀ t‖ ^ 2 = 0 := by simp
    rwa [e] at h

end Positive

theorem integral_intervalMeasure (f : ℝ → ℝ) :
    ∫ t, f t ∂intervalMeasure = ∫ t in (0 : ℝ)..1, f t := by
  change (∫ t in Ioo (0 : ℝ) 1, f t) = _
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

theorem intervalIntegrable_indicator {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s) {x₀ x₁ : ℝ}
    (hf : IntervalIntegrable f volume x₀ x₁) : IntervalIntegrable (s.indicator f) volume x₀ x₁ :=
  intervalIntegrable_iff.mpr ((intervalIntegrable_iff.mp hf).indicator hs)

theorem integrable_of_intervalIntegrable {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1) :
    Integrable f intervalMeasure :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hf

section Zero

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F (sc P Q t, sv P Q t) =
      Finsler.SphereDistance.minEnergy F P Q)
  {N : ℕ} [NeZero N] {a : ℝ}
  (hspace : ∀ u : SphereLoop n, energy F u < a ^ 2 →
    ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖continuousRepresentative (u.data : Space n) t -
        continuousRepresentative (u.data : Space n) s‖ < δ)
  {u : SphereLoop n} (hu : energy F u < a ^ 2) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)

include hseg hspace hu hτ in
theorem homLoop_mem : homLoop F hseg hspace hu hτ ∈ SpherePath n := fun _ ht =>
  (congrArg norm (representative_homLoop F hseg hspace hu hτ ht)).trans
    (norm_homVal F hseg hspace hu hτ ht)

include hseg hspace hu hτ in
theorem segLagrangian_continuousOn (hτ0 : 0 < τ) {k : ℕ} (hk : k < N) :
    ContinuousOn (fun t => lagrangian F (segC sc N τ u k t, segV sv N τ u k t))
      (Icc (leftEnd N τ k) (rightEnd N τ k)) := by
  intro t ht
  have hz : segC sc N τ u k t ≠ 0 := by
    intro h0
    have h1 := norm_segC F hseg hspace hu hτ hk t
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun x => (segC sc N τ u k x, segV sv N τ u k x)) (x := t)
    (lagrangian_continuousAt F (z := (segC sc N τ u k t, segV sv N τ u k t)) hz)
    ((segC_continuousOn F hseg hspace hu hτ hτ0 hk t ht).prodMk
      (segV_continuousOn F hseg hspace hu hτ hτ0 hk t ht))

include hseg hspace hu hτ in
theorem homLagrangian_part_integrable {j : ℕ} (hj : j < 3 * N) :
    IntervalIntegrable (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) volume
      (brk N τ j) (brk N τ (j + 1)) :=
  brk_part_integrable F hseg hspace hu hτ (Φ := fun x v => lagrangian F (x, v))
    (density_intervalIntegrable F (data_mem_spherePath u))
    (fun hτ0 _ hk => segLagrangian_continuousOn F hseg hspace hu hτ hτ0 hk) hj

include hseg hspace hu hτ in
theorem homLagrangian_intervalIntegrable :
    IntervalIntegrable (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) volume 0 1 :=
  homPair_intervalIntegrable F hseg hspace hu hτ (Φ := fun x v => lagrangian F (x, v))
    (density_intervalIntegrable F (data_mem_spherePath u))
    (fun hτ0 _ hk => segLagrangian_continuousOn F hseg hspace hu hτ hτ0 hk)

theorem indicator_congr_pt {s : Set ℝ} {f g : ℝ → ℝ} {t : ℝ} (h : f t = g t) :
    s.indicator f t = s.indicator g t := by
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, h]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]

include hseg hspace hu hτ in
/-- On every part the energy of the homotopy on the straightened set is at most that of the loop. -/
theorem brk_part_straight_le {j : ℕ} (hj : j < 3 * N) :
    ∫ t in (brk N τ j)..(brk N τ (j + 1)), (straight N τ).indicator
        (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t ≤
      ∫ t in (brk N τ j)..(brk N τ (j + 1)), (straight N τ).indicator (fun t => lagrangian F
        (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)) t := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hU : ∀ x₀ x₁ : ℝ, 0 ≤ x₀ → x₁ ≤ 1 → x₀ ≤ x₁ →
      (∀ t ∈ Icc x₀ x₁, τ / 2 ≤ |pieceLoc N t - 1 / 2|) →
      ∫ t in x₀..x₁, (straight N τ).indicator
          (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t ≤
        ∫ t in x₀..x₁, (straight N τ).indicator (fun t => lagrangian F
          (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)) t := by
    intro x₀ x₁ h0 h1 h01 hloc
    apply le_of_eq
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le h01] at ht
    exact indicator_congr_pt (congrArg₂ (fun x v => lagrangian F (x, v))
      (homVal_eq_rep F hseg hspace hu hτ ⟨h0.trans ht.1, ht.2.trans h1⟩ (hloc t ht))
      (homVel_eq_vel (hloc t ht)))
  have hB : ∀ k < N, ∫ t in (leftEnd N τ k)..(rightEnd N τ k), (straight N τ).indicator
          (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t ≤
        ∫ t in (leftEnd N τ k)..(rightEnd N τ k), (straight N τ).indicator (fun t => lagrangian F
          (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)) t := by
    intro k hk
    by_cases hτ0 : τ = 0
    · have e := rightEnd_eq_leftEnd (N := N) hτ0 k
      simp only [e, intervalIntegral.integral_same, le_refl]
    · have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτ0)
      have hlr := leftEnd_le_rightEnd hN' hτ.1 k
      have hmem : ∀ t ∈ Ioo (leftEnd N τ k) (rightEnd N τ k), t ∈ straight N τ :=
        fun t ht => (partB_facts hN' hτ hτpos hk ht).2.1
      calc ∫ t in (leftEnd N τ k)..(rightEnd N τ k), (straight N τ).indicator
            (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t
          = ∫ t in (leftEnd N τ k)..(rightEnd N τ k),
            lagrangian F (homVal sc N τ u t, homVel sv N τ u t) :=
            intervalIntegral.integral_congr_Ioo_of_le hlr fun t ht =>
              Set.indicator_of_mem (hmem t ht) _
        _ ≤ ∫ t in (leftEnd N τ k)..(rightEnd N τ k), lagrangian F
            (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t) :=
            partB_energy_le F hseg hspace hu hτ hk
        _ = _ := by
            have eu : ∫ t in (leftEnd N τ k)..(rightEnd N τ k), (straight N τ).indicator
                (fun t => lagrangian F (continuousRepresentative (u.data : Space n) t,
                  velocity (u.data : Space n) t)) t =
                ∫ t in (leftEnd N τ k)..(rightEnd N τ k), lagrangian F
                  (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t) :=
              intervalIntegral.integral_congr_Ioo_of_le hlr fun t ht =>
                Set.indicator_of_mem (hmem t ht) _
            exact eu.symm
  exact brk_induction (P := fun x₀ x₁ => ∫ t in x₀..x₁, (straight N τ).indicator
      (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t ≤
    ∫ t in x₀..x₁, (straight N τ).indicator (fun t => lagrangian F
      (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)) t)
    (fun k hk => hU _ _ (partA_bounds hN' hτ hk).1 (partA_bounds hN' hτ hk).2.1
      (partA_bounds hN' hτ hk).2.2 (fun t ht => loc_partA hN' hτ.1 hk ht))
    hB
    (fun k hk => hU _ _ (partC_bounds hN' hτ hk).1 (partC_bounds hN' hτ hk).2.1
      (partC_bounds hN' hτ hk).2.2 (fun t ht => loc_partC hN' hτ hk ht)) hj

include hseg hspace hu hτ in
/-- On the straightened set the energy of the homotopy is at most that of the loop. -/
theorem straight_energy_le :
    ∫ t, (straight N τ).indicator
        (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t ∂intervalMeasure ≤
      ∫ t, (straight N τ).indicator (fun t => lagrangian F
        (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)) t
        ∂intervalMeasure := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hS := measurableSet_straight N τ
  have hdens := density_intervalIntegrable F (data_mem_spherePath u)
  have hint1 : ∀ j < 3 * N, IntervalIntegrable ((straight N τ).indicator
      (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t))) volume
      (brk N τ j) (brk N τ (j + 1)) := fun j hj =>
    intervalIntegrable_indicator hS (homLagrangian_part_integrable F hseg hspace hu hτ hj)
  have hint2 : ∀ j < 3 * N, IntervalIntegrable ((straight N τ).indicator (fun t => lagrangian F
      (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t))) volume
      (brk N τ j) (brk N τ (j + 1)) := by
    intro j hj
    apply intervalIntegrable_indicator hS
    apply hdens.mono_set
    have h1 := brk_mem hτ hN (j := j) hj.le
    have h2 := brk_mem hτ hN (j := j + 1) hj
    have hm := brk_mono hτ hN' hj
    rw [uIcc_of_le zero_le_one, uIcc_of_le hm]
    exact Icc_subset_Icc h1.1 h2.2
  calc ∫ t, (straight N τ).indicator
        (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t ∂intervalMeasure
      = ∫ t in (0 : ℝ)..1, (straight N τ).indicator
          (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t :=
        integral_intervalMeasure _
    _ = ∑ j ∈ Finset.range (3 * N), ∫ t in (brk N τ j)..(brk N τ (j + 1)),
          (straight N τ).indicator
            (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t :=
        integral_eq_sum_brk hN hint1
    _ ≤ ∑ j ∈ Finset.range (3 * N), ∫ t in (brk N τ j)..(brk N τ (j + 1)),
          (straight N τ).indicator (fun t => lagrangian F
            (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)) t :=
        Finset.sum_le_sum fun j hj =>
          brk_part_straight_le F hseg hspace hu hτ (Finset.mem_range.mp hj)
    _ = ∫ t in (0 : ℝ)..1, (straight N τ).indicator (fun t => lagrangian F
            (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)) t :=
        (integral_eq_sum_brk hN hint2).symm
    _ = _ := (integral_intervalMeasure _).symm

include hseg hspace hu hτ in
/-- The squared velocity of the homotopy on the straightened set is controlled by that of the
loop. -/
theorem straight_velocity_sq_le {c C : ℝ}
    (hb : ∀ w ∈ SpherePath n, ∀ᵐ t ∂intervalMeasure,
      c * ‖velocity w t‖ ^ 2 ≤ lagrangian F (continuousRepresentative w t, velocity w t) ∧
      lagrangian F (continuousRepresentative w t, velocity w t) ≤ C * ‖velocity w t‖ ^ 2) :
    c * ∫ t, (straight N τ).indicator (fun t => ‖homVel sv N τ u t‖ ^ 2) t ∂intervalMeasure ≤
      C * ∫ t, (straight N τ).indicator (fun t => ‖velocity (u.data : Space n) t‖ ^ 2) t
        ∂intervalMeasure := by
  have hS := measurableSet_straight N τ
  have hw := homLoop_mem F hseg hspace hu hτ
  have h1 : ∀ᵐ t ∂intervalMeasure,
      c * (straight N τ).indicator (fun t => ‖homVel sv N τ u t‖ ^ 2) t ≤
        (straight N τ).indicator
          (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t := by
    filter_upwards [hb _ hw, velocity_homLoop_ae F hseg hspace hu hτ,
      ae_restrict_mem measurableSet_Ioo] with t h1 h2 ht
    have h3 : c * ‖homVel sv N τ u t‖ ^ 2 ≤
        lagrangian F (homVal sc N τ u t, homVel sv N τ u t) :=
      calc c * ‖homVel sv N τ u t‖ ^ 2
          = c * ‖velocity (homLoop F hseg hspace hu hτ) t‖ ^ 2 :=
            congrArg (fun x : Ambient n => c * ‖x‖ ^ 2) h2.symm
        _ ≤ _ := h1.1
        _ = _ := congrArg₂ (fun x v => lagrangian F (x, v))
            (representative_homLoop F hseg hspace hu hτ (Ioo_subset_Icc_self ht)) h2
    by_cases hs : t ∈ straight N τ
    · simp only [Set.indicator_of_mem hs]
      exact h3
    · simp only [Set.indicator_of_notMem hs, mul_zero, le_refl]
  have h2 : ∀ᵐ t ∂intervalMeasure, (straight N τ).indicator (fun t => lagrangian F
      (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)) t ≤
      C * (straight N τ).indicator (fun t => ‖velocity (u.data : Space n) t‖ ^ 2) t := by
    filter_upwards [hb _ (data_mem_spherePath u)] with t h
    by_cases hs : t ∈ straight N τ
    · simp only [Set.indicator_of_mem hs]
      exact h.2
    · simp only [Set.indicator_of_notMem hs, mul_zero, le_refl]
  have i1 : Integrable (fun t => (straight N τ).indicator (fun t => ‖homVel sv N τ u t‖ ^ 2) t)
      intervalMeasure :=
    ((memLp_two_iff_integrable_sq_norm (homVel_memLp F hseg hspace hu hτ).aestronglyMeasurable).mp
      (homVel_memLp F hseg hspace hu hτ)).indicator hS
  have i2 : Integrable (fun t => (straight N τ).indicator
      (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t) intervalMeasure :=
    (integrable_of_intervalIntegrable (homLagrangian_intervalIntegrable F hseg hspace hu hτ)).indicator hS
  have i3 : Integrable (fun t => (straight N τ).indicator (fun t => lagrangian F
      (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)) t)
      intervalMeasure :=
    (density_integrable F (data_mem_spherePath u)).indicator hS
  have i4 : Integrable (fun t => (straight N τ).indicator
      (fun t => ‖velocity (u.data : Space n) t‖ ^ 2) t) intervalMeasure :=
    (integrable_velocity_sq _).indicator hS
  calc c * ∫ t, (straight N τ).indicator (fun t => ‖homVel sv N τ u t‖ ^ 2) t ∂intervalMeasure
      = ∫ t, c * (straight N τ).indicator (fun t => ‖homVel sv N τ u t‖ ^ 2) t
          ∂intervalMeasure := (integral_const_mul _ _).symm
    _ ≤ ∫ t, (straight N τ).indicator
          (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) t ∂intervalMeasure :=
        integral_mono_ae (i1.const_mul c) i2 h1
    _ ≤ ∫ t, (straight N τ).indicator (fun t => lagrangian F
          (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)) t
          ∂intervalMeasure := straight_energy_le F hseg hspace hu hτ
    _ ≤ ∫ t, C * (straight N τ).indicator (fun t => ‖velocity (u.data : Space n) t‖ ^ 2) t
          ∂intervalMeasure := integral_mono_ae i3 (i4.const_mul C) h2
    _ = _ := integral_const_mul _ _

theorem alg_bound {X A V I J c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (ha : X ≤ 2 * A + 2 * J)
    (hAV : c * A ≤ C * V) (hV : V ≤ 2 * I + 2 * J) :
    X ≤ 4 * C / c * I + (4 * C / c + 2) * J := by
  have hA' : A ≤ C / c * V := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  have hCc : 0 ≤ C / c := div_nonneg hC hc.le
  have := mul_le_mul_of_nonneg_left hV hCc
  calc X ≤ 2 * A + 2 * J := ha
    _ ≤ 2 * (C / c * (2 * I + 2 * J)) + 2 * J := by linarith
    _ = 4 * C / c * I + (4 * C / c + 2) * J := by ring

theorem sq_norm_sub_le (x y : Ambient n) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 := norm_sub_le x y
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y), sq_nonneg (‖x‖ - ‖y‖)]

theorem sq_norm_le_sub (x y : Ambient n) : ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 := norm_le_insert' x y
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y), sq_nonneg (‖x - y‖ - ‖y‖)]

theorem mixVel_sub_pt {sv : Sphere n → Sphere n → ℝ → Ambient n} {N : ℕ} {τ : ℝ}
    (u u₀ : SphereLoop n) (t : ℝ) :
    ‖mixVel sv N τ u u₀ t - velocity (u₀.data : Space n) t‖ ^ 2 ≤
      2 * (straight N τ).indicator (fun t => ‖homVel sv N τ u t‖ ^ 2) t +
      2 * (straight N τ).indicator (fun t => ‖velocity (u₀.data : Space n) t‖ ^ 2) t := by
  by_cases hs : |pieceLoc N t - 1 / 2| < τ / 2
  · have e : mixVel sv N τ u u₀ t = homVel sv N τ u t :=
      (mixVel_of_lt (sv := sv) (u := u) (w := u₀) t hs).trans
        (homVel_of_lt (sv := sv) (u := u) t hs).symm
    have hs' : t ∈ straight N τ := hs
    simp only [e, Set.indicator_of_mem hs']
    exact sq_norm_sub_le _ _
  · have e : mixVel sv N τ u u₀ t = velocity (u₀.data : Space n) t :=
      mixVel_of_not (sv := sv) (u := u) (w := u₀) t hs
    have hs' : t ∉ straight N τ := hs
    simp only [e, sub_self, norm_zero, Set.indicator_of_notMem hs']
    norm_num

theorem straight_velocity_pt (N : ℕ) (τ : ℝ) (u u₀ : SphereLoop n) (t : ℝ) :
    (straight N τ).indicator (fun t => ‖velocity (u.data : Space n) t‖ ^ 2) t ≤
      2 * ‖velocity (u.data : Space n) t - velocity (u₀.data : Space n) t‖ ^ 2 +
      2 * (straight N τ).indicator (fun t => ‖velocity (u₀.data : Space n) t‖ ^ 2) t := by
  by_cases hs : t ∈ straight N τ
  · simp only [Set.indicator_of_mem hs]
    exact sq_norm_le_sub _ _
  · simp only [Set.indicator_of_notMem hs, mul_zero, add_zero]
    positivity

theorem integral_two_add {f g : ℝ → ℝ} (hf : Integrable f intervalMeasure)
    (hg : Integrable g intervalMeasure) :
    ∫ t, (2 * f t + 2 * g t) ∂intervalMeasure =
      2 * ∫ t, f t ∂intervalMeasure + 2 * ∫ t, g t ∂intervalMeasure :=
  (integral_add (hf.const_mul 2) (hg.const_mul 2)).trans
    (congrArg₂ (· + ·) (integral_const_mul _ _) (integral_const_mul _ _))

include hseg hspace hu hτ in
/-- The L² distance of the mixed velocity to the velocity of u₀ is controlled by the distance of
the velocities and the squared velocity of u₀ on the straightened set. -/
theorem integral_mixVel_le {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hb : ∀ w ∈ SpherePath n, ∀ᵐ t ∂intervalMeasure,
      c * ‖velocity w t‖ ^ 2 ≤ lagrangian F (continuousRepresentative w t, velocity w t) ∧
      lagrangian F (continuousRepresentative w t, velocity w t) ≤ C * ‖velocity w t‖ ^ 2)
    (u₀ : SphereLoop n) :
    ∫ t, ‖mixVel sv N τ u u₀ t - velocity (u₀.data : Space n) t‖ ^ 2 ∂intervalMeasure ≤
      4 * C / c * ∫ t, ‖velocity (u.data : Space n) t - velocity (u₀.data : Space n) t‖ ^ 2
        ∂intervalMeasure +
      (4 * C / c + 2) * ∫ t, (straight N τ).indicator
        (fun t => ‖velocity (u₀.data : Space n) t‖ ^ 2) t ∂intervalMeasure := by
  have hS := measurableSet_straight N τ
  have iH : Integrable (fun t => (straight N τ).indicator (fun t => ‖homVel sv N τ u t‖ ^ 2) t)
      intervalMeasure :=
    ((memLp_two_iff_integrable_sq_norm (homVel_memLp F hseg hspace hu hτ).aestronglyMeasurable).mp
      (homVel_memLp F hseg hspace hu hτ)).indicator hS
  have i0 : Integrable (fun t => (straight N τ).indicator
      (fun t => ‖velocity (u₀.data : Space n) t‖ ^ 2) t) intervalMeasure :=
    (integrable_velocity_sq _).indicator hS
  have ha := (integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
    ((iH.const_mul 2).add (i0.const_mul 2))
    (Eventually.of_forall fun t => mixVel_sub_pt (sv := sv) (N := N) (τ := τ) u u₀ t)).trans_eq
    (integral_two_add iH i0)
  have hV := (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
    (((integrable_velocity_sub_sq _ _).const_mul 2).add (i0.const_mul 2))
    (Eventually.of_forall fun t => straight_velocity_pt N τ u u₀ t)).trans_eq
    (integral_two_add (integrable_velocity_sub_sq _ _) i0)
  exact alg_bound hc hC ha (straight_velocity_sq_le F hseg hspace hu hτ hb) hV

/-- The squared velocity of a loop on the straightened set tends to 0 as τ → 0. -/
theorem tendsto_straight_zero (w : SphereLoop n) :
    Tendsto (fun τ : ℝ => ∫ t, (straight N τ).indicator
      (fun t => ‖velocity (w.data : Space n) t‖ ^ 2) t ∂intervalMeasure) (𝓝 0) (𝓝 0) := by
  have key := tendsto_integral_filter_of_dominated_convergence (μ := intervalMeasure)
    (l := 𝓝 (0 : ℝ))
    (F := fun τ t => (straight N τ).indicator (fun t => ‖velocity (w.data : Space n) t‖ ^ 2) t)
    (f := fun _ => (0 : ℝ)) (fun t => ‖velocity (w.data : Space n) t‖ ^ 2) ?_ ?_ ?_ ?_
  · rwa [integral_zero] at key
  · exact Eventually.of_forall fun τ =>
      ((integrable_velocity_sq _).indicator (measurableSet_straight N τ)).aestronglyMeasurable
  · refine Eventually.of_forall fun τ => Eventually.of_forall fun t => ?_
    exact (Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)).trans_le
      (Set.indicator_le_self' (fun _ _ => sq_nonneg _) t)
  · exact integrable_velocity_sq _
  · filter_upwards [ae_restrict_of_ae ((midpoints_countable N).ae_notMem volume)] with t ht
    have hpos : 0 < |pieceLoc N t - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr ht)
    have hev : ∀ᶠ τ : ℝ in 𝓝 0, τ / 2 < |pieceLoc N t - 1 / 2| :=
      ((continuous_id.div_const 2).tendsto 0).eventually (gt_mem_nhds (by simpa using hpos))
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards [hev] with τ hτ
    exact (Set.indicator_of_notMem (fun h : t ∈ straight N τ => absurd h (not_lt.mpr hτ.le)) _).symm

end Zero

theorem sq_norm_add_le (x y : Ambient n) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 := norm_add_le x y
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x + y), sq_nonneg (‖x‖ - ‖y‖)]

theorem homVel_sub_sq_le {sv : Sphere n → Sphere n → ℝ → Ambient n} {N : ℕ} {τ τ₀ : ℝ}
    (u u₀ : SphereLoop n) (t : ℝ) :
    ‖homVel sv N τ u t - homVel sv N τ₀ u₀ t‖ ^ 2 ≤
      2 * ‖velocity (u.data : Space n) t - velocity (u₀.data : Space n) t‖ ^ 2 +
      2 * ‖mixVel sv N τ u u₀ t - mixVel sv N τ₀ u₀ u₀ t‖ ^ 2 := by
  have h1 := norm_homVel_sub_mixVel_le (sv := sv) (N := N) (τ := τ) (u := u) (w := u₀) t
  have e2 : mixVel sv N τ₀ u₀ u₀ t = homVel sv N τ₀ u₀ t := rfl
  have e : homVel sv N τ u t - homVel sv N τ₀ u₀ t =
      (homVel sv N τ u t - mixVel sv N τ u u₀ t) +
        (mixVel sv N τ u u₀ t - mixVel sv N τ₀ u₀ u₀ t) := by
    rw [e2]
    abel
  have h3 := sq_norm_add_le (homVel sv N τ u t - mixVel sv N τ u u₀ t)
    (mixVel sv N τ u u₀ t - mixVel sv N τ₀ u₀ u₀ t)
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ‖homVel sv N τ u t - homVel sv N τ₀ u₀ t‖ ^ 2
      = ‖(homVel sv N τ u t - mixVel sv N τ u u₀ t) +
          (mixVel sv N τ u u₀ t - mixVel sv N τ₀ u₀ u₀ t)‖ ^ 2 := congrArg (fun x => ‖x‖ ^ 2) e
    _ ≤ _ := by linarith

section Homotopy

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F (sc P Q t, sv P Q t) =
      Finsler.SphereDistance.minEnergy F P Q)
  (hunif : ∀ P₀ Q₀ : Sphere n, ‖(Q₀ : Ambient n) - P₀‖ < δ → ∀ ε > 0,
    ∀ᶠ x : Sphere n × Sphere n in 𝓝 (P₀, Q₀), ∀ t ∈ Icc (0 : ℝ) 1,
      ‖sc x.1 x.2 t - sc P₀ Q₀ t‖ < ε ∧ ‖sv x.1 x.2 t - sv P₀ Q₀ t‖ < ε)
  {N : ℕ} [NeZero N] {a : ℝ}
  (hspace : ∀ u : SphereLoop n, energy F u < a ^ 2 →
    ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖continuousRepresentative (u.data : Space n) t -
        continuousRepresentative (u.data : Space n) s‖ < δ)

include hseg hspace in
theorem mixVel_memLp {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) {u : SphereLoop n}
    (hu : energy F u < a ^ 2) (w : SphereLoop n) :
    MemLp (mixVel sv N τ u w) 2 intervalMeasure := by
  have h : MemLp (homVel sv N τ u + (straight N τ)ᶜ.indicator
      (fun t => velocity (w.data : Space n) t - velocity (u.data : Space n) t)) 2
      intervalMeasure :=
    (homVel_memLp F hseg hspace hu hτ).add
      (((Lp.memLp (velocity (w.data : Space n))).sub (Lp.memLp (velocity (u.data : Space n)))).indicator
        (measurableSet_straight N τ).compl.nullMeasurableSet)
  exact h.ae_eq (mixVel_eq (sv := sv) (N := N) (τ := τ) (u := u) (w := w)).symm.eventuallyEq

open Classical in
/-- The straightening homotopy on [0,1] × {E < a²}, the loop itself elsewhere. -/
def milnorH (p : ℝ × SphereLoop n) : SphereLoop n :=
  if h : p.1 ∈ Icc (0 : ℝ) 1 ∧ energy F p.2 < a ^ 2 then
    homSphereLoop F hseg hspace h.2 h.1 else p.2

theorem milnorH_of_mem {p : ℝ × SphereLoop n}
    (h : p.1 ∈ Icc (0 : ℝ) 1 ∧ energy F p.2 < a ^ 2) :
    milnorH F hseg hspace p = homSphereLoop F hseg hspace h.2 h.1 := dite_eq_left h

theorem milnorH_data {p : ℝ × SphereLoop n}
    (h : p.1 ∈ Icc (0 : ℝ) 1 ∧ energy F p.2 < a ^ 2) :
    ((milnorH F hseg hspace p).data : Space n) = homLoop F hseg hspace h.2 h.1 :=
  congrArg (fun q : SphereLoop n => (q.data : Space n)) (milnorH_of_mem F hseg hspace h)

/-- At time 0 the homotopy is the identity. -/
theorem milnorH_zero {u : SphereLoop n} (hu : energy F u < a ^ 2) :
    milnorH F hseg hspace (0, u) = u :=
  (milnorH_of_mem F hseg hspace (p := (0, u)) ⟨⟨le_rfl, zero_le_one⟩, hu⟩).trans
    (homSphereLoop_zero F hseg hspace hu _ rfl)

/-- At time 1 the homotopy is the broken geodesic of the samples. -/
theorem milnorH_one {u : SphereLoop n} (hu : energy F u < a ^ 2) :
    milnorH F hseg hspace (1, u) = polySphereLoop F hseg (shortPolygon_samplePoly F hspace hu) :=
  (milnorH_of_mem F hseg hspace (p := (1, u)) ⟨⟨zero_le_one, le_rfl⟩, hu⟩).trans
    (homSphereLoop_one F hseg hspace hu _ rfl)

/-- The homotopy does not increase the energy. -/
theorem energy_milnorH_le {p : ℝ × SphereLoop n}
    (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}) :
    energy F (milnorH F hseg hspace p) ≤ energy F p.2 := by
  rw [milnorH_of_mem F hseg hspace ⟨hp.1, hp.2⟩]
  exact energy_homSphereLoop_le F hseg hspace hp.2 hp.1

/-- The squared L² distance of the velocities tends to 0. -/
theorem tendsto_velocity_dist (τ₀ : ℝ) (u₀ : SphereLoop n) :
    Tendsto (fun p : ℝ × SphereLoop n => ∫ t, ‖velocity (p.2.data : Space n) t -
      velocity (u₀.data : Space n) t‖ ^ 2 ∂intervalMeasure) (𝓝 (τ₀, u₀)) (𝓝 0) := by
  have h1 : Continuous (fun p : ℝ × SphereLoop n => velocity (p.2.data : Space n)) :=
    (velocityL n).continuous.comp ((sphereLoop_data_isometry n).continuous.comp continuous_snd)
  have h2 : Tendsto (fun p : ℝ × SphereLoop n =>
      ‖velocity (p.2.data : Space n) - velocity (u₀.data : Space n)‖ ^ 2) (𝓝 (τ₀, u₀))
      (𝓝 (‖velocity (u₀.data : Space n) - velocity (u₀.data : Space n)‖ ^ 2)) :=
    (((h1.sub (continuous_const (y := velocity (u₀.data : Space n)))).norm).pow 2).tendsto
      (τ₀, u₀)
  have e0 : ‖velocity (u₀.data : Space n) - velocity (u₀.data : Space n)‖ ^ 2 = 0 := by simp
  exact (h2.mono_right (congrArg 𝓝 e0).le).congr (fun p => (integral_velocity_sub_sq _ _).symm)

include hseg hspace in
/-- At τ₀ = 0 the mixed velocities converge to the velocity of u₀. -/
theorem tendsto_integral_mixVel_zero {u₀ : SphereLoop n} :
    Tendsto (fun p : ℝ × SphereLoop n =>
      ∫ t, ‖mixVel sv N p.1 p.2 u₀ t - mixVel sv N 0 u₀ u₀ t‖ ^ 2 ∂intervalMeasure)
      (𝓝[Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}] ((0 : ℝ), u₀)) (𝓝 0) := by
  obtain ⟨c, C, hc, hC, hb⟩ := SobolevSpherePath.exists_density_bounds F
  have hI1 : Tendsto (fun p : ℝ × SphereLoop n => ∫ t, ‖velocity (p.2.data : Space n) t -
      velocity (u₀.data : Space n) t‖ ^ 2 ∂intervalMeasure)
      (𝓝[Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}] ((0 : ℝ), u₀)) (𝓝 0) :=
    (tendsto_velocity_dist 0 u₀).mono_left nhdsWithin_le_nhds
  have hJ : Tendsto (fun p : ℝ × SphereLoop n => ∫ t, (straight N p.1).indicator
      (fun t => ‖velocity (u₀.data : Space n) t‖ ^ 2) t ∂intervalMeasure)
      (𝓝[Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}] ((0 : ℝ), u₀)) (𝓝 0) :=
    ((tendsto_straight_zero (N := N) u₀).comp (continuous_fst.tendsto ((0 : ℝ), u₀))).mono_left
      nhdsWithin_le_nhds
  have e : 4 * C / c * 0 + (4 * C / c + 2) * 0 = (0 : ℝ) := by ring
  have hbound := ((hI1.const_mul (4 * C / c)).add (hJ.const_mul (4 * C / c + 2))).mono_right
    (congrArg 𝓝 e).le
  refine squeeze_zero' (Eventually.of_forall fun p => integral_nonneg fun t => sq_nonneg _) ?_
    hbound
  filter_upwards [self_mem_nhdsWithin] with p hp
  have e' : ∀ t, mixVel sv N 0 u₀ u₀ t = velocity (u₀.data : Space n) t := fun t => mixVel_zero t
  calc ∫ t, ‖mixVel sv N p.1 p.2 u₀ t - mixVel sv N 0 u₀ u₀ t‖ ^ 2 ∂intervalMeasure
      = ∫ t, ‖mixVel sv N p.1 p.2 u₀ t - velocity (u₀.data : Space n) t‖ ^ 2
          ∂intervalMeasure := by simp only [e']
    _ ≤ _ := integral_mixVel_le F hseg hspace hp.2 hp.1 hc hC.le hb u₀

include hseg hunif hspace in
/-- The velocities of the homotopy converge in L². -/
theorem tendsto_integral_homVel {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Icc (0 : ℝ) 1) {u₀ : SphereLoop n}
    (hu₀ : energy F u₀ < a ^ 2) :
    Tendsto (fun p : ℝ × SphereLoop n =>
      ∫ t, ‖homVel sv N p.1 p.2 t - homVel sv N τ₀ u₀ t‖ ^ 2 ∂intervalMeasure)
      (𝓝[Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}] (τ₀, u₀)) (𝓝 0) := by
  have hI2 : Tendsto (fun p : ℝ × SphereLoop n =>
      ∫ t, ‖mixVel sv N p.1 p.2 u₀ t - mixVel sv N τ₀ u₀ u₀ t‖ ^ 2 ∂intervalMeasure)
      (𝓝[Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}] (τ₀, u₀)) (𝓝 0) := by
    rcases eq_or_lt_of_le hτ₀.1 with h0 | hpos
    · subst h0
      exact tendsto_integral_mixVel_zero F hseg hspace
    · exact tendsto_integral_mixVel_pos F hseg hunif hspace hu₀ ⟨hpos, hτ₀.2⟩
  have hI1 : Tendsto (fun p : ℝ × SphereLoop n => ∫ t, ‖velocity (p.2.data : Space n) t -
      velocity (u₀.data : Space n) t‖ ^ 2 ∂intervalMeasure)
      (𝓝[Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}] (τ₀, u₀)) (𝓝 0) :=
    (tendsto_velocity_dist τ₀ u₀).mono_left nhdsWithin_le_nhds
  have e : 2 * 0 + 2 * 0 = (0 : ℝ) := by ring
  have hsum := ((hI1.const_mul 2).add (hI2.const_mul 2)).mono_right (congrArg 𝓝 e).le
  refine squeeze_zero' (Eventually.of_forall fun p => integral_nonneg fun t => sq_nonneg _) ?_
    hsum
  filter_upwards [self_mem_nhdsWithin] with p hp
  have i1 := integrable_velocity_sub_sq (p.2.data : Space n) (u₀.data : Space n)
  have hm := (mixVel_memLp F hseg hspace hp.1 hp.2 u₀).sub (mixVel_memLp F hseg hspace hτ₀ hu₀ u₀)
  have i2 : Integrable (fun t => ‖mixVel sv N p.1 p.2 u₀ t - mixVel sv N τ₀ u₀ u₀ t‖ ^ 2)
      intervalMeasure := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  exact (integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
    ((i1.const_mul 2).add (i2.const_mul 2))
    (Eventually.of_forall fun t => homVel_sub_sq_le (sv := sv) (N := N) p.2 u₀ t)).trans_eq
    (integral_two_add i1 i2)

theorem trace_milnorH {p : ℝ × SphereLoop n}
    (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}) :
    continuousRepresentative ((milnorH F hseg hspace p).data : Space n) 0 =
      continuousRepresentative (p.2.data : Space n) 0 := by
  rw [milnorH_data F hseg hspace (p := p) ⟨hp.1, hp.2⟩,
    representative_homLoop F hseg hspace hp.2 hp.1 (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)]
  exact homVal_eq_rep F hseg hspace hp.2 hp.1 (by norm_num) (by
    rw [pieceLoc_zero, show |(0 : ℝ) - 1 / 2| = 1 / 2 by norm_num]
    linarith [hp.1.2])

include hunif in
/-- The straightening homotopy is continuous on [0,1] × {E < a²}. -/
theorem milnorH_continuousOn :
    ContinuousOn (milnorH F hseg hspace)
      (Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}) := by
  apply (sphereLoop_data_isometry n).isEmbedding.isInducing.continuousOn_iff.mpr
  rintro ⟨τ₀, u₀⟩ hp₀
  have hτ₀ : τ₀ ∈ Icc (0 : ℝ) 1 := hp₀.1
  have hu₀ : energy F u₀ < a ^ 2 := hp₀.2
  have hg : Continuous (fun p : ℝ × SphereLoop n =>
      continuousRepresentative (p.2.data : Space n) 0) :=
    (traceZeroL n).continuous.comp ((sphereLoop_data_isometry n).continuous.comp continuous_snd)
  show Tendsto (fun p => ((milnorH F hseg hspace p).data : Space n))
    (𝓝[Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}] (τ₀, u₀))
    (𝓝 ((milnorH F hseg hspace (τ₀, u₀)).data : Space n))
  apply tendsto_of_trace_velocity
  · rw [trace_milnorH F hseg hspace hp₀]
    refine Tendsto.congr' ?_ ((hg.tendsto (τ₀, u₀)).mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (trace_milnorH F hseg hspace hp).symm
  · apply tendsto_velocity_of_integral (c := fun p t => homVel sv N p.1 p.2 t)
      (c₀ := homVel sv N τ₀ u₀)
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact (Eq.eventuallyEq (congrArg (fun w : Space n => (velocity w : ℝ → Ambient n))
        (milnorH_data F hseg hspace (p := p) ⟨hp.1, hp.2⟩))).trans
        (velocity_homLoop_ae F hseg hspace hp.2 hp.1)
    · exact (Eq.eventuallyEq (congrArg (fun w : Space n => (velocity w : ℝ → Ambient n))
        (milnorH_data F hseg hspace (p := (τ₀, u₀)) ⟨hτ₀, hu₀⟩))).trans
        (velocity_homLoop_ae F hseg hspace hu₀ hτ₀)
    · exact tendsto_integral_homVel F hseg hunif hspace hτ₀ hu₀

end Homotopy

end

end Finsler.MilnorContinuity
