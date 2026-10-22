module

public import Finsler.Geometry.AmbientDescent
public import Finsler.Geometry.PolygonHessian
public import Finsler.Geometry.AmbientEnergyRegularity
public import Finsler.Analysis.IndexComparison
public import Finsler.Analysis.OperatorIndex

/-! The index of the penalized polygon energy at a stationary sphere polygon. The second
derivative of a function at a point defines a quadratic form. At a short stationary sphere
polygon q without zero edges, the negative index of inertia of the second derivative of the
penalized polygon energy on ambient polygons equals the index of q, defined by the Hessian of
the polygon energy in the Hilbert coordinates of q: the inverse coordinate map composes with the
penalized energy to the coordinate energy, and the coordinate map of the normalized polygon is a
retraction which does not increase the functions, because the penalty is nonnegative. Thus the
index theory of polygons in Hilbert coordinates applies to the penalized energy in the ambient
space, where rotations act linearly. -/

@[expose] public section

namespace Finsler.AmbientHessian

open Module QuadraticForm QuadraticMap Filter
open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth Finsler.PolygonChart
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.IndexComparison Finsler.OperatorIndex
open Finsler.AmbientPenalty Finsler.AmbientDescent Finsler.AmbientEnergyRegularity
open Finsler.SphereCoordinateEuler Finsler.PolygonEnergyGlobal
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section
set_option maxSynthPendingDepth 3

/-- The quadratic form of the second derivative of a function at a point. -/
def sndQuad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (p : E) :
    QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap (fderiv ℝ (fderiv ℝ f) p).toLinearMap₁₂

theorem sndQuad_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (p v : E) : sndQuad f p v = fderiv ℝ (fderiv ℝ f) p v v := rfl

variable {n N : ℕ} [NeZero N]

/-- The Hilbert coordinates of the normalization of an ambient polygon. -/
def chartN (q : ZMod N → Sphere n) (Q : ZMod N → Ambient n) : Model n N :=
  WithLp.toLp 2 (fun i => chartNormalize (q i) (Q i))

omit [NeZero N] in
theorem chartN_amb (q : ZMod N → Sphere n) : chartN q (amb q) = base q := by
  unfold chartN base
  congr 1
  funext i
  unfold chartNormalize
  rw [show amb q i = (q i : Ambient n) from rfl, normalize_inclusion]

omit [NeZero N] in
theorem amb_ne_zero (q : ZMod N → Sphere n) (i : ZMod N) : amb q i ≠ 0 := fun h => by
  have h1 := norm_amb q i
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem chartN_contDiffAt (q : ZMod N → Sphere n) : ContDiffAt ℝ ∞ (chartN q) (amb q) := by
  have hpi : ContDiffAt ℝ ∞ (fun Q : ZMod N → Ambient n => fun i => chartNormalize (q i) (Q i))
      (amb q) := by
    refine contDiffAt_pi.mpr fun i => ?_
    have hs : SphereRetraction.normalize (amb q i) ∈ (extChartAt (𝓡 n) (q i)).source := by
      rw [show amb q i = (q i : Ambient n) from rfl, normalize_inclusion]
      exact mem_extChartAt_source (q i)
    exact ContDiffAt.comp (x := amb q) (g := chartNormalize (q i))
      (f := fun Q : ZMod N → Ambient n => Q i)
      (chartNormalize_smoothAt (q i) (amb_ne_zero q i) hs)
      (contDiff_apply ℝ (Ambient n) i).contDiffAt
  exact ((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : ZMod N => Coordinates n)).symm.contDiff.contDiffAt).comp (amb q) hpi

/-- Near a sphere polygon, decoding the coordinates of the normalization gives the normalized
polygon. -/
theorem eventually_decode_chartN (q : ZMod N → Sphere n) :
    ∀ᶠ Q in 𝓝 (amb q), decode q (chartN q Q) = fun i => (SphereRetraction.normalize (Q i) : Ambient n) := by
  have hev : ∀ i : ZMod N, ∀ᶠ Q in 𝓝 (amb q),
      SphereRetraction.normalize (Q i) ∈ (extChartAt (𝓡 n) (q i)).source := by
    intro i
    have hc : ContinuousAt (fun Q : ZMod N → Ambient n => SphereRetraction.normalize (Q i)) (amb q) :=
      ContinuousAt.comp (g := SphereRetraction.normalize (n := n)) (f := fun Q : ZMod N → Ambient n => Q i)
        (normalize_smoothAt (amb_ne_zero q i)).continuousAt (continuous_apply i).continuousAt
    refine hc.eventually ((isOpen_extChartAt_source (I := 𝓡 n) (q i)).mem_nhds ?_)
    change SphereRetraction.normalize ((q i : Sphere n) : Ambient n) ∈ _
    rw [normalize_inclusion]
    exact mem_extChartAt_source (q i)
  filter_upwards [eventually_all.mpr hev] with Q hQ
  funext i
  exact congrArg Subtype.val ((extChartAt (𝓡 n) (q i)).left_inv (hQ i))

/-- The penalized energy of a decoded coordinate vector is the coordinate energy. -/
theorem pen_decode (F : ReversibleMetric n) (lam : ℝ) (q : ZMod N → Sphere n) (x : Model n N) :
    pen F N lam (decode q x) = PolygonChart.energy F q x := by
  unfold pen PolygonChart.energy
  have h0 : logPen (decode q x) = 0 := by
    unfold logPen
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [norm_decode, Real.log_one]
    norm_num
  rw [h0, mul_zero, add_zero]

/-- The negative index of inertia of the second derivative of the penalized energy at a short
stationary sphere polygon without zero edges is the index of the polygon. -/
theorem sigNeg_sndQuad_pen (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)
    (hc : PolyCritical F N q) {lam : ℝ} (hlam : 0 ≤ lam)
    (hs : (hessian F q).toLinearMap.IsSymmetric) :
    sigNeg (sndQuad (pen F N lam) (amb q)) = index F q hs := by
  have hf₁ : ContDiffAt ℝ 2 (PolygonChart.energy F q) (base q) :=
    (energy_contDiffAt F hδ hq hne).of_le (by norm_num)
  have hE : ContDiffAt ℝ 2 (polyEnergyN F N) (amb q) :=
    (polyEnergyN_contDiffAt F hδ hq hne).of_le (by norm_num)
  have hf₂ : ContDiffAt ℝ 2 (pen F N lam) (amb q) := by
    unfold pen
    exact hE.add (contDiffAt_const.mul ((logPen_contDiffAt (incl q)).of_le (by simp)))
  have h₁ : fderiv ℝ (PolygonChart.energy F q) (base q) = 0 :=
    fderiv_energy_eq_zero_of_polyCritical F hδ hq hne hc
  have hR : HasFDerivAt (decode q) (fderiv ℝ (decode q) (base q)) (base q) :=
    ((decode_contDiffAt q (base_mem_target q)).differentiableAt (by simp)).hasFDerivAt
  have hR0 : decode q (base q) = amb q := decode_base q
  have hρ : HasFDerivAt (chartN q) (fderiv ℝ (chartN q) (amb q)) (amb q) :=
    ((chartN_contDiffAt q).differentiableAt (by simp)).hasFDerivAt
  have hρ0 : chartN q (amb q) = base q := chartN_amb q
  have hcomp : ∀ᶠ x in 𝓝 (base q), pen F N lam (decode q x) = PolygonChart.energy F q x :=
    Eventually.of_forall fun x => pen_decode F lam q x
  have hle : ∀ᶠ Q in 𝓝 (amb q), PolygonChart.energy F q (chartN q Q) ≤ pen F N lam Q := by
    filter_upwards [eventually_decode_chartN q] with Q hQ
    have h1 : PolygonChart.energy F q (chartN q Q) = polyEnergyN F N Q := by
      unfold PolygonChart.energy
      rw [hQ, polyEnergyN_eq_normalize F Q]
      exact polyEnergyN_eq F N (fun i => norm_coe (SphereRetraction.normalize (Q i)))
    rw [h1]
    unfold pen
    linarith [mul_nonneg hlam (logPen_nonneg Q)]
  have heq : PolygonChart.energy F q (base q) = pen F N lam (amb q) := by
    rw [← hR0]
    exact (pen_decode F lam q (base q)).symm
  have h₂ : fderiv ℝ (pen F N lam) (amb q) = 0 :=
    fderiv_eq_zero_of_le hρ0 (hf₁.differentiableAt (by simp)) (hf₂.differentiableAt (by simp))
      h₁ hρ hle heq
  have hq₁ : ∀ v, quad (hessian F q) v =
      fderiv ℝ (fderiv ℝ (PolygonChart.energy F q)) (base q) v v := fun v => by
    rw [quad_apply]
    exact Hessian.inner_operator _ _ _ _
  have hidx : index F q hs = sigNeg (quad (hessian F q)) :=
    OperatorIndex.finrank_negative (hessian F q) hs
  rw [hidx]
  refine le_antisymm ?_ ?_
  · refine sigNeg_le_of_le _ _ (fderiv ℝ (chartN q) (amb q)).toLinearMap fun u => ?_
    change quad (hessian F q) (fderiv ℝ (chartN q) (amb q) u) ≤ sndQuad (pen F N lam) (amb q) u
    rw [hq₁, sndQuad_apply]
    exact sndDeriv_le_of_le hρ0 hf₁ hf₂ h₁ h₂ hρ hle heq u
  · refine sigNeg_le_of_le _ _ (fderiv ℝ (decode q) (base q)).toLinearMap fun v => ?_
    change sndQuad (pen F N lam) (amb q) (fderiv ℝ (decode q) (base q) v) ≤
      quad (hessian F q) v
    rw [hq₁, sndQuad_apply, sndDeriv_eq_of_comp hR0 hf₁ hf₂ h₁ h₂ hR hcomp v]

end

end Finsler.AmbientHessian
