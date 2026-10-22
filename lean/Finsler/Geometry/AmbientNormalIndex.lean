module

public import Finsler.Geometry.AmbientHessian
public import Finsler.Geometry.AmbientSymmetry
public import Finsler.Algebra.SymmetricBlocks

/-! The index of the penalized energy normal to the iterated polygons. The second derivative of
a composition with a continuous linear map is the second derivative at the image applied to the
images of the vectors. Hence the second derivative of a function which is invariant under a
linear map is invariant under this map at its fixed points, and the second derivative of the
penalized energy with m N vertices at an iterated polygon, restricted to iterated vectors, is m²
times the second derivative of the penalized energy with N vertices and weight λ / m. At the
iterate of a short stationary polygon without zero edges the negative index of inertia of the
second derivative of the penalized energy is therefore the sum of the index of the polygon and
of the negative index on the vectors whose sum over the rotations by the periods vanishes: the
negative index in the directions normal to the iterated polygons is the index of the iterate
minus the index of the polygon. -/

@[expose] public section

namespace Finsler.AmbientNormalIndex

open Module QuadraticForm QuadraticMap Filter
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth Finsler.PolygonIterate
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.AmbientPenalty Finsler.AmbientDescent
open Finsler.AmbientHessian Finsler.AmbientSymmetry Finsler.SymmetricBlocks
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

section Linear

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]

/-- The second derivative of a composition with a continuous linear map. -/
theorem sndDeriv_comp_linear {f : E₂ → ℝ} (L : E₁ →L[ℝ] E₂) {p : E₁}
    (hf : ContDiffAt ℝ 2 f (L p)) (v w : E₁) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) p v w = fderiv ℝ (fderiv ℝ f) (L p) (L v) (L w) := by
  have hev : ∀ᶠ y in 𝓝 (L p), DifferentiableAt ℝ f y := by
    have h1 : ∀ᶠ y in 𝓝 (L p), ContDiffAt ℝ 1 f y :=
      (hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).eventually (by simp)
    exact h1.mono fun y hy => hy.differentiableAt one_ne_zero
  have hev' : ∀ᶠ x in 𝓝 p, fderiv ℝ (f ∘ L) x =
      (ContinuousLinearMap.compL ℝ E₁ E₂ ℝ).flip L (fderiv ℝ f (L x)) := by
    have h2 := L.continuous.continuousAt.eventually hev
    exact h2.mono fun x hx => (hx.hasFDerivAt.comp x L.hasFDerivAt).fderiv
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (L p)) (L p) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hc : HasFDerivAt (fun x : E₁ => fderiv ℝ f (L x))
      ((fderiv ℝ (fderiv ℝ f) (L p)).comp L) p := hD.comp p L.hasFDerivAt
  have hpre : HasFDerivAt
      (fun x : E₁ => (ContinuousLinearMap.compL ℝ E₁ E₂ ℝ).flip L (fderiv ℝ f (L x)))
      (((ContinuousLinearMap.compL ℝ E₁ E₂ ℝ).flip L).comp
        ((fderiv ℝ (fderiv ℝ f) (L p)).comp L)) p :=
    ((ContinuousLinearMap.compL ℝ E₁ E₂ ℝ).flip L).hasFDerivAt.comp p hc
  have h3 : fderiv ℝ (fderiv ℝ (f ∘ L)) p =
      ((ContinuousLinearMap.compL ℝ E₁ E₂ ℝ).flip L).comp
        ((fderiv ℝ (fderiv ℝ f) (L p)).comp L) :=
    (hpre.congr_of_eventuallyEq hev').fderiv
  rw [h3]
  rfl

/-- The second derivative of a function which is invariant under a continuous linear map is
invariant under the map at a fixed point. -/
theorem sndDeriv_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (ρ : E →L[ℝ] E) (hinv : ∀ x, f (ρ x) = f x) {p : E} (hp : ρ p = p)
    (hf : ContDiffAt ℝ 2 f p) (v w : E) :
    fderiv ℝ (fderiv ℝ f) p (ρ v) (ρ w) = fderiv ℝ (fderiv ℝ f) p v w := by
  have hf' : ContDiffAt ℝ 2 f (ρ p) := by rw [hp]; exact hf
  have h := sndDeriv_comp_linear ρ hf' v w
  have he : f ∘ ρ = f := funext hinv
  rw [he, hp] at h
  exact h.symm

/-- The derivative of a nonzero multiple of a map, without differentiability assumptions. -/
theorem fderiv_const_smul_any {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) {c : ℝ} (hc : c ≠ 0) (p : E) :
    fderiv ℝ (fun x => c • g x) p = c • fderiv ℝ g p := by
  by_cases hg : DifferentiableAt ℝ g p
  · exact (hg.hasFDerivAt.const_smul c).fderiv
  · have hg' : ¬DifferentiableAt ℝ (fun x => c • g x) p := by
      intro hd
      apply hg
      have h2 : DifferentiableAt ℝ (fun x => c⁻¹ • (c • g x)) p := hd.const_smul c⁻¹
      have h3 : (fun x => c⁻¹ • (c • g x)) = g := by
        funext x
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rwa [h3] at h2
    rw [fderiv_zero_of_not_differentiableAt hg', fderiv_zero_of_not_differentiableAt hg,
      smul_zero]

end Linear

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N]

/-- The second derivative of the penalized energy at an iterated polygon on iterated vectors is
m² times the second derivative of the penalized energy with the weight divided by m. -/
theorem sndDeriv_iterate (F : ReversibleMetric n) (lam : ℝ) {Q : ZMod N → Ambient n}
    (hQ : ContDiffAt ℝ 2 (pen F (m * N) lam) (iterate m N Q))
    (v w : ZMod N → Ambient n) :
    fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (iterate m N Q) (iterate m N v) (iterate m N w) =
      (m : ℝ) ^ 2 * fderiv ℝ (fderiv ℝ (pen F N (lam / m))) Q v w := by
  have hm : (m : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne m))
  have h := sndDeriv_comp_linear (iterA (n := n) m N) (p := Q) hQ v w
  have he : (pen F (m * N) lam) ∘ (iterA (n := n) m N) =
      fun Q' : ZMod N → Ambient n => (m : ℝ) ^ 2 * pen F N (lam / m) Q' :=
    funext fun Q' => pen_iterate m N F lam Q'
  rw [he] at h
  have h1 : fderiv ℝ (fun Q' : ZMod N → Ambient n => (m : ℝ) ^ 2 * pen F N (lam / m) Q') =
      fun x => (m : ℝ) ^ 2 • fderiv ℝ (pen F N (lam / m)) x :=
    funext fun x => fderiv_const_smul_any (pen F N (lam / m)) hm x
  rw [h1] at h
  have h4 : fderiv ℝ (fun x : ZMod N → Ambient n => (m : ℝ) ^ 2 • fderiv ℝ (pen F N (lam / m)) x)
      Q = (m : ℝ) ^ 2 • fderiv ℝ (fderiv ℝ (pen F N (lam / m))) Q :=
    fderiv_const_smul_any (fderiv ℝ (pen F N (lam / m))) hm Q
  rw [h4] at h
  rw [show iterate m N Q = iterA (n := n) m N Q from rfl,
    show iterate m N v = iterA (n := n) m N v from rfl,
    show iterate m N w = iterA (n := n) m N w from rfl, ← h]
  rfl

/-- The rotation by one period as a linear map. -/
def rotL : (ZMod (m * N) → Ambient n) →ₗ[ℝ] (ZMod (m * N) → Ambient n) :=
  (rotA (n := n) (m * N) (N : ZMod (m * N))).toLinearMap

omit [NeZero m] [NeZero N] in
theorem rotL_apply (Q : ZMod (m * N) → Ambient n) :
    rotL m N Q = rotA (m * N) (N : ZMod (m * N)) Q := rfl

omit [NeZero m] [NeZero N] in
theorem rotL_pow_apply (j : ℕ) (Q : ZMod (m * N) → Ambient n) :
    ((rotL (n := n) m N) ^ j) Q =
      rotA (m * N) ((j : ZMod (m * N)) * (N : ZMod (m * N))) Q := by
  induction j with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, rotA_zero]
    rfl
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, rotL_apply, rotA_rotA, Nat.cast_succ, add_mul,
      one_mul]
    exact congrArg (fun t : ZMod (m * N) => rotA (m * N) t Q) (add_comm _ _)

omit [NeZero m] [NeZero N] in
/-- The m-th power of the rotation by one period is the identity. -/
theorem rotL_pow : (rotL (n := n) m N) ^ m = 1 := by
  refine LinearMap.ext fun Q => ?_
  rw [rotL_pow_apply, ← Nat.cast_mul, ZMod.natCast_self, rotA_zero]
  rfl

/-- The fixed vectors of the rotation by one period are the iterated vectors. -/
theorem fixed_rotL :
    fixed (rotL (n := n) m N) = LinearMap.range (iterA (n := n) m N).toLinearMap := by
  ext Q
  rw [mem_fixed, rotL_apply, rotA_eq_iff, LinearMap.mem_range]
  rfl

/-- At the iterate of a short stationary polygon without zero edges, the index of the iterate is
the index of the polygon plus the negative index of inertia of the second derivative of the
penalized energy on the vectors with vanishing sum over the rotations by the periods. -/
theorem index_iterate_eq_add (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {q₀ : ZMod N → Sphere n} (hq : ShortPolygon δ (iterate m N q₀))
    (hne : ∀ i, (iterate m N q₀) (i + 1) ≠ (iterate m N q₀) i)
    (hq₀ : ShortPolygon δ q₀) (hne₀ : ∀ i, q₀ (i + 1) ≠ q₀ i)
    (hc : PolyCritical F (m * N) (iterate m N q₀)) (hc₀ : PolyCritical F N q₀) {lam : ℝ}
    (hlam : 0 ≤ lam) (hs : (hessian F (iterate m N q₀)).toLinearMap.IsSymmetric)
    (hs₀ : (hessian F q₀).toLinearMap.IsSymmetric) :
    index F (iterate m N q₀) hs = index F q₀ hs₀ +
      sigNeg ((sndQuad (pen F (m * N) lam) (amb (iterate m N q₀))).restrict
        (normal (rotL (n := n) m N) m)) := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hp : amb (iterate m N q₀) = iterate m N (amb q₀) := rfl
  -- regularity at the iterated polygon
  have hE : ContDiffAt ℝ 2 (polyEnergyN F (m * N)) (amb (iterate m N q₀)) :=
    (polyEnergyN_contDiffAt F hδ hq hne).of_le (by norm_num)
  have hf : ContDiffAt ℝ 2 (pen F (m * N) lam) (amb (iterate m N q₀)) := by
    unfold pen
    exact hE.add (contDiffAt_const.mul
      ((logPen_contDiffAt (incl (iterate m N q₀))).of_le (by simp)))
  -- symmetry and invariance of the second derivative
  have hsym : ∀ v w : ZMod (m * N) → Ambient n,
      (fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))).toLinearMap₁₂ v w =
      (fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))).toLinearMap₁₂ w v :=
    fun v w => (hf.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq v w
  have hfix : rotA (m * N) (N : ZMod (m * N)) (amb (iterate m N q₀)) =
      amb (iterate m N q₀) := by
    rw [hp]
    exact rotA_iterate m N (amb q₀)
  have hinv : ∀ v w : ZMod (m * N) → Ambient n,
      (fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))).toLinearMap₁₂
        (rotL m N v) (rotL m N w) =
      (fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))).toLinearMap₁₂ v w :=
    fun v w => sndDeriv_invariant (rotA (n := n) (m * N) (N : ZMod (m * N)))
      (fun x => pen_rotA (m * N) F lam _ x) hfix hf v w
  have hsplit := sigNeg_eq_add (β := (fderiv ℝ (fderiv ℝ (pen F (m * N) lam))
    (amb (iterate m N q₀))).toLinearMap₁₂) hmpos (rotL_pow m N) hsym hinv
  -- the index of the iterate
  have hidx : sigNeg (sndQuad (pen F (m * N) lam) (amb (iterate m N q₀))) =
      index F (iterate m N q₀) hs := sigNeg_sndQuad_pen F hδ hq hne hc hlam hs
  -- the fixed part is the root
  have hlam₀ : 0 ≤ lam / m := div_nonneg hlam (Nat.cast_nonneg m)
  have hidx₀ : sigNeg (sndQuad (pen F N (lam / m)) (amb q₀)) = index F q₀ hs₀ :=
    sigNeg_sndQuad_pen F hδ hq₀ hne₀ hc₀ hlam₀ hs₀
  have hfixed : sigNeg ((sndQuad (pen F (m * N) lam) (amb (iterate m N q₀))).restrict
      (fixed (rotL (n := n) m N))) = sigNeg (sndQuad (pen F N (lam / m)) (amb q₀)) := by
    have hequiv : QuadraticMap.Equivalent ((m : ℝ) ^ 2 • sndQuad (pen F N (lam / m)) (amb q₀))
        ((sndQuad (pen F (m * N) lam) (amb (iterate m N q₀))).restrict
          (fixed (rotL (n := n) m N))) :=
      ⟨⟨(LinearEquiv.ofInjective (iterA (n := n) m N).toLinearMap (iterA_injective m N)).trans
          (LinearEquiv.ofEq _ _ (fixed_rotL m N).symm), fun v => by
        change sndQuad (pen F (m * N) lam) (amb (iterate m N q₀)) (iterA m N v) =
          (m : ℝ) ^ 2 • sndQuad (pen F N (lam / m)) (amb q₀) v
        rw [sndQuad_apply, sndQuad_apply, smul_eq_mul, hp]
        exact sndDeriv_iterate m N F lam (by rw [← hp]; exact hf) v v⟩⟩
    rw [← hequiv.sigNeg_eq, QuadraticForm.sigNeg_smul_of_pos _ hm2]
  rw [← hidx, ← hidx₀, ← hfixed]
  exact hsplit

end

end Finsler.AmbientNormalIndex
