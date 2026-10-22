module

public import Finsler.Geometry.AmbientNullity
public import Finsler.Geometry.AmbientNormalIndex

/-! Nondegeneracy of the penalized energy normal to the iterated polygons. At the iterate of a
short stationary polygon without zero edges, the second derivative of the penalized energy with
m N vertices is symmetric and invariant under the rotation by one period, and iteration maps the
kernel of the second derivative of the penalized energy of the polygon into its kernel. If the
iterate has the nullity of the polygon, the two kernels have the same dimension, so the kernel
at the iterate consists of iterated vectors; hence a vector with vanishing sum over the
rotations by the periods which is orthogonal to all such vectors vanishes: the second
derivative is nondegenerate in the directions normal to the iterated polygons. -/

@[expose] public section

namespace Finsler.AmbientNormalNondeg

open Module Filter
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth Finsler.PolygonIterate
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.AmbientPenalty Finsler.AmbientDescent
open Finsler.AmbientHessian Finsler.AmbientSymmetry Finsler.SymmetricBlocks
open Finsler.AmbientNormalIndex Finsler.AmbientNullity
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N]

/-- The penalized energy is C² at a short sphere polygon without zero edges. -/
theorem pen_contDiffAt_two (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {K : ℕ} [NeZero K] {q : ZMod K → Sphere n} (hq : ShortPolygon δ q)
    (hne : ∀ i, q (i + 1) ≠ q i) (lam : ℝ) : ContDiffAt ℝ 2 (pen F K lam) (amb q) := by
  have hE : ContDiffAt ℝ 2 (polyEnergyN F K) (amb q) :=
    (polyEnergyN_contDiffAt F hδ hq hne).of_le (by norm_num)
  unfold pen
  exact hE.add (contDiffAt_const.mul ((logPen_contDiffAt (incl q)).of_le (by simp)))

/-- The second derivative of the penalized energy at an iterated polygon is invariant under the
rotation by one period. -/
theorem sndDeriv_rotL (F : ReversibleMetric n) (lam : ℝ) (q₀ : ZMod N → Sphere n)
    (hf : ContDiffAt ℝ 2 (pen F (m * N) lam) (amb (iterate m N q₀)))
    (v w : ZMod (m * N) → Ambient n) :
    fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀)) (rotL m N v) (rotL m N w) =
      fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀)) v w := by
  have hp : amb (iterate m N q₀) = iterate m N (amb q₀) := rfl
  have hfix : rotA (m * N) (N : ZMod (m * N)) (amb (iterate m N q₀)) =
      amb (iterate m N q₀) := by
    rw [hp]
    exact rotA_iterate m N (amb q₀)
  exact sndDeriv_invariant (rotA (n := n) (m * N) (N : ZMod (m * N)))
    (fun x => pen_rotA (m * N) F lam _ x) hfix hf v w

/-- At the iterate of a short stationary polygon without zero edges with the nullity of the
polygon, the second derivative of the penalized energy is nondegenerate on the vectors with
vanishing sum over the rotations by the periods. -/
theorem normal_nondegenerate (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {q₀ : ZMod N → Sphere n} (hq : ShortPolygon δ (iterate m N q₀))
    (hne : ∀ i, (iterate m N q₀) (i + 1) ≠ (iterate m N q₀) i)
    (hq₀ : ShortPolygon δ q₀) (hne₀ : ∀ i, q₀ (i + 1) ≠ q₀ i)
    (hc : PolyCritical F (m * N) (iterate m N q₀)) (hc₀ : PolyCritical F N q₀) {lam : ℝ}
    (hlam : 0 < lam) (hnull : nullity F (iterate m N q₀) = nullity F q₀)
    {v : ZMod (m * N) → Ambient n} (hv : v ∈ normal (rotL (n := n) m N) m)
    (h : ∀ w ∈ normal (rotL (n := n) m N) m,
      fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀)) v w = 0) : v = 0 := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hmpos
  have hlam₀ : 0 < lam / m := div_pos hlam hmR
  have hp : amb (iterate m N q₀) = iterate m N (amb q₀) := rfl
  have hf := pen_contDiffAt_two F hδ hq hne lam
  have hsym : ∀ v w : ZMod (m * N) → Ambient n,
      (fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))).toLinearMap₁₂ v w =
      (fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))).toLinearMap₁₂ w v :=
    fun v w => (hf.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq v w
  have hinv : ∀ v w : ZMod (m * N) → Ambient n,
      (fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))).toLinearMap₁₂
        (rotL m N v) (rotL m N w) =
      (fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))).toLinearMap₁₂ v w :=
    fun v w => sndDeriv_rotL m N F lam q₀ hf v w
  -- the vector lies in the kernel of the second derivative
  have hker : v ∈ LinearMap.ker
      (fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))).toLinearMap₁₂ := by
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun x => ?_
    exact form_eq_zero_of_normal hmpos (rotL_pow m N) hsym hinv hv h x
  -- iteration maps the kernel for the polygon into the kernel for the iterate
  have hmap : (LinearMap.ker
      (fderiv ℝ (fderiv ℝ (pen F N (lam / m))) (amb q₀)).toLinearMap₁₂).map
      (iterA (n := n) m N).toLinearMap ≤ LinearMap.ker
      (fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))).toLinearMap₁₂ := by
    rintro _ ⟨v₀, hv₀, rfl⟩
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun x => ?_
    obtain ⟨u, w, hu, hw, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp (isCompl hmpos (rotL_pow (n := n) m N)).2 x
    rw [fixed_rotL] at hu
    obtain ⟨x₀, rfl⟩ := hu
    have h1 : fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))
        (iterA m N v₀) (iterA m N x₀) = 0 := by
      have h2 := sndDeriv_iterate m N F lam (Q := amb q₀) (by rw [← hp]; exact hf) v₀ x₀
      rw [show iterate m N v₀ = iterA (n := n) m N v₀ from rfl,
        show iterate m N x₀ = iterA (n := n) m N x₀ from rfl, ← hp] at h2
      rw [h2]
      have h3 : (fderiv ℝ (fderiv ℝ (pen F N (lam / m))) (amb q₀)).toLinearMap₁₂ v₀ = 0 :=
        LinearMap.mem_ker.mp hv₀
      have h5 : fderiv ℝ (fderiv ℝ (pen F N (lam / m))) (amb q₀) v₀ x₀ = 0 :=
        LinearMap.congr_fun h3 x₀
      rw [h5, mul_zero]
    have h4 : fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))
        (iterA m N v₀) w = 0 :=
      form_eq_zero _ hmpos hinv (rotA_iterate m N v₀) ((mem_normal _ _ _).mp hw)
    change fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀)) (iterA m N v₀)
      (iterA m N x₀ + w) = 0
    rw [map_add, h1, h4, add_zero]
  -- the two kernels have the same dimension
  have hdim : finrank ℝ ((LinearMap.ker
      (fderiv ℝ (fderiv ℝ (pen F N (lam / m))) (amb q₀)).toLinearMap₁₂).map
      (iterA (n := n) m N).toLinearMap) = finrank ℝ (LinearMap.ker
      (fderiv ℝ (fderiv ℝ (pen F (m * N) lam)) (amb (iterate m N q₀))).toLinearMap₁₂) := by
    rw [finrank_ker_sndDeriv_pen F hδ hq hne hc hlam, hnull,
      ← finrank_ker_sndDeriv_pen F hδ hq₀ hne₀ hc₀ hlam₀]
    exact (Submodule.equivMapOfInjective _ (iterA_injective m N) _).finrank_eq.symm
  have heq := Submodule.eq_of_le_of_finrank_eq hmap hdim
  rw [← heq] at hker
  obtain ⟨v₀, -, rfl⟩ := hker
  -- an iterated vector with vanishing orbit sum vanishes
  have hfix : iterA (n := n) m N v₀ ∈ fixed (rotL (n := n) m N) := by
    rw [fixed_rotL]
    exact ⟨v₀, rfl⟩
  exact Submodule.disjoint_def.mp (isCompl hmpos (rotL_pow (n := n) m N)).1 _ hfix hv

end

end Finsler.AmbientNormalNondeg
