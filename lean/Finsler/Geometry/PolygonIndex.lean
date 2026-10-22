module

public import Finsler.Geometry.PolygonMonodromy
public import Finsler.Analysis.OperatorIndex
public import Finsler.Algebra.ChainForm

/-! The index of the iterates of a short polygon. In the Hilbert coordinates of a short polygon
without zero edges, the quadratic form of the Hessian of the coordinate energy is N times the
chain form of the pair forms (the quadratic forms of the second derivatives of the pair
energies), so the index of the polygon is the negative index of inertia of that chain form.
The pair forms of the m-fold iterate are the iterated pair forms. Hence the indices I(m) of the
iterates satisfy |I(m + k) - I(m) - I(k)| ≤ n, there is a mean index Δ ≥ 0 with
|I(m) - m Δ| ≤ n for all m ≥ 1, and |I(2 m) - 2 I(m)| ≤ n. The radius below which these
estimates hold for every polygon without zero edges is uniform. This is the first half of the
elementary iteration lemma for the index (in place of Bott's formula). No statement on local
cohomology is made. -/

@[expose] public section

namespace Finsler.PolygonIndex

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.EnergySphereSmooth Finsler.PolygonChart Finsler.PolygonHessian
open Finsler.PolygonNullity Finsler.PolygonIterate Finsler.PolygonIterateReduction
open Finsler.PolygonMonodromy
open Set Filter Module QuadraticMap
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n N : ℕ} [NeZero N]

/-- The pair form of the edge j: the quadratic form of the second derivative of the pair energy
at the central polygon. -/
def pairForm (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod N) :
    QuadraticForm ℝ (Coordinates n × Coordinates n) :=
  (hess2 F q j).toBilinForm.toQuadraticMap

omit [NeZero N] in
theorem pairForm_apply (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod N)
    (ζ : Coordinates n × Coordinates n) : pairForm F q j ζ = hess2 F q j ζ ζ := rfl

section Regular

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

include hδ hq hne in
/-- The quadratic form of the Hessian is N times the sum of the pair forms of the edges. -/
theorem inner_hessian_self (w : Model n N) :
    ⟪hessian F q w, w⟫ = N * ∑ j : ZMod N, pairForm F q j (w j, w (j + 1)) := by
  have hT : ∀ j : ZMod N, ⟪hessian F q w j, w j⟫ =
      N * (hess2 F q j (0, w (j + 1)) (w j, 0) +
        (hess2 F q j (w j, 0) (w j, 0) + hess2 F q (j - 1) (0, w j) (0, w j)) +
        hess2 F q (j - 1) (w (j - 1), 0) (0, w j)) := fun j => by
    rw [hessian_apply F hδ hq hne, real_inner_smul_left, inner_add_left, inner_add_left,
      inner_Tmap, inner_Amap, inner_Bmap]
  have hP : ∀ j : ZMod N, pairForm F q j (w j, w (j + 1)) =
      hess2 F q j (w j, 0) (w j, 0) + hess2 F q j (w j, 0) (0, w (j + 1)) +
        (hess2 F q j (0, w (j + 1)) (w j, 0) + hess2 F q j (0, w (j + 1)) (0, w (j + 1))) :=
    fun j => by
      have e : ((w j, w (j + 1)) : Coordinates n × Coordinates n) = (w j, 0) + (0, w (j + 1)) := by
        rw [Prod.mk_add_mk, add_zero, zero_add]
      rw [pairForm_apply, e]
      simp only [map_add, add_apply]
      ring
  have hD : ∑ j : ZMod N, hess2 F q (j - 1) (0, w j) (0, w j) =
      ∑ j : ZMod N, hess2 F q j (0, w (j + 1)) (0, w (j + 1)) :=
    Fintype.sum_equiv (Equiv.subRight 1) _ _ fun j => by
      change _ = hess2 F q (j - 1) (0, w (j - 1 + 1)) (0, w (j - 1 + 1))
      rw [sub_add_cancel]
  have hC : ∑ j : ZMod N, hess2 F q (j - 1) (w (j - 1), 0) (0, w j) =
      ∑ j : ZMod N, hess2 F q j (w j, 0) (0, w (j + 1)) :=
    Fintype.sum_equiv (Equiv.subRight 1) _ _ fun j => by
      change _ = hess2 F q (j - 1) (w (j - 1), 0) (0, w (j - 1 + 1))
      rw [sub_add_cancel]
  rw [PiLp.inner_apply]
  simp only [hT, hP, ← Finset.mul_sum, Finset.sum_add_distrib, hD, hC]
  ring

include hδ hq hne in
/-- **The index is the negative index of inertia of the chain form of the pair forms.** -/
theorem index_eq_sigNeg (hs : (hessian F q).toLinearMap.IsSymmetric) :
    index F q hs = sigNeg (ChainForm.form (pairForm F q)) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  let e := WithLp.linearEquiv 2 ℝ (ZMod N → Coordinates n)
  have hquad : OperatorIndex.quad (hessian F q) =
      (N : ℝ) • (ChainForm.form (pairForm F q)).comp e.toLinearMap := by
    ext w
    rw [OperatorIndex.quad_apply, inner_hessian_self F hδ hq hne, smul_apply,
      QuadraticMap.comp_apply, ChainForm.form_apply, smul_eq_mul]
    rfl
  have hequiv : QuadraticMap.Equivalent
      ((ChainForm.form (pairForm F q)).comp e.toLinearMap) (ChainForm.form (pairForm F q)) :=
    ⟨⟨e, fun _ => rfl⟩⟩
  rw [index, OperatorIndex.finrank_negative, hquad, QuadraticForm.sigNeg_smul_of_pos _ hN,
    hequiv.sigNeg_eq]

end Regular

/-! ### Iterates -/

/-- The pair forms of the iterate are the iterated pair forms. -/
theorem pairForm_iterate (F : ReversibleMetric n) (q : ZMod N → Sphere n) (m : ℕ) [NeZero m] :
    pairForm F (iterate m N q) = ChainForm.iter m N (pairForm F q) := by
  funext j
  rw [pairForm, hess2_iterate]
  rfl

/-- The index of the m-fold iterate as a function of m (zero for m = 0): the negative index of
inertia of the chain form of m periods of the pair forms. -/
def iterIndex (F : ReversibleMetric n) (q : ZMod N → Sphere n) (m : ℕ) : ℕ :=
  ChainForm.idx N (pairForm F q) m

/-- At a short polygon without zero edges, this function gives the indices of the iterates. -/
theorem iterIndex_eq (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i) (m : ℕ)
    [NeZero m] (hs : (hessian F (iterate m N q)).toLinearMap.IsSymmetric) :
    index F (iterate m N q) hs = iterIndex F q m := by
  rw [iterIndex, ChainForm.idx_eq, ← pairForm_iterate,
    index_eq_sigNeg F hδ (shortPolygon_iterate m N hq) (iterate_ne m N hne)]

/-- The index of the iterates is subadditive up to n. -/
theorem iterIndex_add_le (F : ReversibleMetric n) (q : ZMod N → Sphere n) {m k : ℕ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) :
    iterIndex F q (m + k) ≤ iterIndex F q m + iterIndex F q k + n := by
  have h := ChainForm.idx_add_le N (pairForm F q) hm hk
  rw [finrank_euclideanSpace_fin] at h
  exact h

/-- The index of the iterates is superadditive up to n. -/
theorem le_iterIndex_add (F : ReversibleMetric n) (q : ZMod N → Sphere n) {m k : ℕ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) :
    iterIndex F q m + iterIndex F q k ≤ iterIndex F q (m + k) + n := by
  have h := ChainForm.le_idx_add N (pairForm F q) hm hk
  rw [finrank_euclideanSpace_fin] at h
  exact h

/-- **The mean index.** There is Δ ≥ 0 with |I(m) - m Δ| ≤ n for all m ≥ 1. -/
theorem exists_mean (F : ReversibleMetric n) (q : ZMod N → Sphere n) :
    ∃ Δ : ℝ, 0 ≤ Δ ∧ ∀ m, 1 ≤ m → |(iterIndex F q m : ℝ) - m * Δ| ≤ n := by
  obtain ⟨Δ, hΔ, h⟩ := ChainForm.exists_mean N (pairForm F q)
  rw [finrank_euclideanSpace_fin] at h
  exact ⟨Δ, hΔ, h⟩

/-- The index of the iterate of even order compared with twice the index of its half. -/
theorem iterIndex_two_mul (F : ReversibleMetric n) (q : ZMod N → Sphere n) {m : ℕ}
    (hm : 1 ≤ m) :
    iterIndex F q (2 * m) ≤ 2 * iterIndex F q m + n ∧
      2 * iterIndex F q m ≤ iterIndex F q (2 * m) + n := by
  have h := ChainForm.idx_two_mul N (pairForm F q) hm
  rw [finrank_euclideanSpace_fin] at h
  exact h

/-- **Index estimates for the iterates, uniformly.** There is a positive radius below which,
for every polygon without zero edges with any number of vertices, the indices I(m) of the
m-fold iterates satisfy |I(m + k) - I(m) - I(k)| ≤ n, |I(m) - m Δ| ≤ n for a mean Δ ≥ 0, and
|I(2 m) - 2 I(m)| ≤ n. -/
theorem exists_index_mean (F : ReversibleMetric n) :
    ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (q : ZMod N → Sphere n), ShortPolygon δ q →
      (∀ i, q (i + 1) ≠ q i) →
      ∃ (I : ℕ → ℕ) (Δ : ℝ), 0 ≤ Δ ∧
        (∀ (m : ℕ) [NeZero m] (hs : (hessian F (iterate m N q)).toLinearMap.IsSymmetric),
          index F (iterate m N q) hs = I m) ∧
        (∀ m k, 1 ≤ m → 1 ≤ k → I (m + k) ≤ I m + I k + n ∧ I m + I k ≤ I (m + k) + n) ∧
        (∀ m, 1 ≤ m → |(I m : ℝ) - m * Δ| ≤ n) ∧
        ∀ m, 1 ≤ m → I (2 * m) ≤ 2 * I m + n ∧ 2 * I m ≤ I (2 * m) + n := by
  obtain ⟨δ, hδ, hs⟩ := exists_ambientMinEnergy_contDiffAt F
  refine ⟨δ, hδ, fun N _ q hq hne => ?_⟩
  obtain ⟨Δ, hΔ, hmean⟩ := exists_mean F q
  exact ⟨iterIndex F q, Δ, hΔ, fun m _ hsym => iterIndex_eq F hs hq hne m hsym,
    fun m k hm hk => ⟨iterIndex_add_le F q hm hk, le_iterIndex_add F q hm hk⟩, hmean,
    fun m hm => iterIndex_two_mul F q hm⟩

end

end Finsler.PolygonIndex
