module

public import Finsler.Geometry.PolygonTypes
public import Finsler.Geometry.PolygonIndex
public import Finsler.Analysis.MorseBott
public import Finsler.Analysis.InvariantIndex

/-! The Morse–Bott normal form of the energy of an iterated polygon along the iterated polygons.
In the Hilbert coordinates of the k-fold iterate of a short polygon q without zero edges, let K
be the space of the iterated vectors. The Hessian preserves K, and the component of the
gradient normal to K vanishes at the iterated points (symmetric criticality for the rotation by
one period). If the nullity of the iterate is at most the nullity of q, the kernel of the
Hessian lies in K, the normal block of the Hessian is nondegenerate, and near the centre the
coordinate energy of the iterate is k² times the coordinate energy of q at the first period of
the component in K, plus half the quadratic form of the Hessian at the normal component of a
C¹ chart tangent to the identity. The index of the iterate is the index of q plus the negative
index of the normal block; in particular the index does not decrease under iteration. With the
period L of the nullities, this applies to the k-fold iterate of the d-fold iterate whenever
gcd(d k, L) = gcd(d, L). These are the normal coordinates of the normal shift lemma; no
statement on local cohomology is made. -/

@[expose] public section

namespace Finsler.PolygonNormal

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.EnergySphereSmooth Finsler.PolygonChart Finsler.PolygonHessian
open Finsler.PolygonNullity Finsler.PolygonIterate Finsler.PolygonIterateReduction
open Finsler.MorseBott Finsler.OperatorIndex
open Set Filter Module QuadraticMap
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n : ℕ} (k N : ℕ) [NeZero k] [NeZero N]

/-- The first period of a family on the iterated chain. -/
def resL : Model n (k * N) →L[ℝ] Model n N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (fun j : ZMod N => y ((j.val : ℕ) : ZMod (k * N)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem resL_iterL (x : Model n N) : resL k N (iterL k N x) = x := by
  refine PiLp.ext fun j => ?_
  change x (red k N ((j.val : ℕ) : ZMod (k * N))) = x j
  rw [red_natCast, ZMod.natCast_zmod_val]

/-- The space of the iterated vectors. -/
def iterSpace : Submodule ℝ (Model n (k * N)) :=
  LinearMap.range (iterL (n := n) k N).toLinearMap

theorem iterL_mem (x : Model n N) : iterL k N x ∈ iterSpace (n := n) k N :=
  LinearMap.mem_range_self _ x

theorem iterL_resL {w : Model n (k * N)} (hw : w ∈ iterSpace k N) :
    iterL k N (resL k N w) = w := by
  obtain ⟨x, rfl⟩ := hw
  change iterL k N (resL k N (iterL k N x)) = iterL k N x
  rw [resL_iterL]

/-- The normal form of the coordinate energy of the k-fold iterate along the iterated vectors:
k² times the coordinate energy of the polygon plus half the quadratic form of the Hessian in the
normal component of a chart tangent to the identity. -/
def HasNormalForm (F : ReversibleMetric n) (q : ZMod N → Sphere n) : Prop :=
  ∃ Ξ : Model n (k * N) → Model n (k * N), ContDiffAt ℝ 1 Ξ 0 ∧ Ξ 0 = 0 ∧
    HasStrictFDerivAt Ξ (ContinuousLinearMap.id ℝ (Model n (k * N))) 0 ∧
    (∀ᶠ z in 𝓝 (0 : Model n (k * N)),
      tanProj (iterSpace k N) (Ξ z) = tanProj (iterSpace k N) z) ∧
    ∀ᶠ z in 𝓝 (0 : Model n (k * N)),
      energy F (iterate k N q) (base (iterate k N q) + z) =
        (k : ℝ) ^ 2 * energy F q (base q + resL k N (tanProj (iterSpace k N) z)) +
          1 / 2 * ⟪hessian F (iterate k N q) (norProj (iterSpace k N) (Ξ z)),
            norProj (iterSpace k N) (Ξ z)⟫

section Regular

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

include hδ hq hne in
/-- The Hessian of the iterate preserves the iterated vectors. -/
theorem hessian_mem (v : Model n (k * N)) (hv : v ∈ iterSpace k N) :
    hessian F (iterate k N q) v ∈ iterSpace k N := by
  obtain ⟨x, rfl⟩ := hv
  change hessian F (iterate k N q) (iterL k N x) ∈ _
  rw [hessian_iterate k N F hδ hq hne]
  exact Submodule.smul_mem _ _ (iterL_mem k N _)

include hδ hq hne in
/-- If the nullity does not increase, the kernel of the Hessian of the iterate consists of
iterated vectors. -/
theorem ker_le (hnull : nullity F (iterate k N q) ≤ nullity F q) :
    LinearMap.ker (hessian F (iterate k N q)).toLinearMap ≤ iterSpace k N := by
  intro κ hκ
  obtain ⟨w, -, rfl⟩ := exists_of_nullity_le k N F hδ hq hne hnull (LinearMap.mem_ker.mp hκ)
  exact iterL_mem k N w

include hδ hq hne in
/-- Symmetric criticality: at the iterated points near the centre the gradient is an iterated
vector. -/
theorem eventually_norProj_grad :
    ∀ᶠ w in 𝓝 (0 : Model n (k * N)), w ∈ iterSpace k N →
      norProj (iterSpace k N) (grad F (iterate k N q) (base (iterate k N q) + w)) = 0 := by
  have ht : Tendsto (fun w : Model n (k * N) => base q + resL k N w) (𝓝 0) (𝓝 (base q)) := by
    have h : ContinuousAt (fun w : Model n (k * N) => base q + resL k N w) 0 :=
      continuousAt_const.add (resL k N).continuous.continuousAt
    have h' := h.tendsto
    rwa [map_zero, add_zero] at h'
  filter_upwards [ht.eventually (eventually_grad_iterate k N F hδ hq hne)] with w hw hwK
  have e : base (iterate k N q) + w = iterL k N (base q + resL k N w) := by
    rw [map_add, iterL_resL k N hwK, base_iterate]
  rw [e, hw]
  exact norProj_of_mem _ (Submodule.smul_mem _ _ (iterL_mem k N _))

include hδ hq hne in
/-- **The normal form along the iterated polygons.** -/
theorem hasNormalForm (hnull : nullity F (iterate k N q) ≤ nullity F q) :
    HasNormalForm k N F q := by
  have hq' := shortPolygon_iterate k N hq
  have hne' := iterate_ne k N hne
  obtain ⟨Ξ, hΞ1, hΞ0, hΞd, hΞP, hΞf⟩ := MorseBott.exists_normal_form
    (K := iterSpace k N) (A := hessian F (iterate k N q)) (G := grad F (iterate k N q))
    (p := base (iterate k N q)) (f := energy F (iterate k N q))
    (hessian_isSymmetric F hδ hq' hne') (hessian_mem k N F hδ hq hne)
    (ker_le k N F hδ hq hne hnull) (grad_contDiffAt F hδ hq' hne')
    (grad_hasFDerivAt F hδ hq' hne') (eventually_hasFDerivAt F hδ hq' hne')
    (eventually_norProj_grad k N F hδ hq hne)
  refine ⟨Ξ, hΞ1, hΞ0, hΞd, hΞP, hΞf.mono fun z hz => ?_⟩
  have e : base (iterate k N q) + tanProj (iterSpace k N) z =
      iterL k N (base q + resL k N (tanProj (iterSpace k N) z)) := by
    rw [map_add, iterL_resL k N (tanProj_mem _ z), base_iterate]
  have hz' : energy F (iterate k N q) (base (iterate k N q) + z) =
      energy F (iterate k N q) (base (iterate k N q) + tanProj (iterSpace k N) z) +
        1 / 2 * ⟪hessian F (iterate k N q) (norProj (iterSpace k N) (Ξ z)),
          norProj (iterSpace k N) (Ξ z)⟫ := hz
  rw [hz', e, energy_iterate]

include hδ hq hne in
/-- If the nullity does not increase, the normal block of the Hessian is nondegenerate. -/
theorem normal_nondegenerate (hnull : nullity F (iterate k N q) ≤ nullity F q)
    {ν : Model n (k * N)} (hν : ν ∈ (iterSpace k N)ᗮ)
    (h : hessian F (iterate k N q) ν = 0) : ν = 0 := by
  have hK : ν ∈ iterSpace k N := ker_le k N F hδ hq hne hnull (LinearMap.mem_ker.mpr h)
  exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hK hν)

include hδ hq hne in
/-- **The index of the iterate** is the index of the polygon plus the negative index of the
normal block of the Hessian. -/
theorem index_iterate_eq (hs₀ : (hessian F q).toLinearMap.IsSymmetric)
    (hs : (hessian F (iterate k N q)).toLinearMap.IsSymmetric) :
    index F (iterate k N q) hs = index F q hs₀ +
      sigNeg ((quad (hessian F (iterate k N q))).restrict (iterSpace k N)ᗮ) := by
  have hk : (0 : ℝ) < (k : ℝ) * k := by
    have h : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
    positivity
  have hK : sigNeg ((quad (hessian F (iterate k N q))).restrict (iterSpace k N)) =
      sigNeg (quad (hessian F q)) :=
    InvariantIndex.sigNeg_restrict_range (hessian F q) (iterL k N).toLinearMap
      (iterL_injective k N) hk (fun w => by
        rw [quad_apply, quad_apply]
        change ⟪hessian F (iterate k N q) (iterL k N w), iterL k N w⟫ = _
        rw [hessian_iterate k N F hδ hq hne, real_inner_smul_left, inner_iterL]
        ring)
  rw [index, index, OperatorIndex.finrank_negative, OperatorIndex.finrank_negative,
    InvariantIndex.sigNeg_quad_eq_add hs (hessian_mem k N F hδ hq hne), hK]

include hδ hq hne in
/-- The index does not decrease under iteration. -/
theorem index_le_iterate (hs₀ : (hessian F q).toLinearMap.IsSymmetric)
    (hs : (hessian F (iterate k N q)).toLinearMap.IsSymmetric) :
    index F q hs₀ ≤ index F (iterate k N q) hs := by
  rw [index_iterate_eq k N F hδ hq hne hs₀ hs]
  exact Nat.le_add_right _ _

end Regular

/-- **Normal coordinates for all iterates, uniformly.** There is a positive radius below which
every polygon without zero edges, with any number of vertices, has a period L ≥ 1 such that,
whenever gcd(d k, L) = gcd(d, L), the energy of the k-fold iterate of the d-fold iterate has the
normal form along the iterated vectors, and the normal block of its Hessian is
nondegenerate. -/
theorem exists_normal_forms (F : ReversibleMetric n) :
    ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (q : ZMod N → Sphere n), ShortPolygon δ q →
      (∀ i, q (i + 1) ≠ q i) →
      ∃ L : ℕ, 1 ≤ L ∧ ∀ (d k : ℕ) [NeZero d] [NeZero k], Nat.gcd (d * k) L = Nat.gcd d L →
        HasNormalForm k (d * N) F (iterate d N q) ∧
        ∀ ν : Model n (k * (d * N)), ν ∈ (iterSpace k (d * N))ᗮ →
          hessian F (iterate k (d * N) (iterate d N q)) ν = 0 → ν = 0 := by
  obtain ⟨δ₁, hδ₁, hper⟩ := PolygonMonodromy.exists_nullity_period F
  obtain ⟨δ₂, hδ₂, hs⟩ := exists_ambientMinEnergy_contDiffAt F
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun N _ q hq hne => ?_⟩
  have hq₁ : ShortPolygon δ₁ q := fun i => (hq i).trans_le (min_le_left _ _)
  have hq₂ : ShortPolygon δ₂ q := fun i => (hq i).trans_le (min_le_right _ _)
  obtain ⟨L, hL, -, hnull⟩ := hper N q hq₁ hne
  refine ⟨L, hL, fun d k _ _ hg => ?_⟩
  have hqd := shortPolygon_iterate d N hq₂
  have hned := iterate_ne d N hne
  exact ⟨hasNormalForm k (d * N) F hs hqd hned (hnull d k hg).le,
    fun ν hν h => normal_nondegenerate k (d * N) F hs hqd hned (hnull d k hg).le hν h⟩

end

end Finsler.PolygonNormal
