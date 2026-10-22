module

public import Finsler.Geometry.PolygonHessian
public import Finsler.Geometry.PolygonIterate
public import Finsler.Algebra.JacobiRecursion

/-! The nullity of the Hessian of the polygon energy is at most 2 n under the twist condition.
In the Hilbert coordinates of a short polygon without zero edges, the coordinate energy is N
times the sum over the edges of the pair energies, each depending on the coordinates of the two
ends of the edge. The derivative of the coordinate energy in a direction supported at one vertex
involves only the two edges at that vertex. Hence, if a vector of the kernel of the Hessian
vanishes at the vertices j - 1 and j, the mixed second derivative of the pair energy of the
edge from j to j + 1 annihilates its component at j + 1; under the twist condition (the mixed
second derivative is nondegenerate) this component vanishes. By the propagation lemma the
kernel is determined by the components at two consecutive vertices, so the nullity is at most
2 n. The twist condition is a hypothesis; it is not proved here. -/

@[expose] public section

namespace Finsler.PolygonNullity

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.EnergySphereSmooth Finsler.PolygonChart Finsler.PolygonHessian
open Set Filter Module
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n N : ℕ} [NeZero N]

/-- The energy of the edge from the vertex i to the vertex i + 1, in the coordinates of its two
ends. -/
def pairE (F : ReversibleMetric n) (q : ZMod N → Sphere n) (i : ZMod N)
    (z : Coordinates n × Coordinates n) : ℝ :=
  ambientMinEnergy F (inverseAmbient (q i) z.1, inverseAmbient (q (i + 1)) z.2)

/-- The coordinates of the two ends of the edge from i to i + 1. -/
def edgeL (i : ZMod N) : Model n N →L[ℝ] Coordinates n × Coordinates n :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ZMod N => Coordinates n) i).prod
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ZMod N => Coordinates n) (i + 1))

omit [NeZero N] in
theorem edgeL_apply (i : ZMod N) (x : Model n N) : edgeL i x = (x i, x (i + 1)) := rfl

/-- The coordinate energy is N times the sum of the pair energies of the edges. -/
theorem energy_eq_sum (F : ReversibleMetric n) (q : ZMod N → Sphere n) (x : Model n N) :
    energy F q x = N * ∑ i : ZMod N, pairE F q i (edgeL i x) := by
  rw [PolygonIterate.sum_univ_eq_sum_range]
  rfl

section Regular

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

include hδ hq hne in
/-- The pair energies are C³ at the central polygon. -/
theorem pairE_contDiffAt (i : ZMod N) : ContDiffAt ℝ 3 (pairE F q i) (edgeL i (base q)) := by
  have h1 : ContDiffAt ℝ 3 (ambientMinEnergy F) ((q i : Ambient n), (q (i + 1) : Ambient n)) :=
    hδ (q i) (q (i + 1)) (hne i) (hq i)
  have hb : ∀ k : ZMod N, inverseAmbient (q k) (base q k) = (q k : Ambient n) := fun k =>
    congrFun (decode_base q) k
  have ht : ∀ k : ZMod N, base q k ∈ (extChartAt (𝓡 n) (q k)).target :=
    (mem_chart_target q (base q)).mp (base_mem_target q)
  have ha : ContDiffAt ℝ 3 (inverseAmbient (q i)) (edgeL i (base q)).1 :=
    (inverseAmbient_smoothAt (q i) (ht i)).of_le (by simp)
  have hb' : ContDiffAt ℝ 3 (inverseAmbient (q (i + 1))) (edgeL i (base q)).2 :=
    (inverseAmbient_smoothAt (q (i + 1)) (ht (i + 1))).of_le (by simp)
  have h2 : ContDiffAt ℝ 3 (fun z : Coordinates n × Coordinates n =>
      (inverseAmbient (q i) z.1, inverseAmbient (q (i + 1)) z.2)) (edgeL i (base q)) :=
    (ha.comp _ contDiffAt_fst).prodMk (hb'.comp _ contDiffAt_snd)
  have h3 : ContDiffAt ℝ 3 (ambientMinEnergy F)
      (inverseAmbient (q i) (edgeL i (base q)).1,
        inverseAmbient (q (i + 1)) (edgeL i (base q)).2) := by
    change ContDiffAt ℝ 3 (ambientMinEnergy F)
      (inverseAmbient (q i) (base q i), inverseAmbient (q (i + 1)) (base q (i + 1)))
    rw [hb, hb]
    exact h1
  exact ContDiffAt.comp (g := ambientMinEnergy F)
    (f := fun z : Coordinates n × Coordinates n =>
      (inverseAmbient (q i) z.1, inverseAmbient (q (i + 1)) z.2)) (edgeL i (base q)) h3 h2

include hδ hq hne in
/-- Near the central polygon every pair energy is differentiable at the coordinates of its
edge. -/
theorem eventually_differentiableAt :
    ∀ᶠ x in 𝓝 (base q), ∀ i : ZMod N, DifferentiableAt ℝ (pairE F q i) (edgeL i x) := by
  rw [Filter.eventually_all]
  intro i
  have h := (pairE_contDiffAt F hδ hq hne i).eventually (by simp)
  have ht : Tendsto (edgeL (n := n) i) (𝓝 (base q)) (𝓝 (edgeL i (base q))) :=
    (edgeL i).continuous.tendsto _
  exact (ht.eventually h).mono fun x hx => hx.differentiableAt (by simp)

/-- The derivative of the coordinate energy in a direction supported at the vertex j involves
only the two edges at j. -/
theorem fderiv_energy_single (q : ZMod N → Sphere n) {x : Model n N}
    (hx : ∀ i, DifferentiableAt ℝ (pairE F q i) (edgeL i x)) (h10 : (1 : ZMod N) ≠ 0)
    (j : ZMod N) (η : Coordinates n) :
    fderiv ℝ (energy F q) x (PiLp.single 2 j η) =
      N * (fderiv ℝ (pairE F q j) (edgeL j x) (η, 0) +
        fderiv ℝ (pairE F q (j - 1)) (edgeL (j - 1) x) (0, η)) := by
  have hsum : HasFDerivAt (fun x : Model n N => (N : ℝ) * ∑ i : ZMod N, pairE F q i (edgeL i x))
      ((N : ℝ) • ∑ i : ZMod N, (fderiv ℝ (pairE F q i) (edgeL i x)).comp (edgeL i)) x := by
    have h1 : ∀ i ∈ (Finset.univ : Finset (ZMod N)),
        HasFDerivAt (fun x : Model n N => pairE F q i (edgeL i x))
          ((fderiv ℝ (pairE F q i) (edgeL i x)).comp (edgeL i)) x := fun i _ =>
      (hx i).hasFDerivAt.comp x (edgeL i).hasFDerivAt
    exact (HasFDerivAt.fun_sum h1).const_mul (N : ℝ)
  have hE : energy F q =
      fun x : Model n N => (N : ℝ) * ∑ i : ZMod N, pairE F q i (edgeL i x) :=
    funext (energy_eq_sum F q)
  have hjj : j ≠ j - 1 := fun h => h10 (by
    have h' : j - (j - 1) = j - j := congrArg (fun t => j - t) h.symm
    simpa using h')
  have h0 : ∀ c ∈ (Finset.univ : Finset (ZMod N)), c ≠ j ∧ c ≠ j - 1 →
      (fderiv ℝ (pairE F q c) (edgeL c x)) (edgeL c (PiLp.single 2 j η)) = 0 := by
    intro c _ hc
    have hc1 : c + 1 ≠ j := fun h => hc.2 (eq_sub_of_add_eq h)
    have hz : edgeL c (PiLp.single 2 j η : Model n N) = 0 := by
      rw [edgeL_apply, PiLp.single_eq_of_ne 2 hc.1, PiLp.single_eq_of_ne 2 hc1]
      rfl
    rw [hz, map_zero]
  have hj : edgeL j (PiLp.single 2 j η : Model n N) = (η, 0) := by
    have hne1 : j + 1 ≠ j := fun h => h10 (by simpa using h)
    rw [edgeL_apply, PiLp.single_eq_same, PiLp.single_eq_of_ne 2 hne1]
  have hj' : edgeL (j - 1) (PiLp.single 2 j η : Model n N) = (0, η) := by
    rw [edgeL_apply, PiLp.single_eq_of_ne 2 hjj.symm, sub_add_cancel, PiLp.single_eq_same]
  rw [hE, hsum.fderiv]
  change (N : ℝ) * (∑ i : ZMod N, (fderiv ℝ (pairE F q i) (edgeL i x)).comp (edgeL i))
    (PiLp.single 2 j η) = _
  rw [sum_apply]
  have hs : ∑ i : ZMod N, ((fderiv ℝ (pairE F q i) (edgeL i x)).comp (edgeL i))
      (PiLp.single 2 j η) =
      (fderiv ℝ (pairE F q j) (edgeL j x)) (edgeL j (PiLp.single 2 j η)) +
        (fderiv ℝ (pairE F q (j - 1)) (edgeL (j - 1) x))
          (edgeL (j - 1) (PiLp.single 2 j η)) :=
    Finset.sum_eq_add j (j - 1) hjj h0 (fun h => absurd (Finset.mem_univ _) h)
      (fun h => absurd (Finset.mem_univ _) h)
  rw [hs, hj, hj']

/-- The twist condition: the mixed second derivative of every pair energy at the central polygon
is nondegenerate in the second variable. -/
def Twist (F : ReversibleMetric n) (q : ZMod N → Sphere n) : Prop :=
  ∀ (j : ZMod N) (v : Coordinates n),
    (∀ η : Coordinates n,
      fderiv ℝ (fun z => fderiv ℝ (pairE F q j) z (η, 0)) (edgeL j (base q)) (0, v) = 0) →
    v = 0

include hδ hq hne in
/-- Propagation for the kernel of the Hessian: a kernel vector that vanishes at the vertices
j - 1 and j vanishes at j + 1, under the twist condition. -/
theorem propagation (htw : Twist F q) {w : Model n N} (hw : hessian F q w = 0) (j : ZMod N)
    (h1 : w (j - 1) = 0) (h2 : w j = 0) : w (j + 1) = 0 := by
  have h10 : (1 : ZMod N) ≠ 0 := fun h => hne 0 (by rw [zero_add, h])
  have hNpos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  apply htw j
  intro η
  have hE3 := energy_contDiffAt F hδ hq hne
  have hD2 : HasFDerivAt (fderiv ℝ (energy F q)) (fderiv ℝ (fderiv ℝ (energy F q)) (base q))
      (base q) :=
    ((hE3.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  -- the derivative in the direction of the vertex j, as a function of the point
  have hψ : HasFDerivAt (fun x : Model n N => fderiv ℝ (energy F q) x (PiLp.single 2 j η))
      ((ContinuousLinearMap.apply ℝ ℝ (PiLp.single 2 j η : Model n N)).comp
        (fderiv ℝ (fderiv ℝ (energy F q)) (base q))) (base q) :=
    (ContinuousLinearMap.apply ℝ ℝ (PiLp.single 2 j η : Model n N)).hasFDerivAt.comp (base q) hD2
  have hval : fderiv ℝ (fun x : Model n N => fderiv ℝ (energy F q) x (PiLp.single 2 j η))
      (base q) w = 0 := by
    rw [hψ.fderiv]
    change fderiv ℝ (fderiv ℝ (energy F q)) (base q) w (PiLp.single 2 j η) = 0
    rw [← Hessian.inner_operator]
    change ⟪hessian F q w, (PiLp.single 2 j η : Model n N)⟫ = 0
    rw [hw, inner_zero_left]
  -- the same function through the two edges at j
  have hev : (fun x : Model n N => fderiv ℝ (energy F q) x (PiLp.single 2 j η)) =ᶠ[𝓝 (base q)]
      fun x => (N : ℝ) * (fderiv ℝ (pairE F q j) (edgeL j x) (η, 0) +
        fderiv ℝ (pairE F q (j - 1)) (edgeL (j - 1) x) (0, η)) :=
    (eventually_differentiableAt F hδ hq hne).mono fun x hx =>
      fderiv_energy_single F q hx h10 j η
  have hA : DifferentiableAt ℝ (fun z => fderiv ℝ (pairE F q j) z (η, 0)) (edgeL j (base q)) :=
    (ContinuousLinearMap.apply ℝ ℝ ((η, 0) : Coordinates n × Coordinates n)).differentiableAt.comp
      _ (((pairE_contDiffAt F hδ hq hne j).fderiv_right (m := 2) (by norm_num)).differentiableAt
        (by norm_num))
  have hB : DifferentiableAt ℝ (fun z => fderiv ℝ (pairE F q (j - 1)) z (0, η))
      (edgeL (j - 1) (base q)) :=
    (ContinuousLinearMap.apply ℝ ℝ ((0, η) : Coordinates n × Coordinates n)).differentiableAt.comp
      _ (((pairE_contDiffAt F hδ hq hne (j - 1)).fderiv_right (m := 2)
        (by norm_num)).differentiableAt (by norm_num))
  have hψ' : HasFDerivAt (fun x : Model n N =>
      (N : ℝ) * (fderiv ℝ (pairE F q j) (edgeL j x) (η, 0) +
        fderiv ℝ (pairE F q (j - 1)) (edgeL (j - 1) x) (0, η)))
      ((N : ℝ) • ((fderiv ℝ (fun z => fderiv ℝ (pairE F q j) z (η, 0))
          (edgeL j (base q))).comp (edgeL j) +
        (fderiv ℝ (fun z => fderiv ℝ (pairE F q (j - 1)) z (0, η))
          (edgeL (j - 1) (base q))).comp (edgeL (j - 1)))) (base q) :=
    ((hA.hasFDerivAt.comp (base q) (edgeL j).hasFDerivAt).add
      (hB.hasFDerivAt.comp (base q) (edgeL (j - 1)).hasFDerivAt)).const_mul (N : ℝ)
  have hw1 : edgeL (j - 1) w = 0 := by
    rw [edgeL_apply, h1, sub_add_cancel, h2]
    rfl
  have hw2 : edgeL j w = (0, w (j + 1)) := by rw [edgeL_apply, h2]
  rw [hev.fderiv_eq, hψ'.fderiv] at hval
  have hval' : (N : ℝ) * ((fderiv ℝ (fun z => fderiv ℝ (pairE F q j) z (η, 0))
      (edgeL j (base q))) (edgeL j w) +
      (fderiv ℝ (fun z => fderiv ℝ (pairE F q (j - 1)) z (0, η))
        (edgeL (j - 1) (base q))) (edgeL (j - 1) w)) = 0 := hval
  rw [hw1, hw2, map_zero, add_zero] at hval'
  exact (mul_eq_zero.mp hval').resolve_left hNpos

include hδ hq hne in
/-- Under the twist condition the nullity of a short polygon without zero edges is at most
2 n. -/
theorem nullity_le (htw : Twist F q) : nullity F q ≤ 2 * n := by
  have h := JacobiRecursion.finrank_ker_le (V := Coordinates n) (N := N)
    (hessian F q).toLinearMap
    (fun w hw j h1 h2 => propagation F hδ hq hne htw hw j h1 h2)
  rw [finrank_euclideanSpace_fin] at h
  exact h

end Regular

end

end Finsler.PolygonNullity
