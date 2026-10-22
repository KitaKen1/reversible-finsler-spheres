module

public import Finsler.Geometry.PolygonTwist
public import Finsler.Geometry.PolygonIterateReduction
public import Finsler.Algebra.JacobiChain

/-! The monodromy of a short polygon and the nullities of its iterates. In the Hilbert
coordinates of a short polygon without zero edges, the Hessian of the coordinate energy is of
Jacobi type: its component at the vertex j is N times T_j w_{j+1} + A_j w_j + B_j w_{j-1}, where
the operators T_j, A_j, B_j represent the blocks of the second derivatives of the pair energies
of the two edges at j. Under the twist condition T_j is bijective, so the kernel of the Hessian
is the space of the solutions of a second-order recursion along the closed chain, and the
nullity is the dimension of the space of the vectors fixed by the monodromy M of the recursion.
The pair energies of the m-fold iterate are those of the polygon, so its coefficients are the
iterated coefficients and its monodromy is M^m: the nullity of the m-fold iterate is the
dimension of the space of the vectors fixed by M^m. Hence there is L ≥ 1 such that the nullity
of the m-fold iterate depends only on gcd(m, L), and the nullity of the k-fold iterate of the
d-fold iterate equals that of the d-fold iterate whenever gcd(d k, L) = gcd(d, L). No statement
on indices or local cohomology is made. -/

@[expose] public section

namespace Finsler.PolygonMonodromy

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.EnergySphereSmooth Finsler.PolygonChart Finsler.PolygonHessian
open Finsler.PolygonNullity Finsler.PolygonIterate Finsler.PolygonIterateReduction
open Finsler.PeriodicKernel
open Set Filter Module InnerProductSpace
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

/-! ### Blocks of a bilinear form and their operators -/

section Blocks

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A block of a bilinear form: (v, η) ↦ β (ι₁ v) (ι₂ η). -/
def block (β : W →L[ℝ] W →L[ℝ] ℝ) (ι₁ ι₂ : V →L[ℝ] W) : V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ V W ℝ).flip ι₂).comp (β.comp ι₁)

theorem block_apply (β : W →L[ℝ] W →L[ℝ] ℝ) (ι₁ ι₂ : V →L[ℝ] W) (v η : V) :
    block β ι₁ ι₂ v η = β (ι₁ v) (ι₂ η) := rfl

variable [CompleteSpace V]

/-- The operator representing a bilinear form. -/
def rep (β : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V :=
  (toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp β

theorem inner_rep (β : V →L[ℝ] V →L[ℝ] ℝ) (v η : V) : ⟪rep β v, η⟫ = β v η :=
  toDual_symm_apply

end Blocks

variable {n N : ℕ} [NeZero N]

/-! ### The coefficients -/

/-- The second derivative of the pair energy of the edge i at the central polygon. -/
def hess2 (F : ReversibleMetric n) (q : ZMod N → Sphere n) (i : ZMod N) :
    (Coordinates n × Coordinates n) →L[ℝ] (Coordinates n × Coordinates n) →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (pairE F q i)) (edgeL i (base q))

/-- The coefficient of the next vertex: the mixed block of the edge from j to j + 1. -/
def Tmap (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod N) :
    Coordinates n →L[ℝ] Coordinates n :=
  rep (block (hess2 F q j) (ContinuousLinearMap.inr ℝ (Coordinates n) (Coordinates n))
    (ContinuousLinearMap.inl ℝ (Coordinates n) (Coordinates n)))

/-- The coefficient of the vertex itself: the diagonal blocks of the two edges at j. -/
def Amap (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod N) :
    Coordinates n →L[ℝ] Coordinates n :=
  rep (block (hess2 F q j) (ContinuousLinearMap.inl ℝ (Coordinates n) (Coordinates n))
      (ContinuousLinearMap.inl ℝ (Coordinates n) (Coordinates n)) +
    block (hess2 F q (j - 1)) (ContinuousLinearMap.inr ℝ (Coordinates n) (Coordinates n))
      (ContinuousLinearMap.inr ℝ (Coordinates n) (Coordinates n)))

/-- The coefficient of the previous vertex: the mixed block of the edge from j - 1 to j. -/
def Bmap (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod N) :
    Coordinates n →L[ℝ] Coordinates n :=
  rep (block (hess2 F q (j - 1)) (ContinuousLinearMap.inl ℝ (Coordinates n) (Coordinates n))
    (ContinuousLinearMap.inr ℝ (Coordinates n) (Coordinates n)))

omit [NeZero N] in
theorem inner_Tmap (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod N)
    (v η : Coordinates n) : ⟪Tmap F q j v, η⟫ = hess2 F q j (0, v) (η, 0) := by
  rw [Tmap, inner_rep]
  rfl

omit [NeZero N] in
theorem inner_Amap (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod N)
    (v η : Coordinates n) :
    ⟪Amap F q j v, η⟫ = hess2 F q j (v, 0) (η, 0) + hess2 F q (j - 1) (0, v) (0, η) := by
  rw [Amap, inner_rep]
  rfl

omit [NeZero N] in
theorem inner_Bmap (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod N)
    (v η : Coordinates n) : ⟪Bmap F q j v, η⟫ = hess2 F q (j - 1) (v, 0) (0, η) := by
  rw [Bmap, inner_rep]
  rfl

/-- The inner product with a vector supported at one vertex. -/
theorem inner_single (x : Model n N) (j : ZMod N) (η : Coordinates n) :
    ⟪x, (PiLp.single 2 j η : Model n N)⟫ = ⟪x j, η⟫ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · rw [PiLp.single_eq_same]
  · intro b _ hb
    rw [PiLp.single_eq_of_ne 2 hb, inner_zero_right]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-! ### The Hessian is of Jacobi type -/

section Regular

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

include hδ hq hne in
/-- The derivative of a directional derivative of a pair energy at the central polygon is given
by the second derivative. -/
theorem hasFDerivAt_pair (i : ZMod N) (ζ : Coordinates n × Coordinates n) :
    HasFDerivAt (fun z => fderiv ℝ (pairE F q i) z ζ)
      ((ContinuousLinearMap.apply ℝ ℝ ζ).comp (hess2 F q i)) (edgeL i (base q)) :=
  (ContinuousLinearMap.apply ℝ ℝ ζ).hasFDerivAt.comp (edgeL i (base q))
    (((pairE_contDiffAt F hδ hq hne i).fderiv_right (m := 2) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt

include hδ hq hne in
/-- The Hessian paired with a vector supported at the vertex j involves the second derivatives
of the pair energies of the two edges at j. -/
theorem inner_hessian_single (w : Model n N) (j : ZMod N) (η : Coordinates n) :
    ⟪hessian F q w, (PiLp.single 2 j η : Model n N)⟫ =
      N * (hess2 F q j (edgeL j w) (η, 0) + hess2 F q (j - 1) (edgeL (j - 1) w) (0, η)) := by
  have h10 : (1 : ZMod N) ≠ 0 := fun h => hne 0 (by rw [zero_add, h])
  have hE3 := energy_contDiffAt F hδ hq hne
  have hD2 : HasFDerivAt (fderiv ℝ (energy F q)) (fderiv ℝ (fderiv ℝ (energy F q)) (base q))
      (base q) :=
    ((hE3.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hψ : HasFDerivAt (fun x : Model n N => fderiv ℝ (energy F q) x (PiLp.single 2 j η))
      ((ContinuousLinearMap.apply ℝ ℝ (PiLp.single 2 j η : Model n N)).comp
        (fderiv ℝ (fderiv ℝ (energy F q)) (base q))) (base q) :=
    (ContinuousLinearMap.apply ℝ ℝ (PiLp.single 2 j η : Model n N)).hasFDerivAt.comp (base q) hD2
  have hval : ⟪hessian F q w, (PiLp.single 2 j η : Model n N)⟫ =
      fderiv ℝ (fun x : Model n N => fderiv ℝ (energy F q) x (PiLp.single 2 j η)) (base q) w := by
    rw [hψ.fderiv]
    change _ = fderiv ℝ (fderiv ℝ (energy F q)) (base q) w (PiLp.single 2 j η)
    rw [← Hessian.inner_operator]
    rfl
  have hev : (fun x : Model n N => fderiv ℝ (energy F q) x (PiLp.single 2 j η)) =ᶠ[𝓝 (base q)]
      fun x => (N : ℝ) * (fderiv ℝ (pairE F q j) (edgeL j x) (η, 0) +
        fderiv ℝ (pairE F q (j - 1)) (edgeL (j - 1) x) (0, η)) :=
    (eventually_differentiableAt F hδ hq hne).mono fun x hx =>
      fderiv_energy_single F q hx h10 j η
  have hψ' : HasFDerivAt (fun x : Model n N =>
      (N : ℝ) * (fderiv ℝ (pairE F q j) (edgeL j x) (η, 0) +
        fderiv ℝ (pairE F q (j - 1)) (edgeL (j - 1) x) (0, η)))
      ((N : ℝ) • ((((ContinuousLinearMap.apply ℝ ℝ
          ((η, 0) : Coordinates n × Coordinates n)).comp (hess2 F q j)).comp (edgeL j)) +
        (((ContinuousLinearMap.apply ℝ ℝ
          ((0, η) : Coordinates n × Coordinates n)).comp (hess2 F q (j - 1))).comp
            (edgeL (j - 1))))) (base q) :=
    (((hasFDerivAt_pair F hδ hq hne j (η, 0)).comp (base q) (edgeL j).hasFDerivAt).add
      ((hasFDerivAt_pair F hδ hq hne (j - 1) (0, η)).comp (base q)
        (edgeL (j - 1)).hasFDerivAt)).const_mul (N : ℝ)
  rw [hval, hev.fderiv_eq, hψ'.fderiv]
  rfl

include hδ hq hne in
/-- **The Hessian is of Jacobi type.** Its component at the vertex j is N times
T_j w_{j+1} + A_j w_j + B_j w_{j-1}. -/
theorem hessian_apply (w : Model n N) (j : ZMod N) :
    hessian F q w j =
      (N : ℝ) • (Tmap F q j (w (j + 1)) + Amap F q j (w j) + Bmap F q j (w (j - 1))) := by
  refine ext_inner_right ℝ fun η => ?_
  have e1 : edgeL j w = (w j, 0) + (0, w (j + 1)) := by
    rw [edgeL_apply, Prod.mk_add_mk, add_zero, zero_add]
  have e2 : edgeL (j - 1) w = (w (j - 1), 0) + (0, w j) := by
    rw [edgeL_apply, sub_add_cancel, Prod.mk_add_mk, add_zero, zero_add]
  rw [← inner_single (hessian F q w) j η, inner_hessian_single F hδ hq hne,
    real_inner_smul_left, inner_add_left, inner_add_left, inner_Tmap, inner_Amap, inner_Bmap,
    e1, e2]
  simp only [map_add, add_apply]
  ring

include hδ hq hne in
/-- Under the twist condition the coefficient of the next vertex is injective. -/
theorem Tmap_injective (htw : Twist F q) (j : ZMod N) : Function.Injective (Tmap F q j) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  refine htw j v fun η => ?_
  rw [(hasFDerivAt_pair F hδ hq hne j (η, 0)).fderiv]
  change hess2 F q j (0, v) (η, 0) = 0
  rw [← inner_Tmap, hv, inner_zero_left]

/-- The coefficients of the discrete Jacobi equation of a short polygon without zero edges
with the twist condition. -/
def coeff (htw : Twist F q) : JacobiChain.Coeff (Coordinates n) N where
  T j := LinearEquiv.ofInjectiveEndo (Tmap F q j).toLinearMap (Tmap_injective F hδ hq hne htw j)
  A j := (Amap F q j).toLinearMap
  B j := (Bmap F q j).toLinearMap

include hδ hq hne in
/-- The kernel of the Hessian is the space of the solutions of the discrete Jacobi equation. -/
theorem hessian_eq_zero_iff (htw : Twist F q) (w : Model n N) :
    hessian F q w = 0 ↔
      ∀ j : ZMod N, JacobiChain.res (coeff F hδ hq hne htw) (fun i => w i) j = 0 := by
  have hNpos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hres : ∀ j : ZMod N, hessian F q w j =
      (N : ℝ) • JacobiChain.res (coeff F hδ hq hne htw) (fun i => w i) j :=
    fun j => hessian_apply F hδ hq hne w j
  constructor
  · intro h j
    have h' := hres j
    have h0 : (0 : Model n N) j = 0 := rfl
    rw [h, h0] at h'
    exact (smul_eq_zero.mp h'.symm).resolve_left hNpos
  · intro h
    refine PiLp.ext fun j => ?_
    rw [hres j, h j, smul_zero]
    rfl

include hδ hq hne in
/-- **The nullity and the monodromy.** The nullity of a short polygon without zero edges with
the twist condition is the dimension of the space of the vectors fixed by the monodromy. -/
theorem nullity_eq (htw : Twist F q) :
    nullity F q = finrank ℝ (fixedPow (JacobiChain.mono (coeff F hδ hq hne htw)) 1) :=
  JacobiChain.finrank_ker_eq (coeff F hδ hq hne htw) (hessian F q).toLinearMap
    (hessian_eq_zero_iff F hδ hq hne htw)

end Regular

/-! ### Iterates -/

section Iterate

variable (m : ℕ) [NeZero m]

omit [NeZero m] [NeZero N] in
/-- The pair energies of the iterate are the pair energies of the polygon. -/
theorem pairE_iterate (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod (m * N)) :
    pairE F (iterate m N q) j = pairE F q (red m N j) := by
  funext z
  unfold pairE
  rw [iterate_apply, iterate_apply, map_add, map_one]

theorem edgeL_base_iterate (q : ZMod N → Sphere n) (j : ZMod (m * N)) :
    edgeL j (base (iterate m N q)) = edgeL (red m N j) (base q) := by
  rw [base_iterate, edgeL_apply, edgeL_apply, iterL_apply, iterL_apply, map_add, map_one]

theorem hess2_iterate (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod (m * N)) :
    hess2 F (iterate m N q) j = hess2 F q (red m N j) := by
  rw [hess2, hess2, pairE_iterate, edgeL_base_iterate]

theorem Tmap_iterate (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod (m * N)) :
    Tmap F (iterate m N q) j = Tmap F q (red m N j) := by
  rw [Tmap, Tmap, hess2_iterate]

theorem Amap_iterate (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod (m * N)) :
    Amap F (iterate m N q) j = Amap F q (red m N j) := by
  rw [Amap, Amap, hess2_iterate, hess2_iterate, map_sub, map_one]

theorem Bmap_iterate (F : ReversibleMetric n) (q : ZMod N → Sphere n) (j : ZMod (m * N)) :
    Bmap F (iterate m N q) j = Bmap F q (red m N j) := by
  rw [Bmap, Bmap, hess2_iterate, map_sub, map_one]

/-- The twist condition passes to the iterates. -/
theorem twist_iterate (F : ReversibleMetric n) {q : ZMod N → Sphere n} (htw : Twist F q) :
    Twist F (iterate m N q) := by
  intro j v hv
  refine htw (red m N j) v fun η => ?_
  have h := hv η
  rw [pairE_iterate, edgeL_base_iterate] at h
  exact h

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

/-- The coefficients of the iterate are the iterated coefficients. -/
theorem coeff_iterate (htw : Twist F q) :
    coeff F hδ (shortPolygon_iterate m N hq) (iterate_ne m N hne) (twist_iterate m F htw) =
      JacobiChain.iter m (coeff F hδ hq hne htw) := by
  refine JacobiChain.Coeff.ext (funext fun j => LinearEquiv.ext fun v => ?_)
    (funext fun j => ?_) (funext fun j => ?_)
  · change Tmap F (iterate m N q) j v = Tmap F q (red m N j) v
    rw [Tmap_iterate]
  · change (Amap F (iterate m N q) j).toLinearMap = (Amap F q (red m N j)).toLinearMap
    rw [Amap_iterate]
  · change (Bmap F (iterate m N q) j).toLinearMap = (Bmap F q (red m N j)).toLinearMap
    rw [Bmap_iterate]

/-- **The nullities of the iterates.** The nullity of the m-fold iterate is the dimension of
the space of the vectors fixed by the m-th power of the monodromy. -/
theorem nullity_iterate (htw : Twist F q) :
    nullity F (iterate m N q) =
      finrank ℝ (fixedPow (JacobiChain.mono (coeff F hδ hq hne htw)) m) := by
  rw [nullity_eq F hδ (shortPolygon_iterate m N hq) (iterate_ne m N hne) (twist_iterate m F htw),
    coeff_iterate, JacobiChain.mono_iter, fixedPow_pow, mul_one]

end Iterate

section Period

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

/-- The nullity of the k-fold iterate of the d-fold iterate. -/
theorem nullity_iterate_iterate (htw : Twist F q) (d k : ℕ) [NeZero d] [NeZero k] :
    nullity F (iterate k (d * N) (iterate d N q)) =
      finrank ℝ (fixedPow (JacobiChain.mono (coeff F hδ hq hne htw)) (d * k)) := by
  rw [nullity_iterate k F hδ (shortPolygon_iterate d N hq) (iterate_ne d N hne)
    (twist_iterate d F htw), coeff_iterate, JacobiChain.mono_iter, fixedPow_pow]

include hδ hq hne in
/-- **Finitely many types of iterates.** There is L ≥ 1 such that the nullity of the m-fold
iterate depends only on gcd(m, L), and the nullity of the k-fold iterate of the d-fold iterate
is the nullity of the d-fold iterate whenever gcd(d k, L) = gcd(d, L). -/
theorem exists_period (htw : Twist F q) :
    ∃ L : ℕ, 1 ≤ L ∧
      (∃ ν : ℕ → ℕ, ∀ (m : ℕ) [NeZero m], nullity F (iterate m N q) = ν (Nat.gcd m L)) ∧
      ∀ (d k : ℕ) [NeZero d] [NeZero k], Nat.gcd (d * k) L = Nat.gcd d L →
        nullity F (iterate k (d * N) (iterate d N q)) = nullity F (iterate d N q) := by
  obtain ⟨L, hL, hper⟩ := PeriodicKernel.exists_period
    (JacobiChain.mono (coeff F hδ hq hne htw))
  refine ⟨L, hL, ⟨fun d => finrank ℝ (fixedPow (JacobiChain.mono (coeff F hδ hq hne htw)) d),
    fun m _ => ?_⟩, fun d k _ _ hg => ?_⟩
  · have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    rw [nullity_iterate m F hδ hq hne htw, hper m hm]
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
    rw [nullity_iterate_iterate F hδ hq hne htw d k, nullity_iterate d F hδ hq hne htw,
      hper (d * k) (Nat.mul_pos hd hk), hper d hd, hg]

end Period

/-- **Finitely many types of iterates, uniformly.** There is a positive radius below which
every polygon without zero edges, with any number of vertices, has a period L ≥ 1: the nullity
of its m-fold iterate depends only on gcd(m, L), and the nullity of the k-fold iterate of the
d-fold iterate is the nullity of the d-fold iterate whenever gcd(d k, L) = gcd(d, L). -/
theorem exists_nullity_period (F : ReversibleMetric n) :
    ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (q : ZMod N → Sphere n), ShortPolygon δ q →
      (∀ i, q (i + 1) ≠ q i) →
      ∃ L : ℕ, 1 ≤ L ∧
        (∃ ν : ℕ → ℕ, ∀ (m : ℕ) [NeZero m], nullity F (iterate m N q) = ν (Nat.gcd m L)) ∧
        ∀ (d k : ℕ) [NeZero d] [NeZero k], Nat.gcd (d * k) L = Nat.gcd d L →
          nullity F (iterate k (d * N) (iterate d N q)) = nullity F (iterate d N q) := by
  obtain ⟨δ₁, hδ₁, htw⟩ := PolygonTwist.exists_twist F
  obtain ⟨δ₂, hδ₂, hs⟩ := exists_ambientMinEnergy_contDiffAt F
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun N _ q hq hne => ?_⟩
  have hq₁ : ShortPolygon δ₁ q := fun i => (hq i).trans_le (min_le_left _ _)
  have hq₂ : ShortPolygon δ₂ q := fun i => (hq i).trans_le (min_le_right _ _)
  exact exists_period F hs hq₂ hne (htw N q hq₁ hne)

end

end Finsler.PolygonMonodromy
