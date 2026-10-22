module

public import Finsler.Geometry.PhaseNullity
public import Finsler.Analysis.InvariantFrames

/-! Closed definite frames of the normal bundle along a circle of iterated polygons. On the
ambient polygons the sum of the inner products of the vertices is a positive definite symmetric
bilinear function which is invariant under the rotations. The rotations preserve the space of
the vectors whose sum over the rotations by the periods vanishes (the normal space), and a
rotation by a whose s-th power is the rotation by one period has no real eigenvalue on the
normal space if s is even or the number m of periods is odd.

Let q_θ be a continuous family of short stationary polygons with N vertices without zero edges
such that the m-fold iterates have the nullities of the q_θ and indices exceeding those of the
q_θ by b, such that q_{θ + η} is the rotation of the vertices of q_θ by one, and such that
q_{θ + 2 r η} = q_θ, where N = s (2 r) with s even or m odd. The second derivatives of the
penalized energy at the iterates, restricted to the normal space, form a family of index b,
their negatives a family of index dim - b, both with the symmetry given by the rotation by one
vertex. Hence there are continuous families of negative frames of b vectors and of positive
frames of dim - b vectors of the normal space over [0, 2 r η] which take the same value at both
ends. -/

@[expose] public section

namespace Finsler.NormalFamily

open Module QuadraticForm QuadraticMap Filter Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth Finsler.PolygonIterate
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.AmbientPenalty Finsler.AmbientDescent
open Finsler.AmbientHessian Finsler.AmbientSymmetry Finsler.SymmetricBlocks
open Finsler.AmbientNormalIndex Finsler.AmbientNullity Finsler.AmbientNormalNondeg
open Finsler.AmbientRotation Finsler.PolygonIterateReduction Finsler.PhaseNullity
open Finsler.DefiniteFrames Finsler.FramePath Finsler.FrameIndex Finsler.FormSemicontinuity
open Finsler.InvariantFrames
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ}

/-! ### The sum of the inner products of the vertices -/

section VertexForm

variable (K : ℕ) [NeZero K]

/-- The sum of the inner products of the vertices of two ambient polygons. -/
def vertexForm : (ZMod K → Ambient n) →ₗ[ℝ] (ZMod K → Ambient n) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => ∑ i, ⟪v i, w i⟫)
    (fun v v' w => by simp only [Pi.add_apply, inner_add_left, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [Pi.smul_apply, real_inner_smul_left, smul_eq_mul, Finset.mul_sum])
    (fun v w w' => by simp only [Pi.add_apply, inner_add_right, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [Pi.smul_apply, real_inner_smul_right, smul_eq_mul, Finset.mul_sum])

theorem vertexForm_apply (v w : ZMod K → Ambient n) :
    vertexForm K v w = ∑ i, ⟪v i, w i⟫ := rfl

theorem vertexForm_symm (v w : ZMod K → Ambient n) : vertexForm K v w = vertexForm K w v := by
  rw [vertexForm_apply, vertexForm_apply]
  exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _

theorem vertexForm_pos {v : ZMod K → Ambient n} (hv : v ≠ 0) : 0 < vertexForm K v v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    exact hv (funext fun i => by
      by_contra hi
      exact h ⟨i, hi⟩)
  rw [vertexForm_apply]
  exact Finset.sum_pos' (fun j _ => real_inner_self_nonneg)
    ⟨i, Finset.mem_univ _, real_inner_self_pos.mpr hi⟩

/-- The vertex form is invariant under the rotations. -/
theorem vertexForm_rotA (s : ZMod K) (v w : ZMod K → Ambient n) :
    vertexForm K (rotA K s v) (rotA K s w) = vertexForm K v w := by
  rw [vertexForm_apply, vertexForm_apply]
  exact Equiv.sum_comp (Equiv.addRight s) fun i => ⟪v i, w i⟫

end VertexForm

/-! ### Rotations on the normal space -/

section Normal

variable (m N : ℕ) [NeZero m] [NeZero N]

omit [NeZero m] [NeZero N] in
/-- The rotations commute with the powers of the rotation by one period. -/
theorem rotL_pow_rotA (a : ZMod (m * N)) (j : ℕ) (v : ZMod (m * N) → Ambient n) :
    ((rotL (n := n) m N) ^ j) (rotA (m * N) a v) = rotA (m * N) a (((rotL (n := n) m N) ^ j) v) := by
  rw [rotL_pow_apply, rotL_pow_apply, rotA_rotA, rotA_rotA]
  exact congrArg (fun t : ZMod (m * N) => rotA (m * N) t v) (add_comm _ _)

omit [NeZero m] [NeZero N] in
/-- The rotations preserve the normal space. -/
theorem rotA_mem_normal (a : ZMod (m * N)) {v : ZMod (m * N) → Ambient n}
    (hv : v ∈ normal (rotL (n := n) m N) m) :
    rotA (m * N) a v ∈ normal (rotL (n := n) m N) m := by
  rw [mem_normal, powSum_apply] at hv ⊢
  have h : ∑ j ∈ Finset.range m, ((rotL (n := n) m N) ^ j) (rotA (m * N) a v) =
      rotA (m * N) a (∑ j ∈ Finset.range m, ((rotL (n := n) m N) ^ j) v) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => rotL_pow_rotA m N a j v
  rw [h, hv, map_zero]

/-- A rotation as a continuous linear map of the normal space. -/
def rotV (a : ZMod (m * N)) :
    normal (rotL (n := n) m N) m →L[ℝ] normal (rotL (n := n) m N) m :=
  ((rotA (n := n) (m * N) a).comp (normal (rotL (n := n) m N) m).subtypeL).codRestrict
    (normal (rotL (n := n) m N) m) fun v => rotA_mem_normal m N a v.2

omit [NeZero m] [NeZero N] in
theorem rotV_coe (a : ZMod (m * N)) (v : normal (rotL (n := n) m N) m) :
    ((rotV m N a v : normal (rotL (n := n) m N) m) : ZMod (m * N) → Ambient n) =
      rotA (m * N) a (v : ZMod (m * N) → Ambient n) := rfl

omit [NeZero m] [NeZero N] in
/-- The powers of a rotation of the normal space. -/
theorem rotV_pow_coe (a : ZMod (m * N)) (j : ℕ) (v : normal (rotL (n := n) m N) m) :
    ((((rotV (n := n) m N a) ^ j) v : normal (rotL (n := n) m N) m) :
      ZMod (m * N) → Ambient n) =
      rotA (m * N) ((j : ZMod (m * N)) * a) (v : ZMod (m * N) → Ambient n) := by
  induction j generalizing v with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, rotA_zero]
    rfl
  | succ j ih =>
    rw [pow_succ]
    change ((((rotV (n := n) m N a) ^ j) (rotV m N a v) : normal (rotL (n := n) m N) m) :
      ZMod (m * N) → Ambient n) = _
    rw [ih, rotV_coe, rotA_rotA, Nat.cast_succ, add_mul, one_mul]

/-- **No real eigenvalues on the normal space.** If the s-th power of the rotation by a is the
rotation by one period and s is even or m is odd, an eigenvector of the rotation by a in the
normal space with a real eigenvalue vanishes. -/
theorem eq_zero_of_eigen {a : ZMod (m * N)} {s : ℕ}
    (hsa : (s : ZMod (m * N)) * a = (N : ZMod (m * N))) (hpar : Even s ∨ Odd m)
    {x : ZMod (m * N) → Ambient n} (hx : x ∈ normal (rotL (n := n) m N) m) {μ : ℝ}
    (h : rotA (m * N) a x = μ • x) : x = 0 := by
  have hpow : ∀ j : ℕ, rotA (m * N) ((j : ZMod (m * N)) * a) x = μ ^ j • x := by
    intro j
    induction j with
    | zero => rw [Nat.cast_zero, zero_mul, rotA_zero, pow_zero, one_smul]
    | succ j ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ← rotA_rotA, h, map_smul, ih, smul_smul, pow_succ']
  have hσ : rotL (n := n) m N x = μ ^ s • x := by
    rw [rotL_apply, ← hsa]
    exact hpow s
  have hσj : ∀ j : ℕ, ((rotL (n := n) m N) ^ j) x = (μ ^ s) ^ j • x := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, one_smul]; rfl
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hσ, smul_smul, pow_succ]
  have hsum : (∑ j ∈ Finset.range m, (μ ^ s) ^ j) • x = 0 := by
    rw [mem_normal, powSum_apply] at hx
    rw [Finset.sum_smul, ← hx]
    exact Finset.sum_congr rfl fun j _ => (hσj j).symm
  have hone : (μ ^ s) ^ m • x = x := by
    rw [← hσj m, rotL_pow]
    rfl
  by_contra hx0
  have hc1 : (μ ^ s) ^ m = 1 := by
    have h1 : ((μ ^ s) ^ m - 1) • x = 0 := by rw [sub_smul, hone, one_smul, sub_self]
    have h2 := (smul_eq_zero.mp h1).resolve_right hx0
    linarith
  have hs0 : ∑ j ∈ Finset.range m, (μ ^ s) ^ j = 0 := (smul_eq_zero.mp hsum).resolve_right hx0
  have habs : |μ ^ s| = 1 := by
    have h1 : |μ ^ s| ^ m = 1 := by rw [← abs_pow, hc1, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) (NeZero.ne m)).mp h1
  rcases (abs_eq (zero_le_one' ℝ)).mp habs with hc | hc
  · rw [hc] at hs0
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs0
    exact NeZero.ne m (by exact_mod_cast hs0)
  · have hseven : ¬ Even s := by
      intro he
      have h1 : 0 ≤ μ ^ s := he.pow_nonneg μ
      rw [hc] at h1
      linarith
    have hmeven : Even m := by
      rw [hc] at hc1
      exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hc1
    rcases hpar with hp | hp
    · exact hseven hp
    · exact (Nat.not_even_iff_odd.mpr hp) hmeven

end Normal

/-! ### The family of the normal second derivatives -/

section Family

variable (m N : ℕ) [NeZero m] [NeZero N] (F : ReversibleMetric n)

/-- The second derivative of the penalized energy at the m-fold iterate of the polygon q θ,
restricted to the normal space. -/
def formB (q : ℝ → ZMod N → Sphere n) (θ : ℝ) :
    normal (rotL (n := n) m N) m →ₗ[ℝ] normal (rotL (n := n) m N) m →ₗ[ℝ] ℝ :=
  ((fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (amb (iterate m N (q θ)))).toLinearMap₁₂).compl₁₂
    (normal (rotL (n := n) m N) m).subtype (normal (rotL (n := n) m N) m).subtype

theorem formB_apply (q : ℝ → ZMod N → Sphere n) (θ : ℝ)
    (v w : normal (rotL (n := n) m N) m) :
    formB m N F q θ v w = fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (amb (iterate m N (q θ)))
      (v : ZMod (m * N) → Ambient n) (w : ZMod (m * N) → Ambient n) := rfl

theorem formB_congr (q : ℝ → ZMod N → Sphere n) {θ θ' : ℝ} (h : q θ = q θ') :
    formB m N F q θ = formB m N F q θ' := by
  unfold formB
  rw [h]

variable {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ℝ → ZMod N → Sphere n} (hcont : Continuous fun θ => amb (q θ))
  (hq : ∀ θ, ShortPolygon δ (q θ)) (hne : ∀ θ i, q θ (i + 1) ≠ q θ i)
  (hc : ∀ θ, PolyCritical F N (q θ))

include hδ hcont hq hne in
theorem formB_continuous :
    Continuous fun p : ℝ × normal (rotL (n := n) m N) m × normal (rotL (n := n) m N) m =>
      formB m N F q p.1 p.2.1 p.2.2 := by
  have hcontP : Continuous fun θ => amb (iterate m N (q θ)) :=
    continuous_pi fun i => (continuous_apply (red m N i)).comp hcont
  have h := sndDeriv_continuous F hδ hcontP (fun θ => shortPolygon_iterate m N (hq θ))
    (fun θ => iterate_ne m N (hne θ)) 1
  exact h.comp (continuous_fst.prodMk
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))

include hδ hq hne in
theorem formB_symm (θ : ℝ) (v w : normal (rotL (n := n) m N) m) :
    formB m N F q θ v w = formB m N F q θ w v :=
  ((pen_contDiffAt_two F hδ (shortPolygon_iterate m N (hq θ)) (iterate_ne m N (hne θ))
    1).isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq _ _

include hδ hq hne hc in
/-- The negative index of the normal second derivative is the difference of the indices. -/
theorem sigNeg_formB {b : ℕ}
    (hidx : ∀ θ (hs : (hessian F (iterate m N (q θ))).toLinearMap.IsSymmetric)
      (hs₀ : (hessian F (q θ)).toLinearMap.IsSymmetric),
      index F (iterate m N (q θ)) hs = index F (q θ) hs₀ + b) (θ : ℝ) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap (formB m N F q θ)) = b := by
  have hqP := shortPolygon_iterate m N (hq θ)
  have hneP := iterate_ne m N (hne θ)
  have hs := hessian_isSymmetric F hδ hqP hneP
  have hs₀ := hessian_isSymmetric F hδ (hq θ) (hne θ)
  have h := index_iterate_eq_add m N F hδ hqP hneP (hq θ) (hne θ)
    (polyCritical_iterate m F hδ (hq θ) (hne θ) (hc θ)) (hc θ) zero_le_one hs hs₀
  rw [hidx θ hs hs₀] at h
  have e : LinearMap.BilinMap.toQuadraticMap (formB m N F q θ) =
      (sndQuad (pen F (m * N) 1) (amb (iterate m N (q θ)))).restrict
        (normal (rotL (n := n) m N) m) := QuadraticMap.ext fun x => rfl
  rw [e]
  omega

include hδ hq hne hc in
/-- The normal second derivative is nondegenerate if the iterate has the nullity of the
polygon. -/
theorem ker_formB (hnull : ∀ θ, nullity F (iterate m N (q θ)) = nullity F (q θ)) (θ : ℝ) :
    LinearMap.ker (formB m N F q θ) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hv' : ∀ w : normal (rotL (n := n) m N) m, formB m N F q θ v w = 0 := fun w => by
    rw [LinearMap.mem_ker.mp hv]
    rfl
  have h := normal_nondegenerate m N F hδ (shortPolygon_iterate m N (hq θ))
    (iterate_ne m N (hne θ)) (hq θ) (hne θ)
    (polyCritical_iterate m F hδ (hq θ) (hne θ) (hc θ)) (hc θ) one_pos (hnull θ) v.2
    fun w hw => hv' ⟨w, hw⟩
  exact Subtype.ext h

variable {η : ℝ} (hrot : ∀ θ, q (θ + η) = rotP 1 (q θ))

include hδ hq hne hrot in
/-- The rotation by one vertex is a symmetry of the family shifting the parameter by η. -/
theorem formB_rot (θ : ℝ) (v w : normal (rotL (n := n) m N) m) :
    formB m N F q (θ + η) (rotV m N 1 v) (rotV m N 1 w) = formB m N F q θ v w := by
  have hP : amb (iterate m N (q (θ + η))) = rotA (m * N) 1 (amb (iterate m N (q θ))) := by
    have h1 := iterate_rotP m 1 (q θ)
    rw [Nat.cast_one, Nat.cast_one] at h1
    rw [hrot θ, h1, amb_rotP]
  have hf : ContDiffAt ℝ 2 (pen F (m * N) 1) (rotA (m * N) 1 (amb (iterate m N (q θ)))) := by
    rw [← hP]
    exact pen_contDiffAt_two F hδ (shortPolygon_iterate m N (hq (θ + η)))
      (iterate_ne m N (hne (θ + η))) 1
  rw [formB_apply, formB_apply, hP]
  exact sndDeriv_pen_rotA F 1 1 hf _ _

include hδ hq hne hrot in
theorem formB_rot_pow (j : ℕ) (θ : ℝ) (v w : normal (rotL (n := n) m N) m) :
    formB m N F q (θ + j * η) (((rotV (n := n) m N 1) ^ j) v) (((rotV (n := n) m N 1) ^ j) w) =
      formB m N F q θ v w := by
  induction j generalizing v w with
  | zero => rw [Nat.cast_zero, zero_mul, add_zero, pow_zero]; rfl
  | succ j ih =>
    have h1 : θ + ((j + 1 : ℕ) : ℝ) * η = θ + (j : ℝ) * η + η := by push_cast; ring
    rw [h1, pow_succ']
    change formB m N F q (θ + (j : ℝ) * η + η) (rotV m N 1 (((rotV (n := n) m N 1) ^ j) v))
      (rotV m N 1 (((rotV (n := n) m N 1) ^ j) w)) = _
    rw [formB_rot m N F hδ hq hne hrot, ih]

include hδ hcont hq hne hc hrot in
/-- **Closed negative and positive frames of the normal bundle.** -/
theorem exists_closed_frames {b s r : ℕ} (hr : 0 < r) (hη : 0 < η) (hN : s * (2 * r) = N)
    (hpar : Even s ∨ Odd m)
    (hper : ∀ θ, q (θ + ((2 * r : ℕ) : ℝ) * η) = q θ)
    (hnull : ∀ θ, nullity F (iterate m N (q θ)) = nullity F (q θ))
    (hidx : ∀ θ (hs : (hessian F (iterate m N (q θ))).toLinearMap.IsSymmetric)
      (hs₀ : (hessian F (q θ)).toLinearMap.IsSymmetric),
      index F (iterate m N (q θ)) hs = index F (q θ) hs₀ + b) :
    (∃ H : ℝ → Fin b → normal (rotL (n := n) m N) m, Continuous H ∧
      H (((2 * r : ℕ) : ℝ) * η) = H 0 ∧
      ∀ θ ∈ Icc 0 (((2 * r : ℕ) : ℝ) * η), Neg (formB m N F q θ) (H θ)) ∧
    ∃ H : ℝ → Fin (finrank ℝ (normal (rotL (n := n) m N) m) - b) →
        normal (rotL (n := n) m N) m, Continuous H ∧
      H (((2 * r : ℕ) : ℝ) * η) = H 0 ∧
      ∀ θ ∈ Icc 0 (((2 * r : ℕ) : ℝ) * η), Neg (-formB m N F q θ) (H θ) := by
  have hBcont := formB_continuous m N F hδ hcont hq hne
  have hBsym := formB_symm m N F hδ hq hne
  have hb := sigNeg_formB m N F hδ hq hne hc hidx
  have hF : Family (formB m N F q) b := family_of_sigNeg hBcont hBsym hb
  -- the positive index
  have hb' : ∀ θ, sigNeg (LinearMap.BilinMap.toQuadraticMap (-formB m N F q θ)) =
      finrank ℝ (normal (rotL (n := n) m N) m) - b := by
    intro θ
    have h1 := sigPos_add_sigNeg_add_ker (hBsym θ)
    rw [ker_formB m N F hδ hq hne hc hnull θ, finrank_bot, add_zero, hb θ] at h1
    rw [LinearMap.BilinMap.toQuadraticMap_neg, sigNeg_neg]
    omega
  have hF' : Family (fun θ => -formB m N F q θ)
      (finrank ℝ (normal (rotL (n := n) m N) m) - b) :=
    family_of_sigNeg (B := fun θ => -formB m N F q θ) hBcont.neg
      (fun θ v w => by
        change -(formB m N F q θ v w) = -(formB m N F q θ w v)
        rw [hBsym θ v w]) hb'
  -- the symmetry and the holonomy
  have hT : ∀ θ v w, formB m N F q (θ + η) (rotV m N 1 v) (rotV m N 1 w) = formB m N F q θ v w :=
    formB_rot m N F hδ hq hne hrot
  have hinv : ∀ v w, formB m N F q 0 (((rotV (n := n) m N 1) ^ (2 * r)) v)
      (((rotV (n := n) m N 1) ^ (2 * r)) w) = formB m N F q 0 v w := by
    intro v w
    have h := formB_rot_pow m N F hδ hq hne hrot (2 * r) 0 v w
    have hq0 : q (0 + ((2 * r : ℕ) : ℝ) * η) = q 0 := hper 0
    rw [formB_congr m N F q hq0] at h
    exact h
  -- the invariant positive definite form
  have hg : ∀ v w : normal (rotL (n := n) m N) m,
      (vertexForm (n := n) (m * N)).compl₁₂ (normal (rotL (n := n) m N) m).subtype
        (normal (rotL (n := n) m N) m).subtype v w =
      (vertexForm (n := n) (m * N)).compl₁₂ (normal (rotL (n := n) m N) m).subtype
        (normal (rotL (n := n) m N) m).subtype w v := fun v w => vertexForm_symm (m * N) _ _
  have hpos : ∀ v : normal (rotL (n := n) m N) m, v ≠ 0 →
      0 < (vertexForm (n := n) (m * N)).compl₁₂ (normal (rotL (n := n) m N) m).subtype
        (normal (rotL (n := n) m N) m).subtype v v := fun v hv =>
    vertexForm_pos (m * N) fun h => hv (Subtype.ext h)
  have hgT : ∀ v w : normal (rotL (n := n) m N) m,
      (vertexForm (n := n) (m * N)).compl₁₂ (normal (rotL (n := n) m N) m).subtype
        (normal (rotL (n := n) m N) m).subtype (((rotV (n := n) m N 1) ^ (2 * r)) v)
        (((rotV (n := n) m N 1) ^ (2 * r)) w) =
      (vertexForm (n := n) (m * N)).compl₁₂ (normal (rotL (n := n) m N) m).subtype
        (normal (rotL (n := n) m N) m).subtype v w := by
    intro v w
    change vertexForm (m * N)
      ((((rotV (n := n) m N 1) ^ (2 * r)) v : normal (rotL (n := n) m N) m) :
        ZMod (m * N) → Ambient n)
      ((((rotV (n := n) m N 1) ^ (2 * r)) w : normal (rotL (n := n) m N) m) :
        ZMod (m * N) → Ambient n) = vertexForm (m * N) (v : ZMod (m * N) → Ambient n) w
    rw [rotV_pow_coe, rotV_pow_coe, vertexForm_rotA]
  have hsa : (s : ZMod (m * N)) * (((2 * r : ℕ) : ZMod (m * N)) * 1) = (N : ZMod (m * N)) := by
    rw [mul_one, ← Nat.cast_mul, hN]
  have heig : ∀ (μ : ℝ) (x : normal (rotL (n := n) m N) m),
      ((rotV (n := n) m N 1) ^ (2 * r)) x = μ • x → x = 0 := by
    intro μ x hx
    have h1 := congrArg (Subtype.val) hx
    rw [rotV_pow_coe] at h1
    exact Subtype.ext (eq_zero_of_eigen m N hsa hpar x.2 h1)
  refine ⟨exists_closed_frame_of_invariant hF (hb 0) (rotV m N 1) hη hT hr hinv _ hg hpos hgT
    heig, ?_⟩
  refine exists_closed_frame_of_invariant hF' (hb' 0) (rotV m N 1) hη
    (fun θ v w => by
      change -(formB m N F q (θ + η) (rotV m N 1 v) (rotV m N 1 w)) = -(formB m N F q θ v w)
      rw [hT θ v w]) hr
    (fun v w => by
      change -(formB m N F q 0 (((rotV (n := n) m N 1) ^ (2 * r)) v)
        (((rotV (n := n) m N 1) ^ (2 * r)) w)) = -(formB m N F q 0 v w)
      rw [hinv v w]) _ hg hpos hgT heig

end Family

end

end Finsler.NormalFamily
