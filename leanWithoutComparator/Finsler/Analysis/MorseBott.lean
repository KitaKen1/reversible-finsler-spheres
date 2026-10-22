module

public import Finsler.Analysis.SplittingLemma

/-! The Morse–Bott normal form along an invariant subspace containing the kernel. Let f be a
function on a finite-dimensional real inner product space with gradient G near p, G of class C²
at p with symmetric derivative A, and let K be a subspace which is invariant under A and
contains the kernel of A. Suppose that the component of the gradient normal to K vanishes at
the points p + w with w in K near 0 (symmetric criticality). Then there is a C¹ map Ξ, tangent
to the identity at 0 and preserving the component in K, with
f(p + z) = f(p + P z) + ½ ⟪A (N Ξ z), N Ξ z⟫ near 0, where P is the orthogonal projection onto
K and N = 1 - P. The point p need not be critical for f. The proof applies the degenerate
splitting lemma to the difference f(x) - f(q(x)), where q is the affine projection onto p + K:
its Hessian at p is A N, with kernel K, and its reduction map is the identity on K. -/

@[expose] public section

namespace Finsler.MorseBott

open Filter Finsler.LyapunovSchmidt
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The two projections -/

section Linear

variable (K : Submodule ℝ E)

/-- The orthogonal projection onto K. -/
def tanProj : E →L[ℝ] E := K.starProjection

/-- The complementary projection. -/
def norProj : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - tanProj K

theorem norProj_apply (v : E) : norProj K v = v - tanProj K v := rfl

theorem norProj_add_tanProj (v : E) : norProj K v + tanProj K v = v := by
  rw [norProj_apply]
  abel

theorem tanProj_mem (v : E) : tanProj K v ∈ K := K.starProjection_apply_mem v

theorem tanProj_of_mem {v : E} (hv : v ∈ K) : tanProj K v = v :=
  Submodule.starProjection_eq_self_iff.mpr hv

theorem tanProj_tanProj (v : E) : tanProj K (tanProj K v) = tanProj K v :=
  tanProj_of_mem K (tanProj_mem K v)

theorem inner_tanProj (u v : E) : ⟪tanProj K u, v⟫ = ⟪u, tanProj K v⟫ :=
  Submodule.inner_starProjection_left_eq_right _ u v

theorem norProj_of_mem {v : E} (hv : v ∈ K) : norProj K v = 0 := by
  rw [norProj_apply, tanProj_of_mem K hv, sub_self]

theorem tanProj_norProj (v : E) : tanProj K (norProj K v) = 0 := by
  rw [norProj_apply, map_sub, tanProj_tanProj, sub_self]

theorem mem_of_norProj {v : E} (hv : norProj K v = 0) : v ∈ K := by
  have h : v = tanProj K v := sub_eq_zero.mp hv
  rw [h]
  exact tanProj_mem K v

/-- The affine projection onto p + K, at a point p + z. -/
theorem norProj_add_tanProj_add (p z : E) :
    norProj K p + tanProj K (p + z) = p + tanProj K z := by
  rw [map_add, norProj_apply]
  abel

/-- The operator A - P A P; under invariance it is A N. -/
def normalOp (A : E →L[ℝ] E) : E →L[ℝ] E := A - (tanProj K).comp (A.comp (tanProj K))

variable {K} {A : E →L[ℝ] E} (hs : A.toLinearMap.IsSymmetric) (hK : ∀ v ∈ K, A v ∈ K)

include hs hK in
/-- A symmetric operator which preserves K commutes with the projection onto K. -/
theorem tanProj_map (v : E) : tanProj K (A v) = A (tanProj K v) := by
  have h1 : tanProj K (A (tanProj K v)) = A (tanProj K v) :=
    tanProj_of_mem K (hK _ (tanProj_mem K v))
  have h2 : tanProj K (A (norProj K v)) = 0 := by
    refine (Submodule.starProjection_apply_eq_zero_iff _).mpr ?_
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h : ⟪A u, norProj K v⟫ = ⟪u, A (norProj K v)⟫ := hs u (norProj K v)
    rw [← h, ← tanProj_of_mem K (hK u hu), inner_tanProj, tanProj_norProj, inner_zero_right]
  have h3 : A v = A (norProj K v) + A (tanProj K v) := by
    rw [← map_add, norProj_add_tanProj]
  rw [h3, map_add, h1, h2, zero_add]

include hs hK in
theorem normalOp_apply (v : E) : normalOp K A v = A (norProj K v) := by
  change A v - tanProj K (A (tanProj K v)) = A (norProj K v)
  rw [tanProj_map hs hK, tanProj_tanProj, norProj_apply, map_sub]

include hs in
theorem normalOp_isSymmetric : (normalOp K A).toLinearMap.IsSymmetric := by
  intro v w
  change ⟪A v - tanProj K (A (tanProj K v)), w⟫ = ⟪v, A w - tanProj K (A (tanProj K w))⟫
  have h1 : ⟪A v, w⟫ = ⟪v, A w⟫ := hs v w
  have h2 : ⟪A (tanProj K v), tanProj K w⟫ = ⟪tanProj K v, A (tanProj K w)⟫ := hs _ _
  rw [inner_sub_left, inner_sub_right, inner_tanProj K (A (tanProj K v)) w,
    ← inner_tanProj K v (A (tanProj K w)), h1, h2]

include hs hK in
/-- The quadratic form of the normal operator only sees the normal component. -/
theorem inner_normalOp (y : E) :
    ⟪normalOp K A y, y⟫ = ⟪A (norProj K y), norProj K y⟫ := by
  have h : ⟪A (norProj K y), tanProj K y⟫ = 0 := by
    rw [← inner_tanProj, tanProj_map hs hK, tanProj_norProj, map_zero, inner_zero_left]
  have e : ⟪A (norProj K y), y⟫ =
      ⟪A (norProj K y), norProj K y⟫ + ⟪A (norProj K y), tanProj K y⟫ := by
    rw [← inner_add_right, norProj_add_tanProj]
  rw [normalOp_apply hs hK, e, h, add_zero]

include hs hK in
/-- If K contains the kernel of A, the kernel of the normal operator is K. -/
theorem ker_normalOp (hker : LinearMap.ker A.toLinearMap ≤ K) :
    LinearMap.ker (normalOp K A).toLinearMap = K := by
  ext v
  rw [LinearMap.mem_ker]
  change normalOp K A v = 0 ↔ v ∈ K
  rw [normalOp_apply hs hK]
  constructor
  · intro h
    have h1 : norProj K v ∈ K := hker (LinearMap.mem_ker.mpr h)
    have h2 := tanProj_of_mem K h1
    rw [tanProj_norProj] at h2
    exact mem_of_norProj K h2.symm
  · intro h
    rw [norProj_of_mem K h, map_zero]

include hs hK in
theorem kerProj_normalOp (hker : LinearMap.ker A.toLinearMap ≤ K) :
    kerProj (normalOp K A) = tanProj K := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hK' := ker_normalOp hs hK hker
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · rw [hK']
    exact tanProj_mem K v
  · rw [hK'] at hw
    have h : ⟪norProj K v, tanProj K w⟫ = 0 := by
      rw [← inner_tanProj, tanProj_norProj, inner_zero_left]
    rw [tanProj_of_mem K hw] at h
    exact h

end Linear

/-! ### The normal form -/

section Normal

variable {K : Submodule ℝ E} {A : E →L[ℝ] E} (hs : A.toLinearMap.IsSymmetric)
  (hK : ∀ v ∈ K, A v ∈ K) (hker : LinearMap.ker A.toLinearMap ≤ K)
  {G : E → E} {p : E} {f : E → ℝ}

include hs hK hker in
/-- **The Morse–Bott normal form.** -/
theorem exists_normal_form (hG : ContDiffAt ℝ 2 G p) (hA : HasFDerivAt G A p)
    (hf : ∀ᶠ x in 𝓝 p, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hsym : ∀ᶠ w in 𝓝 (0 : E), w ∈ K → norProj K (G (p + w)) = 0) :
    ∃ Ξ : E → E, ContDiffAt ℝ 1 Ξ 0 ∧ Ξ 0 = 0 ∧
      HasStrictFDerivAt Ξ (ContinuousLinearMap.id ℝ E) 0 ∧
      (∀ᶠ z in 𝓝 (0 : E), tanProj K (Ξ z) = tanProj K z) ∧
      ∀ᶠ z in 𝓝 (0 : E), f (p + z) =
        f (p + tanProj K z) + 1 / 2 * ⟪A (norProj K (Ξ z)), norProj K (Ξ z)⟫ := by
  -- the affine projection onto p + K
  set π : E → E := fun x => norProj K p + tanProj K x with hπ
  have hπp : π p = p := norProj_add_tanProj K p
  have hπd : ∀ x, HasFDerivAt π (tanProj K) x := fun x =>
    (tanProj K).hasFDerivAt.const_add (norProj K p)
  have hπc : ContDiffAt ℝ 2 π p := contDiffAt_const.add (tanProj K).contDiff.contDiffAt
  have hπt : Tendsto π (𝓝 p) (𝓝 p) := by
    have h := (hπd p).continuousAt.tendsto
    rwa [hπp] at h
  -- the difference function and its gradient
  set Ĝ : E → E := fun x => G x - tanProj K (G (π x)) with hĜdef
  set g : E → ℝ := fun x => f x - f (π x) with hgdef
  have hGπ : ContDiffAt ℝ 2 G (π p) := by rw [hπp]; exact hG
  have hĜ : ContDiffAt ℝ 2 Ĝ p :=
    hG.sub ((tanProj K).contDiff.contDiffAt.comp p (hGπ.comp p hπc))
  have hAπ : HasFDerivAt G A (π p) := by rw [hπp]; exact hA
  have hÂ : HasFDerivAt Ĝ (normalOp K A) p :=
    hA.sub ((tanProj K).hasFDerivAt.comp p (hAπ.comp p (hπd p)))
  have h0 : norProj K (G p) = 0 := by
    have h := hsym.self_of_nhds (zero_mem K)
    rwa [add_zero] at h
  have hp : Ĝ p = 0 := by
    change G p - tanProj K (G (π p)) = 0
    rw [hπp]
    exact h0
  have hg : ∀ᶠ x in 𝓝 p, HasFDerivAt g (innerSL ℝ (Ĝ x)) x := by
    filter_upwards [hf, hπt.eventually hf] with x hx hxπ
    have h1 : HasFDerivAt (fun x => f (π x)) ((innerSL ℝ (G (π x))).comp (tanProj K)) x :=
      hxπ.comp x (hπd x)
    have h2 : (innerSL ℝ (G (π x))).comp (tanProj K) = innerSL ℝ (tanProj K (G (π x))) := by
      refine ContinuousLinearMap.ext fun v => ?_
      change ⟪G (π x), tanProj K v⟫ = ⟪tanProj K (G (π x)), v⟫
      rw [inner_tanProj]
    rw [h2] at h1
    have h3 := hx.sub h1
    rw [← map_sub] at h3
    exact h3
  obtain ⟨σ, Ξ, -, -, -, hσl, -, hΞ1, hΞ0, hΞd, hΞP, hΞf⟩ :=
    SplittingLemma.exists_splitting (normalOp_isSymmetric hs) hĜ hÂ hp hg
  rw [kerProj_normalOp hs hK hker] at hσl hΞP hΞf
  -- the reduction map is the identity on K
  have hσK : ∀ᶠ w in 𝓝 (0 : E), w ∈ K → σ w = w := by
    filter_upwards [hσl, hsym] with w hw hsw hwK
    have hĜw : Ĝ (p + w) = 0 := by
      change G (p + w) - tanProj K (G (norProj K p + tanProj K (p + w))) = 0
      rw [norProj_add_tanProj_add, tanProj_of_mem K hwK]
      exact hsw hwK
    have h := hw (by rw [hĜw, map_zero])
    rwa [tanProj_of_mem K hwK] at h
  have htan : Tendsto (fun z : E => tanProj K z) (𝓝 0) (𝓝 0) := by
    have h := (tanProj K).continuous.tendsto 0
    rwa [map_zero] at h
  refine ⟨Ξ, hΞ1, hΞ0, hΞd, hΞP, ?_⟩
  filter_upwards [hΞf, htan.eventually hσK] with z hz hσz
  have h1 : σ (tanProj K z) = tanProj K z := hσz (tanProj_mem K z)
  have h2 : g (p + tanProj K z) = 0 := by
    change f (p + tanProj K z) - f (norProj K p + tanProj K (p + tanProj K z)) = 0
    rw [norProj_add_tanProj_add, tanProj_tanProj, sub_self]
  have h3 : g (p + z) = f (p + z) - f (p + tanProj K z) := by
    change f (p + z) - f (norProj K p + tanProj K (p + z)) = _
    rw [norProj_add_tanProj_add]
  rw [h1, h2, zero_add, h3, inner_normalOp hs hK] at hz
  linarith

end Normal

end

end Finsler.MorseBott
