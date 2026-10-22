module

public import Finsler.Geometry.RoundCoords

/-! The QR decomposition of a pair of vectors and coordinates around the critical manifold.

For linearly independent A, B put x = A/‖A‖, r₁₂ = ⟪B, x⟫, u = (B − r₁₂ x)/‖B − r₁₂ x‖,
r₁₁ = ‖A‖ and r₂₂ = ‖B − r₁₂ x‖. Then (x, u) is orthonormal, A = r₁₁ x, B = r₁₂ x + r₂₂ u, and
conversely an orthonormal pair with r₁₁ > 0, r₂₂ > 0 has these QR data. With the Fourier
coordinates Q = regular N m (A_m Q) (B_m Q) + V this identifies the polygons with independent
m-th coefficients with V₂(ℝⁿ⁺¹) × (triangular data) × ker(A_m, B_m), explicitly; the critical
manifold of regular m-gons is the zero section r = (1, 0, 1), V = 0. -/

@[expose] public section

namespace Finsler.RoundQR

open Finsler.SphereGeometry Finsler.RoundPolygon Finsler.RoundCoords
open scoped RealInnerProductSpace Real

noncomputable section

variable {n : ℕ}

/-- The first Gram–Schmidt vector. -/
def gsx (A : Ambient n) : Ambient n := ‖A‖⁻¹ • A

/-- The off-diagonal entry. -/
def r12 (A B : Ambient n) : ℝ := ⟪B, gsx A⟫

/-- The second residual. -/
def res (A B : Ambient n) : Ambient n := B - r12 A B • gsx A

/-- The second Gram–Schmidt vector. -/
def gsu (A B : Ambient n) : Ambient n := ‖res A B‖⁻¹ • res A B

/-- The pairs of independent vectors (in the form used by Gram–Schmidt). -/
def Indep (A B : Ambient n) : Prop := A ≠ 0 ∧ res A B ≠ 0

theorem norm_gsx {A : Ambient n} (hA : A ≠ 0) : ‖gsx A‖ = 1 := by
  rw [gsx, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA)]

theorem inner_gsx_res {A B : Ambient n} (hA : A ≠ 0) : ⟪gsx A, res A B⟫ = 0 := by
  have h1 : ⟪gsx A, gsx A⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_gsx hA, one_pow]
  rw [res, inner_sub_right, real_inner_smul_right, h1, r12, real_inner_comm]
  ring

theorem norm_gsu {A B : Ambient n} (h : Indep A B) : ‖gsu A B‖ = 1 := by
  rw [gsu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h.2)]

theorem inner_gsx_gsu {A B : Ambient n} (h : Indep A B) : ⟪gsx A, gsu A B⟫ = 0 := by
  rw [gsu, real_inner_smul_right, inner_gsx_res h.1, mul_zero]

theorem A_eq {A : Ambient n} (hA : A ≠ 0) : A = ‖A‖ • gsx A := by
  rw [gsx, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hA), one_smul]

theorem B_eq {A B : Ambient n} (h : Indep A B) :
    B = r12 A B • gsx A + ‖res A B‖ • gsu A B := by
  rw [gsu, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h.2), one_smul, res]
  abel

/-- Gram–Schmidt fixes orthonormal pairs. -/
theorem gs_orthonormal {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0) :
    gsx x = x ∧ r12 x u = 0 ∧ res x u = u ∧ gsu x u = u := by
  have h1 : gsx x = x := by rw [gsx, hx, inv_one, one_smul]
  have h2 : r12 x u = 0 := by rw [r12, h1, real_inner_comm, hxu]
  have h3 : res x u = u := by rw [res, h2, zero_smul, sub_zero]
  refine ⟨h1, h2, h3, ?_⟩
  rw [gsu, h3, hu, inv_one, one_smul]

/-- The QR data of an orthonormal pair with a positive triangular factor. -/
theorem gs_triangular {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    gsx (a • x) = x ∧ r12 (a • x) (b • x + c • u) = b ∧ res (a • x) (b • x + c • u) = c • u ∧
      gsu (a • x) (b • x + c • u) = u := by
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h1 : gsx (a • x) = x := by
    rw [gsx, norm_smul, hx, mul_one, Real.norm_eq_abs, abs_of_pos ha, smul_smul,
      inv_mul_cancel₀ ha.ne', one_smul]
  have h2 : r12 (a • x) (b • x + c • u) = b := by
    rw [r12, h1, inner_add_left, real_inner_smul_left, real_inner_smul_left, hxx,
      real_inner_comm, hxu]
    ring
  have h3 : res (a • x) (b • x + c • u) = c • u := by
    rw [res, h2, h1]
    abel
  refine ⟨h1, h2, h3, ?_⟩
  rw [gsu, h3, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos hc, smul_smul,
    inv_mul_cancel₀ hc.ne', one_smul]

theorem continuousAt_gsx {A : Ambient n} (hA : A ≠ 0) : ContinuousAt gsx A := by
  unfold gsx
  exact ((continuous_norm.continuousAt).inv₀ (norm_ne_zero_iff.mpr hA)).smul continuousAt_id

theorem continuousAt_gs {A B : Ambient n} (h : Indep A B) :
    ContinuousAt (fun p : Ambient n × Ambient n => (gsx p.1, gsu p.1 p.2)) (A, B) := by
  have hx : ContinuousAt (fun p : Ambient n × Ambient n => gsx p.1) (A, B) :=
    ContinuousAt.comp (g := gsx) (f := fun p : Ambient n × Ambient n => p.1)
      (continuousAt_gsx h.1) continuousAt_fst
  have hr : ContinuousAt (fun p : Ambient n × Ambient n => res p.1 p.2) (A, B) := by
    have hi : ContinuousAt (fun p : Ambient n × Ambient n => ⟪p.2, gsx p.1⟫) (A, B) :=
      continuousAt_snd.inner hx
    have hs : ContinuousAt (fun p : Ambient n × Ambient n => ⟪p.2, gsx p.1⟫ • gsx p.1) (A, B) :=
      hi.smul hx
    unfold res r12
    exact continuousAt_snd.sub hs
  have hu : ContinuousAt (fun p : Ambient n × Ambient n => gsu p.1 p.2) (A, B) := by
    unfold gsu
    exact ((continuous_norm.continuousAt.comp hr).inv₀ (norm_ne_zero_iff.mpr h.2)).smul hr
  exact hx.prodMk hu

/-! ### Coordinates around the critical manifold -/

variable {N : ℕ} [NeZero N]

/-- A polygon whose m-th Fourier coefficients are independent. -/
def Good (m : ℕ) (Q : ZMod N → Ambient n) : Prop := Indep (coefA m Q) (coefB m Q)

/-- The frame of the critical manifold attached to a polygon. -/
def frameOf (m : ℕ) (Q : ZMod N → Ambient n) : Ambient n × Ambient n :=
  (gsx (coefA m Q), gsu (coefA m Q) (coefB m Q))

/-- The triangular data of a polygon. -/
def triOf (m : ℕ) (Q : ZMod N → Ambient n) : ℝ × ℝ × ℝ :=
  (‖coefA m Q‖, r12 (coefA m Q) (coefB m Q), ‖res (coefA m Q) (coefB m Q)‖)

/-- Reconstruction of a polygon from frame, triangular data and the rest. -/
def build (m : ℕ) (z : Ambient n × Ambient n) (t : ℝ × ℝ × ℝ) (V : ZMod N → Ambient n) :
    ZMod N → Ambient n :=
  regular N m (t.1 • z.1) (t.2.1 • z.1 + t.2.2 • z.2) + V

theorem frameOf_orthonormal {m : ℕ} {Q : ZMod N → Ambient n} (hQ : Good m Q) :
    ‖(frameOf m Q).1‖ = 1 ∧ ‖(frameOf m Q).2‖ = 1 ∧ ⟪(frameOf m Q).1, (frameOf m Q).2⟫ = 0 :=
  ⟨norm_gsx hQ.1, norm_gsu hQ, inner_gsx_gsu hQ⟩

/-- Every good polygon is rebuilt from its frame, triangular data and rest. -/
theorem build_frameOf {m : ℕ} {Q : ZMod N → Ambient n} (hQ : Good m Q) :
    build m (frameOf m Q) (triOf m Q) (Q - regPart m Q) = Q := by
  unfold build frameOf triOf regPart
  simp only
  rw [← A_eq hQ.1, ← B_eq hQ]
  abel

/-- The frame of a rebuilt polygon. -/
theorem frameOf_build {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N) {x u : Ambient n} (hx : ‖x‖ = 1)
    (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0) {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {V : ZMod N → Ambient n} (hV : V ∈ kern m) :
    Good m (build m (x, u) (a, b, c) V) ∧ frameOf m (build m (x, u) (a, b, c) V) = (x, u) ∧
      triOf m (build m (x, u) (a, b, c) V) = (a, b, c) ∧
      build m (x, u) (a, b, c) V - regPart m (build m (x, u) (a, b, c) V) = V := by
  rw [mem_kern] at hV
  have hA := coefA_regular (N := N) hm hmN hmN (a • x) (b • x + c • u)
  have hB := coefB_regular (N := N) hm hmN hmN (a • x) (b • x + c • u)
  rw [if_pos rfl] at hA hB
  have h1 : coefA m (build m (x, u) (a, b, c) V) = a • x := by
    rw [build, coefA_add, hA, hV.1, add_zero]
  have h2 : coefB m (build m (x, u) (a, b, c) V) = b • x + c • u := by
    rw [build, coefB_add, hB, hV.2, add_zero]
  obtain ⟨g1, g2, g3, g4⟩ := gs_triangular hx hu hxu (b := b) ha hc
  have hgood : Good m (build m (x, u) (a, b, c) V) := by
    unfold Good
    rw [h1, h2]
    refine ⟨?_, ?_⟩
    · intro h
      have := congrArg norm h
      rw [norm_smul, hx, mul_one, norm_zero, Real.norm_eq_abs, abs_of_pos ha] at this
      exact ha.ne' this
    · rw [g3]
      intro h
      have := congrArg norm h
      rw [norm_smul, hu, mul_one, norm_zero, Real.norm_eq_abs, abs_of_pos hc] at this
      exact hc.ne' this
  refine ⟨hgood, ?_, ?_, ?_⟩
  · unfold frameOf
    rw [h1, h2, g1, g4]
  · unfold triOf
    rw [h1, h2, g2, g3, norm_smul, hx, mul_one, Real.norm_eq_abs, abs_of_pos ha, norm_smul, hu,
      mul_one, Real.norm_eq_abs, abs_of_pos hc]
  · unfold regPart
    rw [h1, h2]
    unfold build
    abel

/-- The regular m-gons are the rebuilt polygons with r = (1, 0, 1) and V = 0. -/
theorem build_regular (m : ℕ) (x u : Ambient n) :
    build (N := N) m (x, u) (1, 0, 1) 0 = regular N m x u := by
  simp [build]

end

end Finsler.RoundQR
