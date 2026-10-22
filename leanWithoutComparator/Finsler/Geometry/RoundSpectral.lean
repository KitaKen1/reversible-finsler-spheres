module

public import Finsler.Geometry.RoundCoords
public import Finsler.Geometry.RoundModes

/-! The complete mode decomposition of polygons with an odd number of vertices.

For N = 2M + 1 the modes j = 0, …, M (the constant polygons for j = 0, the polygons
regular N j a b for j ≥ 1) span all polygons: the synthesis map from the coefficient space
Ambient × (Fin M → Ambient²) to the polygons is injective, because the Fourier coefficients
recover the coefficients (discrete orthogonality), and both spaces have dimension N (n + 1).
Hence every polygon is the sum of its modes, with the coefficients given by its Fourier
coefficients. No Dirichlet kernel is needed.

The orthogonal projection onto the normal space of the plane of an orthonormal pair (x, u),
applied to every vertex, commutes with the Fourier coefficients and with the modes. -/

@[expose] public section

namespace Finsler.RoundSpectral

open Finsler.SphereGeometry Finsler.RoundPolygon Finsler.RoundFourier Finsler.RoundCoords
open Finsler.RoundModes Finset Module
open scoped RealInnerProductSpace Real

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N]

/-! ### The constant coefficient -/

/-- The constant Fourier coefficient of a mode. -/
theorem coefA_zero_regular {j : ℕ} (hj : 2 * j < N) (a b : Ambient n) :
    coefA 0 (regular N j a b) = if j = 0 then (2 : ℝ) • a else 0 := by
  have hN : 0 < N := Nat.pos_of_neZero N
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold coefA
  simp only [regular_apply_natCast, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul]
  have h00 : 2 * 0 < N := by omega
  have hcos : ∀ k : ℕ, Real.cos (2 * π * ((0 : ℕ) : ℝ) / N * k) = 1 := fun k => by simp
  have hcc := sum_cos_cos hN h00 hj
  have hcs := sum_cos_sin hN h00 hj
  simp only [hcos, one_mul] at hcc hcs
  have e1 : ∑ k ∈ range N, Real.cos (2 * π * j / N * k) =
      if 0 = j then (if 0 = 0 then (N : ℝ) else N / 2) else 0 := hcc
  have e2 : ∑ k ∈ range N, Real.sin (2 * π * j / N * k) = 0 := hcs
  have hcos' : ∀ k : ℕ, Real.cos (2 * π * (0 : ℝ) / N * k) = 1 := fun k => by simp
  simp only [Nat.cast_zero, hcos', one_mul]
  rw [e1, e2, mul_zero, zero_smul, add_zero]
  by_cases h : j = 0
  · subst h
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    congr 1
    field_simp
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero, zero_smul]

/-! ### Coefficients and modes -/

/-- The coefficient pair of the mode j: for j = 0 the mean and zero, otherwise (A_j, B_j). -/
def coefPair (j : ℕ) (V : ZMod N → Ambient n) : Ambient n × Ambient n :=
  if j = 0 then ((1 / 2 : ℝ) • coefA 0 V, 0) else (coefA j V, coefB j V)

/-- The mode j of a polygon. -/
def mode (j : ℕ) (V : ZMod N → Ambient n) : ZMod N → Ambient n :=
  regular N j (coefPair j V).1 (coefPair j V).2

theorem coefPair_add (j : ℕ) (V V' : ZMod N → Ambient n) :
    coefPair j (V + V') = coefPair j V + coefPair j V' := by
  unfold coefPair
  split_ifs <;> simp [coefA_add, coefB_add, smul_add]

theorem coefPair_smul (j : ℕ) (r : ℝ) (V : ZMod N → Ambient n) :
    coefPair j (r • V) = r • coefPair j V := by
  unfold coefPair
  split_ifs <;> simp [coefA_smul, coefB_smul, smul_comm r]

theorem mode_add (j : ℕ) (V V' : ZMod N → Ambient n) :
    mode j (V + V') = mode j V + mode j V' := by
  unfold mode
  rw [coefPair_add, Prod.fst_add, Prod.snd_add, regular_add]

theorem mode_smul (j : ℕ) (r : ℝ) (V : ZMod N → Ambient n) :
    mode j (r • V) = r • mode j V := by
  unfold mode
  rw [coefPair_smul, Prod.smul_fst, Prod.smul_snd, regular_smul]

/-- The coefficient pairs of a mode. -/
theorem coefPair_regular {j j' : ℕ} (hj : 2 * j < N) (hj' : 2 * j' < N) (a b : Ambient n) :
    coefPair j (regular N j' a b) =
      if j = j' then (if j = 0 then (a, 0) else (a, b)) else 0 := by
  unfold coefPair
  by_cases h0 : j = 0
  · subst h0
    rw [if_pos rfl, coefA_zero_regular hj']
    by_cases h : 0 = j'
    · subst h
      rw [if_pos rfl, if_pos rfl, if_pos rfl, smul_smul]
      norm_num
    · rw [if_neg (Ne.symm h), if_neg h, smul_zero]
      rfl
  · rw [if_neg h0, coefA_regular (Nat.pos_of_ne_zero h0) hj hj',
      coefB_regular (Nat.pos_of_ne_zero h0) hj hj']
    by_cases h : j = j'
    · rw [if_pos h, if_pos h, if_pos h, if_neg h0]
    · rw [if_neg h, if_neg h, if_neg h]
      rfl

/-- The constant mode does not depend on its second coefficient. -/
theorem regular_zero (a b : Ambient n) : regular N 0 a b = regular N 0 a 0 := by
  funext i
  simp [regular, circ]

/-- The mode j of a mode j'. -/
theorem mode_regular {j j' : ℕ} (hj : 2 * j < N) (hj' : 2 * j' < N) (a b : Ambient n) :
    mode j (regular N j' a b) = if j = j' then regular N j' a b else 0 := by
  unfold mode
  rw [coefPair_regular hj hj']
  by_cases h : j = j'
  · subst h
    rw [if_pos rfl, if_pos rfl]
    by_cases h0 : j = 0
    · subst h0
      rw [if_pos rfl]
      exact (regular_zero a b).symm
    · rw [if_neg h0]
  · rw [if_neg h, if_neg h]
    funext i
    simp [regular, circ]

theorem coefA_sum {ι : Type*} (s : Finset ι) (j : ℕ) (f : ι → ZMod N → Ambient n) :
    coefA j (∑ i ∈ s, f i) = ∑ i ∈ s, coefA j (f i) :=
  map_sum (coefAL (n := n) (N := N) j) f s

theorem coefB_sum {ι : Type*} (s : Finset ι) (j : ℕ) (f : ι → ZMod N → Ambient n) :
    coefB j (∑ i ∈ s, f i) = ∑ i ∈ s, coefB j (f i) :=
  map_sum (coefBL (n := n) (N := N) j) f s

/-! ### Completeness for an odd number of vertices -/

section Complete

variable (M : ℕ)

/-- The coefficient space of the modes 0, …, M. -/
abbrev Coef (n M : ℕ) := Ambient n × (Fin M → Ambient n × Ambient n)

/-- The synthesis of a polygon from its mode coefficients. -/
def synth : Coef n M →ₗ[ℝ] (ZMod N → Ambient n) where
  toFun c := regular N 0 c.1 0 + ∑ i : Fin M, regular N (i + 1) (c.2 i).1 (c.2 i).2
  map_add' c c' := by
    have h0 : regular N 0 (c.1 + c'.1) (0 : Ambient n) = regular N 0 c.1 0 + regular N 0 c'.1 0 := by
      rw [← regular_add, add_zero]
    have hs : ∀ i : Fin M, regular N ((i : ℕ) + 1) ((c + c').2 i).1 ((c + c').2 i).2 =
        regular N ((i : ℕ) + 1) (c.2 i).1 (c.2 i).2 + regular N ((i : ℕ) + 1) (c'.2 i).1 (c'.2 i).2 :=
      fun i => regular_add _ _ _ _ _
    change regular N 0 (c.1 + c'.1) 0 + ∑ i : Fin M, regular N ((i : ℕ) + 1) ((c + c').2 i).1
      ((c + c').2 i).2 = _
    rw [h0, Finset.sum_congr rfl fun i _ => hs i, Finset.sum_add_distrib, add_add_add_comm]
  map_smul' r c := by
    have h0 : regular N 0 (r • c.1) (0 : Ambient n) = r • regular N 0 c.1 0 := by
      rw [← regular_smul, smul_zero]
    have hs : ∀ i : Fin M, regular N ((i : ℕ) + 1) ((r • c).2 i).1 ((r • c).2 i).2 =
        r • regular N ((i : ℕ) + 1) (c.2 i).1 (c.2 i).2 := fun i => regular_smul _ _ _ _
    change regular N 0 (r • c.1) 0 + ∑ i : Fin M, regular N ((i : ℕ) + 1) ((r • c).2 i).1
      ((r • c).2 i).2 = _
    rw [h0, Finset.sum_congr rfl fun i _ => hs i, ← Finset.smul_sum, ← smul_add]
    rfl

/-- The mode coefficients of a polygon. -/
def coefMap : (ZMod N → Ambient n) →ₗ[ℝ] Coef n M where
  toFun V := ((1 / 2 : ℝ) • coefA 0 V, fun i => (coefA (i + 1) V, coefB (i + 1) V))
  map_add' V V' := by
    refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_)
    · simp [coefA_add, smul_add]
    · simp [coefA_add]
    · simp [coefB_add]
  map_smul' r V := by
    refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_)
    · simp [coefA_smul, smul_comm r]
    · simp [coefA_smul]
    · simp [coefB_smul]

variable {M}

/-- The coefficients recover the coefficients. -/
theorem coefMap_synth (hNM : N = 2 * M + 1) (c : Coef n M) :
    coefMap (N := N) M (synth (N := N) M c) = c := by
  have hlt : ∀ i : Fin M, 2 * ((i : ℕ) + 1) < N := fun i => by have := i.2; omega
  have h0 : 2 * 0 < N := by omega
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_)
  · change (1 / 2 : ℝ) • coefA 0 (regular N 0 c.1 0 + ∑ i : Fin M,
      regular N (i + 1) (c.2 i).1 (c.2 i).2) = c.1
    rw [coefA_add, coefA_zero_regular h0, if_pos rfl]
    have hs : coefA 0 (∑ i : Fin M, regular N (i + 1) (c.2 i).1 (c.2 i).2) = (0 : Ambient n) := by
      rw [coefA_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [coefA_zero_regular (hlt i), if_neg (by omega)]
    rw [hs, add_zero, smul_smul]
    norm_num
  · change coefA (i + 1) (regular N 0 c.1 0 + ∑ i : Fin M,
      regular N (i + 1) (c.2 i).1 (c.2 i).2) = (c.2 i).1
    rw [coefA_add, coefA_regular (by omega) (hlt i) h0, if_neg (by omega), zero_add, coefA_sum]
    rw [Finset.sum_eq_single i]
    · rw [coefA_regular (by omega) (hlt i) (hlt i), if_pos rfl]
    · intro k _ hk
      rw [coefA_regular (by omega) (hlt i) (hlt k), if_neg]
      intro h
      exact hk (Fin.ext (by omega))
    · intro h
      exact absurd (Finset.mem_univ i) h
  · change coefB (i + 1) (regular N 0 c.1 0 + ∑ i : Fin M,
      regular N (i + 1) (c.2 i).1 (c.2 i).2) = (c.2 i).2
    rw [coefB_add, coefB_regular (by omega) (hlt i) h0, if_neg (by omega), zero_add, coefB_sum]
    rw [Finset.sum_eq_single i]
    · rw [coefB_regular (by omega) (hlt i) (hlt i), if_pos rfl]
    · intro k _ hk
      rw [coefB_regular (by omega) (hlt i) (hlt k), if_neg]
      intro h
      exact hk (Fin.ext (by omega))
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem finrank_coef : finrank ℝ (Coef n M) = (n + 1) * (2 * M + 1) := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_prod]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
  ring

theorem finrank_poly : finrank ℝ (ZMod N → Ambient n) = N * (n + 1) := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_euclideanSpace, ZMod.card]

/-- **Completeness.** For N = 2M + 1 every polygon is the synthesis of its coefficients. -/
theorem synth_coefMap (hNM : N = 2 * M + 1) (V : ZMod N → Ambient n) :
    synth (N := N) M (coefMap (N := N) M V) = V := by
  have hinj : Function.Injective (synth (n := n) (N := N) M) := fun c c' h => by
    have := congrArg (coefMap (n := n) (N := N) M) h
    rwa [coefMap_synth hNM, coefMap_synth hNM] at this
  have hdim : finrank ℝ (Coef n M) = finrank ℝ (ZMod N → Ambient n) := by
    rw [finrank_coef, finrank_poly, hNM]
    ring
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨c, rfl⟩ := hsurj V
  rw [coefMap_synth hNM]

/-- **Every polygon is the sum of its modes.** -/
theorem sum_mode (hNM : N = 2 * M + 1) (V : ZMod N → Ambient n) :
    ∑ j ∈ range (M + 1), mode j V = V := by
  conv_rhs => rw [← synth_coefMap hNM V]
  rw [Finset.sum_range_succ']
  change _ = regular N 0 ((1 / 2 : ℝ) • coefA 0 V) 0 +
    ∑ i : Fin M, regular N (i + 1) (coefA (i + 1) V) (coefB (i + 1) V)
  rw [add_comm, Fin.sum_univ_eq_sum_range (fun i => regular N (i + 1) (coefA (i + 1) V)
    (coefB (i + 1) V))]
  congr 1

end Complete

/-! ### Projections commuting with the modes -/

/-- The projection onto the normal space of the plane of (x, u). -/
def projW (z : Ambient n × Ambient n) : Ambient n →L[ℝ] Ambient n :=
  ContinuousLinearMap.id ℝ (Ambient n) -
    ((innerSL ℝ z.1).smulRight z.1 + (innerSL ℝ z.2).smulRight z.2)

theorem projW_apply (z : Ambient n × Ambient n) (v : Ambient n) :
    projW z v = v - (⟪z.1, v⟫ • z.1 + ⟪z.2, v⟫ • z.2) := rfl

/-- Vertexwise application of a linear map. -/
def onVert (f : Ambient n →L[ℝ] Ambient n) : (ZMod N → Ambient n) →L[ℝ] (ZMod N → Ambient n) :=
  ContinuousLinearMap.pi fun i => f.comp (ContinuousLinearMap.proj i)

theorem onVert_apply (f : Ambient n →L[ℝ] Ambient n) (V : ZMod N → Ambient n) (i : ZMod N) :
    onVert f V i = f (V i) := rfl

theorem coefA_onVert (f : Ambient n →L[ℝ] Ambient n) (j : ℕ) (V : ZMod N → Ambient n) :
    coefA j (onVert f V) = f (coefA j V) := by
  unfold coefA
  simp only [onVert_apply, map_smul, map_sum]

theorem coefB_onVert (f : Ambient n →L[ℝ] Ambient n) (j : ℕ) (V : ZMod N → Ambient n) :
    coefB j (onVert f V) = f (coefB j V) := by
  unfold coefB
  simp only [onVert_apply, map_smul, map_sum]

theorem onVert_regular (f : Ambient n →L[ℝ] Ambient n) (j : ℕ) (a b : Ambient n) :
    onVert (N := N) f (regular N j a b) = regular N j (f a) (f b) := by
  funext i
  simp [onVert_apply, regular, circ]

theorem mode_onVert (f : Ambient n →L[ℝ] Ambient n) (j : ℕ) (V : ZMod N → Ambient n) :
    mode j (onVert f V) = onVert f (mode j V) := by
  unfold mode coefPair
  split_ifs
  · rw [onVert_regular, coefA_onVert, map_smul, map_zero]
  · rw [onVert_regular, coefA_onVert, coefB_onVert]

/-- The projection is idempotent on orthonormal pairs. -/
theorem projW_projW {z : Ambient n × Ambient n} (hx : ‖z.1‖ = 1) (hu : ‖z.2‖ = 1)
    (hxu : ⟪z.1, z.2⟫ = 0) (v : Ambient n) : projW z (projW z v) = projW z v := by
  have hxx : ⟪z.1, z.1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have huu : ⟪z.2, z.2⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hux : ⟪z.2, z.1⟫ = 0 := by rw [real_inner_comm, hxu]
  simp only [projW_apply, inner_sub_right, inner_add_right, real_inner_smul_right, hxx, huu, hxu,
    hux]
  simp

/-- The projection is orthogonal to the plane. -/
theorem inner_projW {z : Ambient n × Ambient n} (hx : ‖z.1‖ = 1) (hu : ‖z.2‖ = 1)
    (hxu : ⟪z.1, z.2⟫ = 0) (v : Ambient n) : ⟪z.1, projW z v⟫ = 0 ∧ ⟪z.2, projW z v⟫ = 0 := by
  have hxx : ⟪z.1, z.1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have huu : ⟪z.2, z.2⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hux : ⟪z.2, z.1⟫ = 0 := by rw [real_inner_comm, hxu]
  simp only [projW_apply, inner_sub_right, inner_add_right, real_inner_smul_right, hxx, huu, hxu,
    hux]
  constructor <;> ring

/-- A vector is its projection plus its part in the plane. -/
theorem projW_add_plane (z : Ambient n × Ambient n) (v : Ambient n) :
    v = projW z v + (⟪z.1, v⟫ • z.1 + ⟪z.2, v⟫ • z.2) := by
  rw [projW_apply]
  abel

end

end Finsler.RoundSpectral
