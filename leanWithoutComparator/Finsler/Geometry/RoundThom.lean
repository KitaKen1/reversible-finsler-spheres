module

public import Finsler.Geometry.RoundCone
public import Finsler.Topology.PairSuspensionProduct

/-! The negative bundle of the regular m-gons and its Thom pair, via stabilization.

The negative bundle ν⁻ = {sqP = 0} of the model consists of the pairs z ∈ V₂ with a low
polygon V = negV z V; its fibre is (normal space of the plane of z)^{2m−1}, a nontrivial bundle.
Coefficients of the low modes identify V with a vector of 2m − 1 normal vectors. Adding two
vectors of 2m − 1 scalars s, s' (the coefficients along x and u) gives

  ν⁻ × (ℝ^{2m−1})² ≅ V₂ × (ℝⁿ⁺¹)^{2m−1},   (z, V, s, s') ↦ (z, coef V + s x + s' u),

a homeomorphism under which the zero section times zero corresponds to the zero section. With
the suspension isomorphism for products with ℝ^b (`PairSuspensionProduct`) on both sides, the Thom
pair (ν⁻, ν⁻ ∖ 0) has the cohomology of V₂ shifted by (2m − 1)(n + 1) − 2(2m − 1) = (2m − 1)(n − 1). -/

@[expose] public section

namespace Finsler.RoundThom

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon
open Finsler.RoundCoords Finsler.RoundSpectral Finsler.RoundModes Finsler.AmbientPenalty
open Finsler.RoundChart Finsler.RoundSplit Finsler.RoundLabel Finsler.RoundModel
open Finsler.RoundCone Finsler.ConeLens Finsler.FlowLens
open Finset Filter Set Metric
open scoped RealInnerProductSpace Real Topology ContDiff

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N] {m : ℕ}

/-! ### Coefficients of low polygons -/

/-- The coefficients of the low modes. -/
abbrev CoefL (n m : ℕ) := Ambient n × (Fin (m - 1) → Ambient n × Ambient n)

/-- Scalar coefficients of the low modes. -/
abbrev CoefS (m : ℕ) := ℝ × (Fin (m - 1) → ℝ × ℝ)

/-- The low polygon with given coefficients. -/
def synL (c : CoefL n m) : ZMod N → Ambient n :=
  regular N 0 c.1 0 + ∑ i : Fin (m - 1), regular N ((i : ℕ) + 1) (c.2 i).1 (c.2 i).2

/-- The low coefficients of a polygon. -/
def coefL (V : ZMod N → Ambient n) : CoefL n m :=
  ((1 / 2 : ℝ) • coefA 0 V, fun i => (coefA ((i : ℕ) + 1) V, coefB ((i : ℕ) + 1) V))

/-- Coefficientwise application of a linear map. -/
def mapC (f : Ambient n →L[ℝ] Ambient n) (c : CoefL n m) : CoefL n m :=
  (f c.1, fun i => (f (c.2 i).1, f (c.2 i).2))

/-- The coefficients along a vector. -/
def innerC (v : Ambient n) (c : CoefL n m) : CoefS m :=
  (⟪v, c.1⟫, fun i => (⟪v, (c.2 i).1⟫, ⟪v, (c.2 i).2⟫))

/-- The in-plane coefficients s x + s' u. -/
def plane (z : Ambient n × Ambient n) (s s' : CoefS m) : CoefL n m :=
  (s.1 • z.1 + s'.1 • z.2, fun i => ((s.2 i).1 • z.1 + (s'.2 i).1 • z.2,
    (s.2 i).2 • z.1 + (s'.2 i).2 • z.2))

theorem coefL_synL (hmN : 2 * m < N) (c : CoefL n m) : coefL (N := N) (synL c) = c := by
  have hlt : ∀ i : Fin (m - 1), 2 * ((i : ℕ) + 1) < N := fun i => by have := i.2; omega
  have h0 : 2 * 0 < N := by omega
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_)
  · change (1 / 2 : ℝ) • coefA 0 (regular N 0 c.1 0 + ∑ i : Fin (m - 1),
      regular N ((i : ℕ) + 1) (c.2 i).1 (c.2 i).2) = c.1
    rw [coefA_add, coefA_zero_regular h0, if_pos rfl, coefA_sum]
    rw [Finset.sum_eq_zero fun i _ => by rw [coefA_zero_regular (hlt i), if_neg (by omega)]]
    rw [add_zero, smul_smul]
    norm_num
  · change coefA ((i : ℕ) + 1) (regular N 0 c.1 0 + ∑ i : Fin (m - 1),
      regular N ((i : ℕ) + 1) (c.2 i).1 (c.2 i).2) = (c.2 i).1
    rw [coefA_add, coefA_regular (by omega) (hlt i) h0, if_neg (by omega), zero_add, coefA_sum,
      Finset.sum_eq_single i]
    · rw [coefA_regular (by omega) (hlt i) (hlt i), if_pos rfl]
    · intro k _ hk
      rw [coefA_regular (by omega) (hlt i) (hlt k), if_neg]
      intro h
      exact hk (Fin.ext (by omega))
    · intro h
      exact absurd (Finset.mem_univ i) h
  · change coefB ((i : ℕ) + 1) (regular N 0 c.1 0 + ∑ i : Fin (m - 1),
      regular N ((i : ℕ) + 1) (c.2 i).1 (c.2 i).2) = (c.2 i).2
    rw [coefB_add, coefB_regular (by omega) (hlt i) h0, if_neg (by omega), zero_add, coefB_sum,
      Finset.sum_eq_single i]
    · rw [coefB_regular (by omega) (hlt i) (hlt i), if_pos rfl]
    · intro k _ hk
      rw [coefB_regular (by omega) (hlt i) (hlt k), if_neg]
      intro h
      exact hk (Fin.ext (by omega))
    · intro h
      exact absurd (Finset.mem_univ i) h

/-- A low polygon is the synthesis of its low coefficients. -/
theorem synL_coefL (hm : 0 < m) (V : ZMod N → Ambient n) : synL (coefL (m := m) V) = low m V := by
  unfold low
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ']
  unfold synL coefL
  rw [add_comm]
  congr 1
  · change ∑ i : Fin k, regular N ((i : ℕ) + 1) (coefA ((i : ℕ) + 1) V) (coefB ((i : ℕ) + 1) V) = _
    rw [Fin.sum_univ_eq_sum_range (fun i => regular N (i + 1) (coefA (i + 1) V)
      (coefB (i + 1) V)) k]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mode, coefPair]
  all_goals try simp [mode, coefPair]

theorem mapC_coefL (f : Ambient n →L[ℝ] Ambient n) (V : ZMod N → Ambient n) :
    mapC f (coefL (m := m) V) = coefL (m := m) (onVert f V) := by
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_)
  · change f ((1 / 2 : ℝ) • coefA 0 V) = (1 / 2 : ℝ) • coefA 0 (onVert f V)
    rw [coefA_onVert, map_smul]
  · exact (coefA_onVert f _ V).symm
  · exact (coefB_onVert f _ V).symm

section Pair

variable {z : Ambient n × Ambient n} (hz : z ∈ V2)
include hz

theorem mapC_projW_plane (s s' : CoefS m) : mapC (projW z) (plane z s s') = 0 := by
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_) <;>
    simp [mapC, plane, map_add, map_smul, projW_fst hz, projW_snd hz]

theorem innerC_plane_fst (s s' : CoefS m) : innerC z.1 (plane z s s') = s := by
  obtain ⟨hx, -, hxu⟩ := hz
  have hxx : ⟪z.1, z.1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_) <;>
    simp [innerC, plane, inner_add_right, real_inner_smul_right, hxx, hxu, hx]

theorem innerC_plane_snd (s s' : CoefS m) : innerC z.2 (plane z s s') = s' := by
  obtain ⟨-, hu, hxu⟩ := hz
  have huu : ⟪z.2, z.2⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hux : ⟪z.2, z.1⟫ = 0 := by rw [real_inner_comm, hxu]
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_) <;>
    simp [innerC, plane, inner_add_right, real_inner_smul_right, huu, hux, hu]

theorem innerC_mapC (v : Ambient n) (hv : v = z.1 ∨ v = z.2) (c : CoefL n m) :
    innerC v (mapC (projW z) c) = 0 := by
  have h : ∀ w : Ambient n, ⟪v, projW z w⟫ = 0 := fun w => by
    rcases hv with rfl | rfl
    · exact (inner_projW hz.1 hz.2.1 hz.2.2 w).1
    · exact (inner_projW hz.1 hz.2.1 hz.2.2 w).2
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_) <;> simp [innerC, mapC, h]

theorem mapC_mapC (c : CoefL n m) : mapC (projW z) (mapC (projW z) c) = mapC (projW z) c := by
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_) <;>
    simp [mapC, projW_projW hz.1 hz.2.1 hz.2.2]

/-- Every coefficient vector splits into its normal part and its in-plane part. -/
theorem split_coef (c : CoefL n m) :
    c = mapC (projW z) c + plane z (innerC z.1 c) (innerC z.2 c) := by
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_)
  · exact projW_add_plane z c.1
  · exact projW_add_plane z (c.2 i).1
  · exact projW_add_plane z (c.2 i).2

end Pair

/-! ### Algebra of the coefficient maps -/

theorem coefL_add (V W : ZMod N → Ambient n) :
    coefL (m := m) (V + W) = coefL (m := m) V + coefL (m := m) W := by
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_)
  · change (1 / 2 : ℝ) • coefA 0 (V + W) = (1 / 2 : ℝ) • coefA 0 V + (1 / 2 : ℝ) • coefA 0 W
    rw [coefA_add, smul_add]
  · exact coefA_add _ V W
  · exact coefB_add _ V W

theorem coefL_smul (r : ℝ) (V : ZMod N → Ambient n) :
    coefL (m := m) (r • V) = r • coefL (m := m) V := by
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_)
  · change (1 / 2 : ℝ) • coefA 0 (r • V) = r • ((1 / 2 : ℝ) • coefA 0 V)
    rw [coefA_smul, smul_comm]
  · exact coefA_smul _ r V
  · exact coefB_smul _ r V

/-- The low coefficients as a continuous linear map. -/
def coefLL : (ZMod N → Ambient n) →L[ℝ] CoefL n m :=
  LinearMap.toContinuousLinearMap
    { toFun := coefL (m := m)
      map_add' := coefL_add
      map_smul' := coefL_smul }

theorem synL_add (c c' : CoefL n m) : synL (N := N) (c + c') = synL c + synL c' := by
  unfold synL
  have h0 : regular N 0 (c + c').1 (0 : Ambient n) = regular N 0 c.1 0 + regular N 0 c'.1 0 := by
    rw [← regular_add, add_zero]
    rfl
  rw [h0, show (∑ i : Fin (m - 1), regular N ((i : ℕ) + 1) ((c + c').2 i).1 ((c + c').2 i).2) =
    ∑ i : Fin (m - 1), (regular N ((i : ℕ) + 1) (c.2 i).1 (c.2 i).2 +
      regular N ((i : ℕ) + 1) (c'.2 i).1 (c'.2 i).2) from
    Finset.sum_congr rfl fun i _ => regular_add _ _ _ _ _, Finset.sum_add_distrib]
  abel

theorem synL_smul (r : ℝ) (c : CoefL n m) : synL (N := N) (r • c) = r • synL c := by
  unfold synL
  have h0 : regular N 0 (r • c).1 (0 : Ambient n) = r • regular N 0 c.1 0 := by
    rw [← regular_smul, smul_zero]
    rfl
  rw [h0, show (∑ i : Fin (m - 1), regular N ((i : ℕ) + 1) ((r • c).2 i).1 ((r • c).2 i).2) =
    ∑ i : Fin (m - 1), r • regular N ((i : ℕ) + 1) (c.2 i).1 (c.2 i).2 from
    Finset.sum_congr rfl fun i _ => regular_smul _ _ _ _, ← Finset.smul_sum, smul_add]

/-- The synthesis as a continuous linear map. -/
def synLL : CoefL n m →L[ℝ] (ZMod N → Ambient n) :=
  LinearMap.toContinuousLinearMap
    { toFun := synL (N := N)
      map_add' := synL_add
      map_smul' := synL_smul }

theorem synL_mem_kern (hm0 : 0 < m) (hmN : 2 * m < N) (c : CoefL n m) :
    synL (N := N) c ∈ kern (n := n) (N := N) m := by
  have hm1 : ∀ i : Fin (m - 1), 2 * ((i : ℕ) + 1) < N := fun i => by have := i.2; omega
  rw [mem_kern]
  unfold synL
  constructor
  · rw [coefA_add, coefA_regular hm0 hmN (by omega), if_neg hm0.ne', zero_add, coefA_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [coefA_regular hm0 hmN (hm1 i), if_neg (by have := i.2; omega)]
  · rw [coefB_add, coefB_regular hm0 hmN (by omega), if_neg hm0.ne', zero_add, coefB_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [coefB_regular hm0 hmN (hm1 i), if_neg (by have := i.2; omega)]

theorem onVert_synL (f : Ambient n →L[ℝ] Ambient n) (c : CoefL n m) :
    onVert (N := N) f (synL c) = synL (mapC f c) := by
  unfold synL mapC
  rw [map_add, map_sum, onVert_regular, map_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [onVert_regular]

theorem low_synL (hm : 0 < m) (hmN : 2 * m < N) (c : CoefL n m) :
    low m (synL (N := N) c) = synL c := by
  rw [← synL_coefL hm, coefL_synL hmN]

/-! ### Points of the negative bundle -/

section Bundle

variable (hm : 0 < m) (hmN : 2 * m < N)

theorem sqP_eq_zero_iff (p : (Ambient n × Ambient n) × Fib n N m) :
    sqP p = 0 ↔ p.2.1 = 0 ∧ (p.2.2 : ZMod N → Ambient n) = negP p := by
  constructor
  · intro h
    unfold sqP at h
    have hq := pair_self_nonneg ((p.2.2 : ZMod N → Ambient n) - negP p)
    have h1 : p.2.1.1 = 0 := by nlinarith [sq_nonneg p.2.1.1, sq_nonneg p.2.1.2.1, sq_nonneg p.2.1.2.2]
    have h2 : p.2.1.2.1 = 0 := by nlinarith [sq_nonneg p.2.1.1, sq_nonneg p.2.1.2.1, sq_nonneg p.2.1.2.2]
    have h3 : p.2.1.2.2 = 0 := by nlinarith [sq_nonneg p.2.1.1, sq_nonneg p.2.1.2.1, sq_nonneg p.2.1.2.2]
    rw [h1, h2, h3] at h
    have h4 : pair ((p.2.2 : ZMod N → Ambient n) - negP p) ((p.2.2 : ZMod N → Ambient n) - negP p) = 0 := by
      linarith
    exact ⟨Prod.ext h1 (Prod.ext h2 h3), sub_eq_zero.mp (pair_eq_zero h4)⟩
  · rintro ⟨h1, h2⟩
    unfold sqP
    rw [h1, h2, sub_self]
    simp [pair]

/-- The negative bundle of the model. -/
abbrev NB (n N m : ℕ) [NeZero N] : TopCat.{0} := TopCat.of {w : MS n N m // sqP w.1 = 0}

/-- V₂ as a space. -/
abbrev V2T (n : ℕ) : TopCat.{0} := TopCat.of {z : Ambient n × Ambient n // z ∈ V2}

include hmN in
theorem nb_low (w : NB n N m) :
    low m ((w.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) = w.1.1.2.2 := by
  obtain ⟨-, h⟩ := (sqP_eq_zero_iff w.1.1).mp w.2
  rw [h]
  unfold negP negV
  rw [low_onVert, low_low hmN]

theorem nb_normal (w : NB n N m) :
    onVert (projW w.1.1.1) ((w.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) =
      w.1.1.2.2 := by
  obtain ⟨-, h⟩ := (sqP_eq_zero_iff w.1.1).mp w.2
  rw [h]
  unfold negP negV
  exact onVert_projW_idem w.1.2 _

theorem nb_coef_normal (w : NB n N m) :
    mapC (projW w.1.1.1) (coefL (m := m)
      ((w.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n)) =
      coefL (m := m) ((w.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) := by
  rw [mapC_coefL, nb_normal]

/-- The point of the negative bundle with given normal coefficients. -/
theorem sqP_synL (z : Ambient n × Ambient n) (hz : z ∈ V2) (c : CoefL n m) :
    sqP ((z, ((0 : ℝ × ℝ × ℝ), ⟨synL (mapC (projW z) c), synL_mem_kern hm hmN _⟩)) :
      (Ambient n × Ambient n) × Fib n N m) = 0 := by
  rw [sqP_eq_zero_iff]
  refine ⟨rfl, ?_⟩
  change synL (N := N) (mapC (projW z) c) = negV m z (synL (mapC (projW z) c))
  unfold negV
  rw [low_synL hm hmN, onVert_synL, mapC_mapC hz]

end Bundle

/-! ### The stabilizing homeomorphism -/

section Homeo

variable (hm : 0 < m) (hmN : 2 * m < N)

theorem plane_continuous : Continuous fun q : (Ambient n × Ambient n) × (CoefS m × CoefS m) =>
    plane q.1 q.2.1 q.2.2 := by
  unfold plane
  refine Continuous.prodMk (by fun_prop) (continuous_pi fun i => ?_)
  have h1 : Continuous fun q : (Ambient n × Ambient n) × (CoefS m × CoefS m) => q.2.1.2 i :=
    (continuous_apply i).comp (continuous_snd.comp (continuous_fst.comp continuous_snd))
  have h2 : Continuous fun q : (Ambient n × Ambient n) × (CoefS m × CoefS m) => q.2.2.2 i :=
    (continuous_apply i).comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
  exact Continuous.prodMk (by fun_prop) (by fun_prop)

theorem mapC_projW_continuous : Continuous fun q : (Ambient n × Ambient n) × CoefL n m =>
    mapC (projW q.1) q.2 := by
  have hP : Continuous fun q : (Ambient n × Ambient n) × Ambient n => projW q.1 q.2 := by
    simp only [projW_apply]
    fun_prop
  unfold mapC
  have h1 : Continuous fun q : (Ambient n × Ambient n) × CoefL n m => projW q.1 q.2.1 :=
    Continuous.comp (g := fun q : (Ambient n × Ambient n) × Ambient n => projW q.1 q.2)
      (f := fun q : (Ambient n × Ambient n) × CoefL n m => (q.1, q.2.1)) hP
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  refine Continuous.prodMk h1 (continuous_pi fun i => ?_)
  have hc : Continuous fun q : (Ambient n × Ambient n) × CoefL n m => q.2.2 i :=
    (continuous_apply i).comp (continuous_snd.comp continuous_snd)
  have h2 : Continuous fun q : (Ambient n × Ambient n) × CoefL n m => projW q.1 (q.2.2 i).1 :=
    Continuous.comp (g := fun q : (Ambient n × Ambient n) × Ambient n => projW q.1 q.2)
      (f := fun q : (Ambient n × Ambient n) × CoefL n m => (q.1, (q.2.2 i).1)) hP
      (continuous_fst.prodMk (continuous_fst.comp hc))
  have h3 : Continuous fun q : (Ambient n × Ambient n) × CoefL n m => projW q.1 (q.2.2 i).2 :=
    Continuous.comp (g := fun q : (Ambient n × Ambient n) × Ambient n => projW q.1 q.2)
      (f := fun q : (Ambient n × Ambient n) × CoefL n m => (q.1, (q.2.2 i).2)) hP
      (continuous_fst.prodMk (continuous_snd.comp hc))
  exact h2.prodMk h3

theorem innerC_continuous : Continuous fun q : Ambient n × CoefL n m => innerC q.1 q.2 := by
  unfold innerC
  refine Continuous.prodMk (continuous_fst.inner (continuous_fst.comp continuous_snd))
    (continuous_pi fun i => ?_)
  have hc : Continuous fun q : Ambient n × CoefL n m => q.2.2 i :=
    (continuous_apply i).comp (continuous_snd.comp continuous_snd)
  exact (continuous_fst.inner (continuous_fst.comp hc)).prodMk
    (continuous_fst.inner (continuous_snd.comp hc))

theorem mapC_add (f : Ambient n →L[ℝ] Ambient n) (c c' : CoefL n m) :
    mapC f (c + c') = mapC f c + mapC f c' := by
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_) <;> simp [mapC]

theorem innerC_add (v : Ambient n) (c c' : CoefL n m) :
    innerC v (c + c') = innerC v c + innerC v c' := by
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_) <;> simp [innerC, inner_add_right]

/-- The stabilizing map. -/
def stab (p : NB n N m × (CoefS m × CoefS m)) : V2T n × CoefL n m :=
  (⟨p.1.1.1.1, p.1.1.2⟩, coefL (m := m) ((p.1.1.1.2.2 : kern (n := n) (N := N) m) :
    ZMod N → Ambient n) + plane p.1.1.1.1 p.2.1 p.2.2)

/-- Its inverse. -/
def unstab (q : V2T n × CoefL n m) : NB n N m × (CoefS m × CoefS m) :=
  (⟨⟨(q.1.1, ((0 : ℝ × ℝ × ℝ), ⟨synL (mapC (projW q.1.1) q.2), synL_mem_kern hm hmN _⟩)), q.1.2⟩,
    sqP_synL hm hmN q.1.1 q.1.2 q.2⟩, (innerC q.1.1.1 q.2, innerC q.1.1.2 q.2))

theorem unstab_stab (p : NB n N m × (CoefS m × CoefS m)) :
    unstab (N := N) hm hmN (stab p) = p := by
  obtain ⟨w, s, s'⟩ := p
  obtain ⟨-, hV⟩ := (sqP_eq_zero_iff w.1.1).mp w.2
  have hτ := ((sqP_eq_zero_iff w.1.1).mp w.2).1
  have hz := w.1.2
  have hnorm := nb_coef_normal w
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext hτ.symm (Subtype.ext ?_))
    change synL (mapC (projW w.1.1.1) (coefL (m := m)
      ((w.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) +
        plane w.1.1.1 s s')) = ((w.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n)
    rw [mapC_add, mapC_projW_plane hz, add_zero, hnorm, synL_coefL hm, nb_low hmN w]
  · change innerC w.1.1.1.1 (coefL (m := m) _ + plane w.1.1.1 s s') = s
    rw [innerC_add, ← hnorm, innerC_mapC hz _ (Or.inl rfl), innerC_plane_fst hz, zero_add]
  · change innerC w.1.1.1.2 (coefL (m := m) _ + plane w.1.1.1 s s') = s'
    rw [innerC_add, ← hnorm, innerC_mapC hz _ (Or.inr rfl), innerC_plane_snd hz, zero_add]

theorem stab_unstab (q : V2T n × CoefL n m) : stab (unstab (N := N) hm hmN q) = q := by
  obtain ⟨z, c⟩ := q
  refine Prod.ext rfl ?_
  change coefL (m := m) (synL (N := N) (mapC (projW z.1) c)) +
    plane z.1 (innerC z.1.1 c) (innerC z.1.2 c) = c
  rw [coefL_synL hmN, ← split_coef z.2]

/-- **The stabilizing homeomorphism.** -/
def stabHomeo : (NB n N m × (CoefS m × CoefS m)) ≃ₜ (V2T n × CoefL n m) where
  toFun := stab
  invFun := unstab hm hmN
  left_inv := unstab_stab hm hmN
  right_inv := stab_unstab hm hmN
  continuous_toFun := by
    have hw : Continuous fun p : NB n N m × (CoefS m × CoefS m) =>
        ((p.1.1.1 : (Ambient n × Ambient n) × Fib n N m)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    have hz : Continuous fun p : NB n N m × (CoefS m × CoefS m) => p.1.1.1.1 :=
      continuous_fst.comp hw
    have hV : Continuous fun p : NB n N m × (CoefS m × CoefS m) =>
        ((p.1.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) :=
      continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp hw))
    refine Continuous.prodMk (hz.subtype_mk _) ?_
    exact ((coefLL (n := n) (N := N) (m := m)).continuous.comp hV).add
      ((plane_continuous (m := m)).comp (hz.prodMk continuous_snd))
  continuous_invFun := by
    have hz : Continuous fun q : V2T n × CoefL n m => (q.1 : Ambient n × Ambient n) :=
      continuous_subtype_val.comp continuous_fst
    have hc := (mapC_projW_continuous (n := n) (m := m)).comp (hz.prodMk continuous_snd)
    have hsyn := (synLL (n := n) (N := N) (m := m)).continuous.comp hc
    refine Continuous.prodMk ?_ ?_
    · refine Continuous.subtype_mk (Continuous.subtype_mk (hz.prodMk
        (continuous_const.prodMk (hsyn.subtype_mk _))) _) _
    · exact ((innerC_continuous (m := m)).comp ((continuous_fst.comp hz).prodMk continuous_snd)).prodMk
        ((innerC_continuous (m := m)).comp ((continuous_snd.comp hz).prodMk continuous_snd))

include hm hmN in
/-- The stabilizing map is zero exactly on the zero section times zero. -/
theorem stab_eq_zero_iff (p : NB n N m × (CoefS m × CoefS m)) :
    (stab p).2 = 0 ↔ ((p.1.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) = 0 ∧
      p.2 = 0 := by
  obtain ⟨w, s, s'⟩ := p
  have hz := w.1.2
  have hnorm := nb_coef_normal w
  constructor
  · intro h
    change coefL (m := m) _ + plane w.1.1.1 s s' = 0 at h
    have h1 := congrArg (mapC (projW w.1.1.1)) h
    rw [mapC_add, mapC_projW_plane hz, add_zero, hnorm] at h1
    have hzero : mapC (projW w.1.1.1) (0 : CoefL n m) = 0 := by
      refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_) <;> simp [mapC]
    rw [hzero] at h1
    have hV : ((w.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) = 0 := by
      rw [← nb_low hmN w, ← synL_coefL hm, h1]
      have : synL (N := N) (0 : CoefL n m) = 0 := by
        have := synL_smul (N := N) (0 : ℝ) (0 : CoefL n m)
        simpa using this
      exact this
    have h2 := congrArg (innerC w.1.1.1.1) h
    have h3 := congrArg (innerC w.1.1.1.2) h
    rw [innerC_add, ← hnorm, innerC_mapC hz _ (Or.inl rfl), innerC_plane_fst hz, zero_add] at h2
    rw [innerC_add, ← hnorm, innerC_mapC hz _ (Or.inr rfl), innerC_plane_snd hz, zero_add] at h3
    have hi0 : ∀ v : Ambient n, innerC v (0 : CoefL n m) = 0 := fun v => by
      refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_) <;> simp [innerC]
    rw [hi0] at h2 h3
    exact ⟨hV, Prod.ext h2 h3⟩
  · rintro ⟨hV, hs⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hs
    change coefL (m := m) ((w.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) +
      plane w.1.1.1 0 0 = 0
    rw [hV]
    refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_) <;> simp [coefL, plane, coefA, coefB]

end Homeo

/-! ### Dimensions -/

section Dims

open Finsler.PairSuspensionProduct Finsler.PairTriple Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Module

variable (hm : 0 < m) (hmN : 2 * m < N)

theorem finrank_coefS1 (hm : 0 < m) : finrank ℝ (CoefS m) = 2 * m - 1 := by
  rw [Module.finrank_prod, Module.finrank_self, Module.finrank_pi_fintype]
  simp only [Module.finrank_prod, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  omega

theorem finrank_coefS (hm : 0 < m) : finrank ℝ (CoefS m × CoefS m) = 2 * (2 * m - 1) := by
  rw [Module.finrank_prod, finrank_coefS1 hm]
  ring

theorem finrank_coefL (hm : 0 < m) : finrank ℝ (CoefL n m) = (2 * m - 1) * (n + 1) := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype]
  simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]
  have : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  rw [this]
  ring

/-- The vectors of the stabilization. -/
def e₁ (hm : 0 < m) : (Fin (2 * (2 * m - 1)) → ℝ) ≃L[ℝ] (CoefS m × CoefS m) :=
  ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun, finrank_coefS hm])

/-- The coefficient vectors of the trivial bundle. -/
def e₂ (hm : 0 < m) : CoefL n m ≃L[ℝ] (Fin ((2 * m - 1) * (n + 1)) → ℝ) :=
  ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun, finrank_coefL hm])

/-- The stabilized homeomorphism in the product form of the suspension. -/
def bigHomeo : Prd (NB n N m) (2 * (2 * m - 1)) ≃ₜ Prd (V2T n) ((2 * m - 1) * (n + 1)) :=
  ((Homeomorph.refl (NB n N m)).prodCongr (e₁ (m := m) hm).toHomeomorph).trans
    ((stabHomeo hm hmN).trans ((Homeomorph.refl (V2T n)).prodCongr (e₂ (n := n) hm).toHomeomorph))

/-- The nonzero vectors of the negative bundle. -/
def nbO : Set (NB n N m) :=
  {w | ((w.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) ≠ 0}

theorem nbO_isOpen : IsOpen (nbO (n := n) (N := N) (m := m)) := by
  have h : Continuous fun w : NB n N m =>
      ((w.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) :=
    continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp
      (continuous_subtype_val.comp continuous_subtype_val)))
  exact isOpen_ne.preimage h

theorem bigHomeo_mem (p : Prd (NB n N m) (2 * (2 * m - 1))) :
    p ∈ prodCyl (univ : Set (NB n N m)) _ ∩ prodOpen nbO _ ↔
      bigHomeo hm hmN p ∈ prodCyl (univ : Set (V2T n)) _ ∩ prodOpen (∅ : Set (V2T n)) _ := by
  obtain ⟨w, u⟩ := p
  have key : (bigHomeo hm hmN (w, u)).2 = e₂ hm (stab (w, e₁ hm u)).2 := rfl
  simp only [prodCyl, prodOpen, nbO, mem_inter_iff, mem_setOf_eq, mem_univ, true_and,
    mem_empty_iff_false, or_false]
  rw [key]
  have he₂ : e₂ (n := n) hm (stab (w, e₁ hm u)).2 ≠ 0 ↔ (stab (w, e₁ hm u)).2 ≠ 0 :=
    (e₂ (n := n) hm).map_ne_zero_iff
  have hst : (stab (w, e₁ hm u)).2 ≠ 0 ↔
      ¬(((w.1.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) = 0 ∧ e₁ (m := m) hm u = 0) :=
    not_congr (stab_eq_zero_iff hm hmN (w, e₁ hm u))
  have he₁ : e₁ (m := m) hm u = 0 ↔ u = 0 := (e₁ (m := m) hm).map_eq_zero_iff
  rw [he₂, hst, he₁]
  tauto

include hm hmN in
/-- The cohomology of the stabilized pair of the negative bundle is that of the trivial bundle. -/
theorem big_finrank (q : ℕ) :
    finrank (ZMod 2) (H (triv (pairOf (inter_subset_left :
      prodCyl (univ : Set (NB n N m)) (2 * (2 * m - 1)) ∩ prodOpen nbO (2 * (2 * m - 1)) ⊆
        prodCyl univ (2 * (2 * m - 1))))) q) =
    finrank (ZMod 2) (H (triv (pairOf (inter_subset_left :
      prodCyl (univ : Set (V2T n)) ((2 * m - 1) * (n + 1)) ∩
        prodOpen (∅ : Set (V2T n)) ((2 * m - 1) * (n + 1)) ⊆
          prodCyl univ ((2 * m - 1) * (n + 1))))) q) :=
  (LinearEquiv.ofBijective _ (bijective_Hmap_of_homeomorph _ _ (bigHomeo hm hmN)
    (fun _ => ⟨fun _ => mem_univ _, fun _ => mem_univ _⟩) (bigHomeo_mem hm hmN) q)).finrank_eq.symm

include hm hmN in
theorem big_zero (q : ℕ)
    (h0 : ∀ y : H (triv (pairOf (inter_subset_left :
      prodCyl (univ : Set (V2T n)) ((2 * m - 1) * (n + 1)) ∩
        prodOpen (∅ : Set (V2T n)) ((2 * m - 1) * (n + 1)) ⊆
          prodCyl univ ((2 * m - 1) * (n + 1))))) q, y = 0)
    (x : H (triv (pairOf (inter_subset_left :
      prodCyl (univ : Set (NB n N m)) (2 * (2 * m - 1)) ∩ prodOpen nbO (2 * (2 * m - 1)) ⊆
        prodCyl univ (2 * (2 * m - 1))))) q) : x = 0 := by
  obtain ⟨y, rfl⟩ := (bijective_Hmap_of_homeomorph
    (inter_subset_left : prodCyl (univ : Set (NB n N m)) (2 * (2 * m - 1)) ∩
      prodOpen nbO (2 * (2 * m - 1)) ⊆ prodCyl univ (2 * (2 * m - 1)))
    (inter_subset_left : prodCyl (univ : Set (V2T n)) ((2 * m - 1) * (n + 1)) ∩
      prodOpen (∅ : Set (V2T n)) ((2 * m - 1) * (n + 1)) ⊆ prodCyl univ ((2 * m - 1) * (n + 1)))
    (bigHomeo hm hmN) (fun _ => ⟨fun _ => mem_univ _, fun _ => mem_univ _⟩)
    (bigHomeo_mem hm hmN) q).2 x
  rw [h0 y, map_zero]

end Dims

/-! ### The Thom pair of the model -/

section ThomPair

open Finsler.PairSuspensionProduct Finsler.PairTriple Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Module

variable (hm : 0 < m) (hmN : 2 * m < N) {a c T : ℝ} (ha : a ≤ (2 * π * m) ^ 2)
  (hc : (2 * π * m) ^ 2 < c)

theorem np_eq_zero_iff (w : MS n N m) : (cone hm hmN).np w = 0 ↔ sqP w.1 = 0 :=
  Real.sqrt_eq_zero (sqP_nonneg w.1)

theorem nn_ne_zero_iff (w : MS n N m) (hw : sqP w.1 = 0) :
    (cone hm hmN).nn w ≠ 0 ↔ ((w.1.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) ≠ 0 := by
  have hV := ((sqP_eq_zero_iff w.1).mp hw).2
  change Real.sqrt (sqN w.1) ≠ 0 ↔ _
  rw [Ne, Real.sqrt_eq_zero (sqN_nonneg w.1), hV]
  unfold sqN
  constructor
  · intro h h0
    exact h (by rw [h0]; simp [pair])
  · intro h h0
    exact h (pair_eq_zero h0)

/-- From T_b of the model to the negative bundle. -/
def toNB : C(setTb (cone hm hmN) (univ : Set (MS n N m)) c, (univ : Set (NB n N m))) :=
  ⟨fun w => ⟨⟨w.1, (np_eq_zero_iff hm hmN w.1).mp w.2.1⟩, mem_univ _⟩,
    ((continuous_subtype_val.subtype_mk _).subtype_mk _)⟩

/-- From the negative bundle to T_b of the model. -/
def ofNB : C((univ : Set (NB n N m)), setTb (cone hm hmN) (univ : Set (MS n N m)) c) :=
  ⟨fun v => ⟨v.1.1, (np_eq_zero_iff hm hmN v.1.1).mpr v.1.2, hc, mem_univ _⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

include ha hc in
/-- **The Thom pair of the model is the pair of the negative bundle.** -/
theorem thom_nb_bijective (q : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX
      (setSx_sub_setTb (cone hm hmN) (descentM hm hmN) (univ : Set (MS n N m)) a c T)
      (inter_subset_left : (univ : Set (NB n N m)) ∩ nbO ⊆ univ) (toNB hm hmN)
      (fun w hw => by
        refine ⟨mem_univ _, ?_⟩
        rcases hw.2.2.2 with h | h
        · exact (nn_ne_zero_iff hm hmN w.1 ((np_eq_zero_iff hm hmN w.1).mp w.2.1)).mp h
        · exfalso
          change (2 * π * m) ^ 2 < a at h
          linarith))) q) := by
  refine bijective_Hmap_of_section _ _ (toNB hm hmN) (ofNB hm hmN hc) _ (fun v hv => ?_) ?_
    (ContinuousMap.Homotopy.refl _) (fun _ _ hx => hx) q
  · refine ⟨(ofNB hm hmN hc v).2.1, hc, mem_univ _, Or.inl ?_⟩
    exact (nn_ne_zero_iff hm hmN v.1.1 v.1.2).mpr hv.2
  · exact ContinuousMap.ext fun v => rfl

include ha hc in
/-- **The Thom pair of the model has the cohomology of V₂ shifted by the index.** -/
theorem thom_finrank (hn : 1 ≤ n) (k : ℕ) :
    finrank (ZMod 2) (H (triv (pairOf
      (setSx_sub_setTb (cone hm hmN) (descentM hm hmN) (univ : Set (MS n N m)) a c T)))
        (k + (2 * m - 1) * (n - 1))) =
      finrank (ZMod 2) (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))) k) := by
  have hL : k + (2 * m - 1) * (n - 1) + 2 * (2 * m - 1) = k + (2 * m - 1) * (n + 1) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [(LinearEquiv.ofBijective _ (thom_nb_bijective hm hmN ha hc _)).finrank_eq.symm]
  rw [← finrank_prod (univ : Set (NB n N m)) nbO_isOpen (2 * (2 * m - 1)), big_finrank hm hmN, hL,
    finrank_prod (univ : Set (V2T n)) isOpen_empty]

include ha hc in
/-- The Thom pair of the model has no cohomology below the index. -/
theorem thom_zero (hn : 1 ≤ n) (q : ℕ) (hq : q < (2 * m - 1) * (n - 1))
    (x : H (triv (pairOf
      (setSx_sub_setTb (cone hm hmN) (descentM hm hmN) (univ : Set (MS n N m)) a c T))) q) :
    x = 0 := by
  obtain ⟨y, rfl⟩ := (thom_nb_bijective hm hmN ha hc (T := T) q).2 x
  suffices hy : y = 0 by rw [hy, map_zero]
  have e := prodEquiv (univ : Set (NB n N m)) nbO_isOpen (2 * (2 * m - 1)) q
  have hz : e y = 0 := by
    refine big_zero hm hmN _ (fun z => prod_eq_zero (univ : Set (V2T n)) isOpen_empty _ _ ?_ z) (e y)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hq
    have : (2 * m - 1) * (n' + 1 + 1) = (2 * m - 1) * n' + 2 * (2 * m - 1) := by ring
    rw [this]
    omega
  exact (LinearEquiv.map_eq_zero_iff e).mp hz

include ha hc in
/-- The Thom pair of the model is finite dimensional in the degrees where V₂ is. -/
theorem thom_finite (hn : 1 ≤ n) (k : ℕ)
    (hk : Module.Finite (ZMod 2)
      (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))) k)) :
    Module.Finite (ZMod 2) (H (triv (pairOf
      (setSx_sub_setTb (cone hm hmN) (descentM hm hmN) (univ : Set (MS n N m)) a c T)))
        (k + (2 * m - 1) * (n - 1))) := by
  have hL : k + (2 * m - 1) * (n - 1) + 2 * (2 * m - 1) = k + (2 * m - 1) * (n + 1) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have h1 : Module.Finite (ZMod 2) (H (triv (pairOf (inter_subset_left :
      prodCyl (univ : Set (V2T n)) ((2 * m - 1) * (n + 1)) ∩
        prodOpen (∅ : Set (V2T n)) ((2 * m - 1) * (n + 1)) ⊆
          prodCyl univ ((2 * m - 1) * (n + 1))))) (k + (2 * m - 1) * (n + 1))) := by
    haveI := hk
    exact Module.Finite.equiv (prodEquiv (univ : Set (V2T n)) isOpen_empty ((2 * m - 1) * (n + 1)) k)
  rw [← hL] at h1
  have h2 : Module.Finite (ZMod 2) (H (triv (pairOf (inter_subset_left :
      prodCyl (univ : Set (NB n N m)) (2 * (2 * m - 1)) ∩ prodOpen nbO (2 * (2 * m - 1)) ⊆
        prodCyl univ (2 * (2 * m - 1))))) (k + (2 * m - 1) * (n - 1) + 2 * (2 * m - 1))) := by
    haveI := h1
    exact Module.Finite.equiv (LinearEquiv.ofBijective _ (bijective_Hmap_of_homeomorph
      (inter_subset_left : prodCyl (univ : Set (NB n N m)) (2 * (2 * m - 1)) ∩
        prodOpen nbO (2 * (2 * m - 1)) ⊆ prodCyl univ (2 * (2 * m - 1)))
      (inter_subset_left : prodCyl (univ : Set (V2T n)) ((2 * m - 1) * (n + 1)) ∩
        prodOpen (∅ : Set (V2T n)) ((2 * m - 1) * (n + 1)) ⊆ prodCyl univ ((2 * m - 1) * (n + 1)))
      (bigHomeo hm hmN) (fun _ => ⟨fun _ => mem_univ _, fun _ => mem_univ _⟩)
      (bigHomeo_mem hm hmN) _))
  have h3 : Module.Finite (ZMod 2) (H (triv (pairOf
      (inter_subset_left : (univ : Set (NB n N m)) ∩ nbO ⊆ univ))) (k + (2 * m - 1) * (n - 1))) := by
    haveI := h2
    exact Module.Finite.equiv (prodEquiv (univ : Set (NB n N m)) nbO_isOpen (2 * (2 * m - 1)) _).symm
  haveI := h3
  exact Module.Finite.equiv (LinearEquiv.ofBijective _ (thom_nb_bijective hm hmN ha hc (T := T) _))

end ThomPair

end

end Finsler.RoundThom
