module

public import Finsler.Geometry.RoundV2Finite
public import Finsler.Topology.PairSuspensionProduct

/-! A trivialization of V₂ over the sphere minus a pole.

Let e₀ be the first basis vector. Over the points x ≠ −e₀ of the sphere, the rotation in the plane
of x and e₀ which takes x to e₀ maps the orthogonal complement of x onto the orthogonal
complement K of e₀. On the unit vectors it is

  fr x u = u − (⟪u, e₀⟫ / (1 + ⟪x, e₀⟫)) (x + e₀),   gr x w = w − (⟪x, w⟫ / (1 + ⟪x, e₀⟫)) (x + e₀),

inverse to each other (no rotation theory is needed: the identities are inner product
computations). With the stereographic projection from −e₀ and a linear identification of its
target with ℝⁿ, the pairs (x, u) ∈ V₂ with x ≠ −e₀ are homeomorphic to S(K) × ℝⁿ, the fibre over
e₀ going to S(K) × {0}. -/

@[expose] public section

namespace Finsler.RoundV2Chart

open CategoryTheory Finsler.SphereGeometry Finsler.RoundChart Finsler.RoundThom
open Finsler.PairSuspensionProduct
open Set Topology Filter Module Metric
open scoped RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ### The pole and the rotation maps -/

/-- The pole. -/
def e₀ : Ambient n := EuclideanSpace.single 0 1

theorem norm_e₀ : ‖(e₀ : Ambient n)‖ = 1 := by
  simp [e₀]

theorem inner_e₀_self : ⟪(e₀ : Ambient n), e₀⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_e₀, one_pow]

theorem e₀_ne_zero : (e₀ : Ambient n) ≠ 0 := by
  intro h
  have := norm_e₀ (n := n)
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem norm_neg_e₀ : ‖-(e₀ : Ambient n)‖ = 1 := by
  rw [norm_neg, norm_e₀]

theorem one_add_inner_ne {x : Ambient n} (hx : ‖x‖ = 1) (hne : x ≠ -e₀) : 1 + ⟪x, e₀⟫ ≠ 0 := by
  intro h
  apply hne
  have h2 : ‖x + e₀‖ ^ 2 = 0 := by
    rw [norm_add_sq_real, hx, norm_e₀]
    linarith
  have h0 : x + e₀ = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
  exact eq_neg_of_add_eq_zero_left h0

/-- The rotation taking x to e₀, on the complement of x. -/
def fr (x u : Ambient n) : Ambient n := u - (⟪u, e₀⟫ / (1 + ⟪x, e₀⟫)) • (x + e₀)

/-- The rotation taking e₀ to x, on the complement of e₀. -/
def gr (x w : Ambient n) : Ambient n := w - (⟪x, w⟫ / (1 + ⟪x, e₀⟫)) • (x + e₀)

section Rot

variable {x : Ambient n} (hx : ‖x‖ = 1) (hc : 1 + ⟪x, e₀⟫ ≠ 0)
include hx

theorem inner_x_self : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]

include hc

theorem fr_inner_e₀ {u : Ambient n} : ⟪fr x u, e₀⟫ = 0 := by
  unfold fr
  rw [inner_sub_left, real_inner_smul_left, inner_add_left, inner_e₀_self]
  field_simp
  ring

theorem fr_inner_x {u : Ambient n} (hu : ⟪x, u⟫ = 0) : ⟪x, fr x u⟫ = -⟪u, e₀⟫ := by
  unfold fr
  rw [inner_sub_right, real_inner_smul_right, inner_add_right, inner_x_self hx, hu]
  field_simp
  ring

theorem norm_sq_fr {u : Ambient n} (hu : ⟪x, u⟫ = 0) : ‖fr x u‖ ^ 2 = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have hux : ⟪u, x⟫ = 0 := by rw [real_inner_comm]; exact hu
  have he1 : ⟪e₀, u⟫ = ⟪u, e₀⟫ := real_inner_comm u e₀
  have he2 : ⟪e₀, x⟫ = ⟪x, e₀⟫ := real_inner_comm x e₀
  unfold fr
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, hux, hu, he1, he2, inner_x_self hx, inner_e₀_self]
  field_simp
  ring

theorem gr_inner_x {w : Ambient n} : ⟪x, gr x w⟫ = 0 := by
  unfold gr
  rw [inner_sub_right, real_inner_smul_right, inner_add_right, inner_x_self hx]
  field_simp
  ring

theorem norm_sq_gr {w : Ambient n} (hw : ⟪w, e₀⟫ = 0) : ‖gr x w‖ ^ 2 = ‖w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have he1 : ⟪e₀, w⟫ = 0 := by rw [real_inner_comm]; exact hw
  have he2 : ⟪e₀, x⟫ = ⟪x, e₀⟫ := real_inner_comm x e₀
  have hwx : ⟪w, x⟫ = ⟪x, w⟫ := real_inner_comm x w
  unfold gr
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, hw, he1, he2, hwx, inner_x_self hx, inner_e₀_self]
  field_simp
  ring

theorem gr_fr {u : Ambient n} (hu : ⟪x, u⟫ = 0) : gr x (fr x u) = u := by
  rw [gr, fr_inner_x hx hc hu, fr]
  rw [sub_sub, ← add_smul]
  have : ⟪u, e₀⟫ / (1 + ⟪x, e₀⟫) + -⟪u, e₀⟫ / (1 + ⟪x, e₀⟫) = 0 := by
    rw [neg_div, add_neg_cancel]
  rw [this, zero_smul, sub_zero]

theorem fr_gr {w : Ambient n} (hw : ⟪w, e₀⟫ = 0) : fr x (gr x w) = w := by
  have hp : ⟪gr x w, e₀⟫ = -⟪x, w⟫ := by
    unfold gr
    rw [inner_sub_left, real_inner_smul_left, inner_add_left, inner_e₀_self, hw]
    field_simp
    ring
  rw [fr, hp, gr, sub_sub, ← add_smul]
  have : ⟪x, w⟫ / (1 + ⟪x, e₀⟫) + -⟪x, w⟫ / (1 + ⟪x, e₀⟫) = 0 := by
    rw [neg_div, add_neg_cancel]
  rw [this, zero_smul, sub_zero]

end Rot

theorem norm_fr {x u : Ambient n} (hx : ‖x‖ = 1) (hc : 1 + ⟪x, e₀⟫ ≠ 0) (hu : ⟪x, u⟫ = 0) :
    ‖fr x u‖ = ‖u‖ :=
  (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (norm_sq_fr hx hc hu)

theorem norm_gr {x w : Ambient n} (hx : ‖x‖ = 1) (hc : 1 + ⟪x, e₀⟫ ≠ 0) (hw : ⟪w, e₀⟫ = 0) :
    ‖gr x w‖ = ‖w‖ :=
  (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (norm_sq_gr hx hc hw)

/-! ### The chart of V₂ over the sphere minus −e₀ -/

/-- The equator space. -/
abbrev Kq (n : ℕ) := (ℝ ∙ (e₀ : Ambient n))ᗮ

/-- The fibre sphere. -/
abbrev Zs (n : ℕ) : TopCat.{0} := TopCat.of (sphere (0 : Kq n) 1)

/-- The pairs over the sphere minus −e₀. -/
def NP : Set (V2T n) := {p | p.1.1 ≠ -e₀}

/-- The pairs over the sphere minus e₀. -/
def AP : Set (V2T n) := {p | p.1.1 ≠ e₀}

theorem NP_isOpen : IsOpen (NP (n := n)) :=
  isOpen_ne.preimage (continuous_fst.comp continuous_subtype_val)

theorem AP_isOpen : IsOpen (AP (n := n)) :=
  isOpen_ne.preimage (continuous_fst.comp continuous_subtype_val)

/-- The identification of the target of the stereographic projection with ℝⁿ. -/
def Lq (n : ℕ) : (ℝ ∙ (-e₀ : Ambient n))ᗮ ≃L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := n) (neg_ne_zero.mpr e₀_ne_zero), Module.finrank_fin_fun])

theorem inner_ne_one {x : Ambient n} (hx : ‖x‖ = 1) (hne : x ≠ -e₀) :
    innerSL ℝ (-e₀ : Ambient n) x ≠ (1 : ℝ) := by
  have h := one_add_inner_ne hx hne
  rw [innerSL_apply_apply, inner_neg_left, real_inner_comm]
  intro h'
  apply h
  linarith

theorem x_mem_sphere (p : V2T n) : (p.1.1 : Ambient n) ∈ sphere (0 : Ambient n) 1 :=
  mem_sphere_zero_iff_norm.mpr p.2.1

theorem fr_mem (p : NP (n := n)) : fr p.1.1.1 p.1.1.2 ∈ Kq n := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
  exact fr_inner_e₀ p.1.2.1 (one_add_inner_ne p.1.2.1 p.2)

theorem fr_mem_sphere (p : NP (n := n)) :
    (⟨fr p.1.1.1 p.1.1.2, fr_mem p⟩ : Kq n) ∈ sphere (0 : Kq n) 1 := by
  rw [mem_sphere_zero_iff_norm, Submodule.coe_norm]
  rw [norm_fr p.1.2.1 (one_add_inner_ne p.1.2.1 p.2) p.1.2.2.2]
  exact p.1.2.2.1

/-- The chart map. -/
def chartFun (p : NP (n := n)) : sphere (0 : Kq n) 1 × (Fin n → ℝ) :=
  (⟨⟨fr p.1.1.1 p.1.1.2, fr_mem p⟩, fr_mem_sphere p⟩, Lq n (stereoToFun (-e₀) p.1.1.1))

theorem stereo_ne_pole (v : (ℝ ∙ (-e₀ : Ambient n))ᗮ) :
    (stereoInvFun norm_neg_e₀ v : Ambient n) ≠ -e₀ := by
  intro h
  exact stereoInvFun_ne_north_pole norm_neg_e₀ v (Subtype.ext h)

/-- The inverse chart map. -/
def chartInv (q : sphere (0 : Kq n) 1 × (Fin n → ℝ)) : NP (n := n) :=
  ⟨⟨((stereoInvFun norm_neg_e₀ ((Lq n).symm q.2) : Ambient n),
      gr (stereoInvFun norm_neg_e₀ ((Lq n).symm q.2) : Ambient n) ((q.1 : Kq n) : Ambient n)),
    norm_eq_of_mem_sphere (stereoInvFun norm_neg_e₀ ((Lq n).symm q.2)),
    by
      rw [norm_gr (norm_eq_of_mem_sphere _) (one_add_inner_ne (norm_eq_of_mem_sphere _)
        (stereo_ne_pole _)) (by
          rw [real_inner_comm]
          exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (q.1 : Kq n).2)]
      rw [← Submodule.coe_norm]
      exact norm_eq_of_mem_sphere q.1,
    gr_inner_x (norm_eq_of_mem_sphere _) (one_add_inner_ne (norm_eq_of_mem_sphere _)
      (stereo_ne_pole _))⟩, stereo_ne_pole _⟩

theorem chartInv_chartFun (p : NP (n := n)) : chartInv (chartFun p) = p := by
  have hx : stereoInvFun norm_neg_e₀ (stereoToFun (-e₀) p.1.1.1) =
      (⟨p.1.1.1, x_mem_sphere p.1⟩ : sphere (0 : Ambient n) 1) :=
    stereo_left_inv norm_neg_e₀ (x := ⟨p.1.1.1, x_mem_sphere p.1⟩) p.2
  apply Subtype.ext
  apply Subtype.ext
  change ((stereoInvFun norm_neg_e₀ ((Lq n).symm (Lq n (stereoToFun (-e₀) p.1.1.1))) : Ambient n),
    gr (stereoInvFun norm_neg_e₀ ((Lq n).symm (Lq n (stereoToFun (-e₀) p.1.1.1))) : Ambient n)
      (fr p.1.1.1 p.1.1.2)) = p.1.1
  rw [ContinuousLinearEquiv.symm_apply_apply, hx]
  exact Prod.ext rfl (gr_fr p.1.2.1 (one_add_inner_ne p.1.2.1 p.2) p.1.2.2.2)

theorem chartFun_chartInv (q : sphere (0 : Kq n) 1 × (Fin n → ℝ)) :
    chartFun (chartInv q) = q := by
  refine Prod.ext (Subtype.ext (Subtype.ext ?_)) ?_
  · change fr (stereoInvFun norm_neg_e₀ ((Lq n).symm q.2) : Ambient n)
      (gr (stereoInvFun norm_neg_e₀ ((Lq n).symm q.2) : Ambient n) ((q.1 : Kq n) : Ambient n)) =
        ((q.1 : Kq n) : Ambient n)
    exact fr_gr (norm_eq_of_mem_sphere _) (one_add_inner_ne (norm_eq_of_mem_sphere _)
      (stereo_ne_pole _)) (by
        rw [real_inner_comm]
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (q.1 : Kq n).2)
  · change Lq n (stereoToFun (-e₀) (stereoInvFun norm_neg_e₀ ((Lq n).symm q.2) : Ambient n)) = q.2
    rw [stereo_right_inv, ContinuousLinearEquiv.apply_symm_apply]

theorem chartFun_continuous : Continuous (chartFun (n := n)) := by
  have hx : Continuous fun p : NP (n := n) => (p.1.1.1 : Ambient n) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hu : Continuous fun p : NP (n := n) => (p.1.1.2 : Ambient n) :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hfr : Continuous fun p : NP (n := n) => fr p.1.1.1 p.1.1.2 := by
    unfold fr
    refine hu.sub (((hu.inner continuous_const).div (continuous_const.add
      (hx.inner continuous_const)) fun p => one_add_inner_ne p.1.2.1 p.2).smul
        (hx.add continuous_const))
  have hst : Continuous fun p : NP (n := n) => stereoToFun (-e₀) (p.1.1.1 : Ambient n) :=
    continuousOn_stereoToFun.comp_continuous hx fun p => inner_ne_one p.1.2.1 p.2
  refine Continuous.prodMk ?_ ((Lq n).continuous.comp hst)
  exact (hfr.subtype_mk _).subtype_mk _

theorem chartInv_continuous : Continuous (chartInv (n := n)) := by
  have hx : Continuous fun q : sphere (0 : Kq n) 1 × (Fin n → ℝ) =>
      (stereoInvFun norm_neg_e₀ ((Lq n).symm q.2) : Ambient n) :=
    continuous_subtype_val.comp ((continuous_stereoInvFun norm_neg_e₀).comp
      ((Lq n).symm.continuous.comp continuous_snd))
  have hw : Continuous fun q : sphere (0 : Kq n) 1 × (Fin n → ℝ) =>
      ((q.1 : Kq n) : Ambient n) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
  have hgr : Continuous fun q : sphere (0 : Kq n) 1 × (Fin n → ℝ) =>
      gr (stereoInvFun norm_neg_e₀ ((Lq n).symm q.2) : Ambient n) ((q.1 : Kq n) : Ambient n) := by
    unfold gr
    exact hw.sub (((hx.inner hw).div (continuous_const.add (hx.inner continuous_const))
      fun q => one_add_inner_ne (norm_eq_of_mem_sphere _) (stereo_ne_pole _)).smul
        (hx.add continuous_const))
  exact ((hx.prodMk hgr).subtype_mk _).subtype_mk _

/-- **The chart of V₂ over the sphere minus −e₀.** -/
def chartHomeo : NP (n := n) ≃ₜ (sphere (0 : Kq n) 1 × (Fin n → ℝ)) where
  toFun := chartFun
  invFun := chartInv
  left_inv := chartInv_chartFun
  right_inv := chartFun_chartInv
  continuous_toFun := chartFun_continuous
  continuous_invFun := chartInv_continuous

theorem stereo_eq_zero_iff {x : Ambient n} (hx : ‖x‖ = 1) (hne : x ≠ -e₀) :
    stereoToFun (-e₀) x = 0 ↔ x = e₀ := by
  constructor
  · intro h
    have hl := stereo_left_inv norm_neg_e₀ (x := ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩) hne
    have h' := congrArg Subtype.val hl
    change (stereoInvFun norm_neg_e₀ (stereoToFun (-e₀) x) : Ambient n) = x at h'
    rw [h, stereoInvFun_apply] at h'
    simp only [ZeroMemClass.coe_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_add, smul_zero, zero_sub, neg_smul, smul_neg, neg_neg] at h'
    rw [← h', smul_smul]
    norm_num
  · rintro rfl
    rw [stereoToFun_apply]
    have hp : (ℝ ∙ (-e₀ : Ambient n))ᗮ.orthogonalProjectionOnto e₀ = 0 := by
      rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]
      exact Submodule.mem_span_singleton.mpr ⟨-1, by simp⟩
    rw [hp, smul_zero]

theorem chartFun_snd_eq_zero_iff (p : NP (n := n)) : (chartFun p).2 = 0 ↔ p.1.1.1 = e₀ := by
  change Lq n (stereoToFun (-e₀) p.1.1.1) = 0 ↔ _
  rw [(Lq n).map_eq_zero_iff]
  exact stereo_eq_zero_iff p.1.2.1 p.2

end

end Finsler.RoundV2Chart
