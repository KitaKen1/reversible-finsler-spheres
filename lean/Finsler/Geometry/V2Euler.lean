module

public import Finsler.Geometry.V2Tower
public import Finsler.Geometry.ECupThom
public import Finsler.Topology.ECupUnit
public import Finsler.Topology.PairAdditive

/-! The evaluation class of V₂ (ECompat step 3).

The pullback π^* : Hⁿ(Sⁿ) → Hⁿ(V₂) of the projection π(x, u) = x is injective. Every class of
Hⁿ(Sⁿ) comes from Hⁿ(Sⁿ, Sⁿ ∖ e₀) (the punctured sphere is acyclic), and the square with the
pair map π̂ : (V₂, A) → (Sⁿ, Sⁿ ∖ e₀) commutes. The map Hⁿ(V₂, A) → Hⁿ(V₂) is injective
(`V2Tower.j_injective`), and π̂^* is injective: composed with the slice y ↦ chart⁻¹(a, y) of the
chart of V₂ over Sⁿ ∖ −e₀ it is the inverse stereographic projection (ℝⁿ, ℝⁿ ∖ 0) →
(Sⁿ ∖ −e₀, Sⁿ ∖ ±e₀) followed by an excision. Hence the cup with π^*[Sⁿ] annihilates no nonzero
class of H⁰(V₂): this follows from the same statement for [Sⁿ] on H⁰(Sⁿ) (`ECupUnit`) and
naturality, H⁰ being spanned by the natural unit class. With `RoundLoopCup.ecompat_of` this is
the e-compatibility of all round crossings. -/

@[expose] public section

namespace Finsler.V2Euler

open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.RoundChart Finsler.RoundThom
open Finsler.RoundV2Chart Finsler.RoundV2Dims Finsler.TrivHq Finsler.ECup Finsler.ECupThom
open Finsler.ECupUnit Finsler.V2Tower Finsler.BorelCochain Finsler.BorelPair Finsler.PairTriple
open Finsler.BorelLoop Finsler.BorelExact Finsler.BorelCrossing Finsler.BorelDeformation
open Finsler.PairAdditive Finsler.TameHomology Finsler.RelativeCohomology
open CategoryTheory.Limits
open Set Module Metric

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-- The sphere as a space. -/
abbrev SP (n : ℕ) : TopCat.{0} := Finsler.BorelEvaluation.sphere n

/-! ### The poles -/

/-- The pole e₀ of the sphere. -/
def pS (n : ℕ) : Sphere n := ⟨e₀, mem_sphere_zero_iff_norm.mpr norm_e₀⟩

/-- The pole −e₀ of the sphere. -/
def qS (n : ℕ) : Sphere n := ⟨-e₀, mem_sphere_zero_iff_norm.mpr norm_neg_e₀⟩

theorem pS_ne_qS : pS n ≠ qS n := by
  intro h
  have h' : (e₀ : Ambient n) = -e₀ := congrArg Subtype.val h
  have h2 : (2 : ℝ) • (e₀ : Ambient n) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h']
    exact add_neg_cancel _
  exact e₀_ne_zero ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-! ### The punctured sphere -/

/-- The relative homology of a pair with empty subspace is the homology of the space. -/
theorem Hrel_isZero {X : TopCat.{0}} {s t : Set X} (h : s ⊆ t) [IsEmpty s] (k : ℕ)
    (hk : IsZero (Hq (TopCat.of ↥t) k)) : IsZero (Hrel (pairOf h) k) := by
  haveI : IsEmpty ((pairOf h).snd : Type) := (inferInstance : IsEmpty ↥s)
  have hz : ∀ j, IsZero (Hq (pairOf h).snd j) := fun j => isZero_Hq_of_isEmpty _ j
  cases k with
  | zero =>
    have hepi : Epi ((pairOf h).singularHomologyπ coeff 0) := inferInstance
    exact IsZero.of_epi ((pairOf h).singularHomologyπ coeff 0) hk
  | succ q =>
    have hepi : Epi ((pairOf h).singularHomologyπ coeff (q + 1)) :=
      ((pairOf h).singularHomology_exact_relative coeff (q + 1) q rfl).epi_f
        ((hz q).eq_of_tgt _ _)
    exact IsZero.of_epi ((pairOf h).singularHomologyπ coeff (q + 1)) hk

/-- The cohomology of a pair with empty subspace vanishes where the homology of the space
does. -/
theorem H_eq_zero_of_empty {X : TopCat.{0}} {s t : Set X} (h : s ⊆ t) [IsEmpty s] (k : ℕ)
    (hk : IsZero (Hq (TopCat.of ↥t) k)) (x : H (triv (pairOf h)) k) : x = 0 := by
  have hrel := Hrel_isZero h k hk
  have : Subsingleton (Hrel (pairOf h) k) := ModuleCat.subsingleton_of_isZero hrel
  let e := (BorelComparison.ordinaryEquiv (pairOf h) (𝟙 _) (Category.comp_id _) k).trans
    (Finsler.RelativeKronecker.equiv (pairOf h) k)
  apply e.injective
  rw [LinearEquiv.map_zero]
  exact LinearMap.ext fun z => by rw [Subsingleton.elim z 0, map_zero, map_zero]

/-- The punctured sphere has no homology in positive degrees. -/
theorem punct_Hq_isZero (p : Sphere n) (k : ℕ) (hk : 1 ≤ k) :
    IsZero (Hq (TopCat.of ↥({p}ᶜ : Set (SP n))) k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact (TauCeti.isZero_reducedSingularHomologyFunctor_sphere_compl_singleton coeff p (j + 1)).of_iso
    ((TauCeti.reducedSingularHomologySuccIso coeff j).app _).symm

theorem hsS : (univ : Set (SP n)) ∩ ∅ ⊆ ({pS n}ᶜ : Set (SP n)) := fun _ h => h.2.elim

theorem htS : ({pS n}ᶜ : Set (SP n)) ⊆ univ := subset_univ _

instance isEmpty_inter_empty {X : Type*} : IsEmpty ↥((univ : Set X) ∩ ∅) := ⟨fun x => x.2.2⟩

/-- **Every class of Hⁿ(Sⁿ) comes from Hⁿ(Sⁿ, Sⁿ ∖ e₀).** -/
theorem jS_surjective (hn : 1 ≤ n) :
    Function.Surjective (Hmap (trivHom (relPair (hsS (n := n)) htS)) n) := by
  intro y
  have hi := H_eq_zero_of_empty (hsS (n := n)) n (punct_Hq_isZero (pS n) n hn)
    (Hmap (trivHom (incPair (hsS (n := n)) htS)) n y)
  exact exact_mid_ordinary (tripleExact (hsS (n := n)) htS) n y hi

/-! ### The maps of pairs -/

/-- The projection on univ. -/
def gπ (n : ℕ) : C((univ : Set (V2T n)), (univ : Set (SP n))) :=
  ⟨fun z => ⟨(piV n).hom z.1, mem_univ _⟩,
    (((piV n).hom.continuous.comp continuous_subtype_val)).subtype_mk _⟩

/-- The pair map (V₂, A) → (Sⁿ, Sⁿ ∖ e₀). -/
def πA (n : ℕ) : pairOf (subset_univ (AP (n := n))) ⟶ pairOf (htS (n := n)) :=
  pairMapX (subset_univ (AP (n := n))) htS (gπ n) (fun z hz h => hz (congrArg Subtype.val h))

/-- The pair map (V₂, ∅) → (Sⁿ, ∅). -/
def π0 (n : ℕ) :
    pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ) ⟶
      pairOf (inter_subset_left : (univ : Set (SP n)) ∩ ∅ ⊆ univ) :=
  pairMapX _ _ (gπ n) (fun _ h => h.2.elim)

theorem square :
    π0 n ≫ relPair (hsS (n := n)) htS =
      relPair (hst (n := n)) (subset_univ (AP (n := n))) ≫ πA n := by
  ext : 2 <;> rfl

/-! ### The slice and the stereographic projection -/

/-- The punctured Euclidean space as a subset. -/
def ne0 (n : ℕ) : Set (TopCat.of (Fin n → ℝ)) := {y | y ≠ 0}

theorem hR : ne0 n ⊆ univ := subset_univ _

theorem exists_a (hn : 2 ≤ n) : Nonempty (sphere (0 : Kq n) 1) := by
  have : Nontrivial (Kq n) := Module.nontrivial_of_finrank_eq_succ (finrank_Kq hn)
  exact (NormedSpace.sphere_nonempty (E := Kq n) (x := 0) (r := 1)).mpr zero_le_one |>.coe_sort

/-- The slice of the chart at a point a of the fibre sphere. -/
def gG (a : sphere (0 : Kq n) 1) : C((univ : Set (TopCat.of (Fin n → ℝ))), (univ : Set (V2T n))) :=
  ⟨fun y => ⟨(chartInv (a, y.1) : V2T n), mem_univ _⟩,
    ((continuous_subtype_val.comp (chartInv_continuous.comp
      (continuous_const.prodMk continuous_subtype_val)))).subtype_mk _⟩

theorem gG_mem (a : sphere (0 : Kq n) 1) (y : (univ : Set (TopCat.of (Fin n → ℝ))))
    (hy : (y : Fin n → ℝ) ∈ ne0 n) : (gG a y : V2T n) ∈ AP := by
  intro h
  apply hy
  have h1 : (chartFun (chartInv (a, y.1))).2 = 0 :=
    (chartFun_snd_eq_zero_iff (chartInv (a, y.1))).mpr h
  rw [chartFun_chartInv] at h1
  exact h1

/-- The slice as a map of pairs (ℝⁿ, ℝⁿ ∖ 0) → (V₂, A). -/
def sliceP (a : sphere (0 : Kq n) 1) : pairOf (hR (n := n)) ⟶ pairOf (subset_univ (AP (n := n))) :=
  pairMapX hR (subset_univ (AP (n := n))) (gG a) (gG_mem a)

theorem hσ : ({pS n}ᶜ ∩ {qS n}ᶜ : Set (SP n)) ⊆ {qS n}ᶜ := inter_subset_right

/-- The inverse stereographic projection from −e₀. -/
def gσ (n : ℕ) : C((univ : Set (TopCat.of (Fin n → ℝ))), ({qS n}ᶜ : Set (SP n))) :=
  ⟨fun y => ⟨stereoInvFun norm_neg_e₀ ((Lq n).symm y.1), fun h =>
      stereo_ne_pole ((Lq n).symm y.1) (congrArg Subtype.val h)⟩,
    ((continuous_stereoInvFun norm_neg_e₀).comp ((Lq n).symm.continuous.comp
      continuous_subtype_val)).subtype_mk _⟩

theorem gσ_mem (y : (univ : Set (TopCat.of (Fin n → ℝ)))) (hy : (y : Fin n → ℝ) ∈ ne0 n) :
    ((gσ n y : ({qS n}ᶜ : Set (SP n))) : Sphere n) ∈ ({pS n}ᶜ ∩ {qS n}ᶜ : Set (SP n)) := by
  refine ⟨fun h => hy ?_, (gσ n y).2⟩
  have hx : ((gσ n y : ({qS n}ᶜ : Set (SP n))) : Ambient n) = e₀ := congrArg Subtype.val h
  have hne : ((gσ n y : ({qS n}ᶜ : Set (SP n))) : Ambient n) ≠ -e₀ :=
    stereo_ne_pole ((Lq n).symm y.1)
  have h0 := (stereo_eq_zero_iff (norm_eq_of_mem_sphere _) hne).mpr hx
  change stereoToFun (-e₀) (stereoInvFun norm_neg_e₀ ((Lq n).symm y.1) : Ambient n) = 0 at h0
  rw [stereo_right_inv] at h0
  have h1 := congrArg (Lq n) h0
  rw [ContinuousLinearEquiv.apply_symm_apply, map_zero] at h1
  exact h1

/-- The stereographic projection from −e₀. -/
def gσinv (n : ℕ) : C(({qS n}ᶜ : Set (SP n)), (univ : Set (TopCat.of (Fin n → ℝ)))) :=
  ⟨fun x => ⟨Lq n (stereoToFun (-e₀) ((x : Sphere n) : Ambient n)), mem_univ _⟩, by
    have hx : Continuous fun x : ({qS n}ᶜ : Set (SP n)) => ((x : Sphere n) : Ambient n) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hst : Continuous fun x : ({qS n}ᶜ : Set (SP n)) =>
        stereoToFun (-e₀) ((x : Sphere n) : Ambient n) :=
      continuousOn_stereoToFun.comp_continuous hx fun x => inner_ne_one (norm_eq_of_mem_sphere _)
        (fun h => x.2 (Subtype.ext h))
    exact ((Lq n).continuous.comp hst).subtype_mk _⟩

theorem gσinv_mem (x : ({qS n}ᶜ : Set (SP n)))
    (hx : (x : Sphere n) ∈ ({pS n}ᶜ ∩ {qS n}ᶜ : Set (SP n))) :
    ((gσinv n x : (univ : Set (TopCat.of (Fin n → ℝ)))) : Fin n → ℝ) ∈ ne0 n := by
  intro h
  apply hx.1
  have h1 : stereoToFun (-e₀) ((x : Sphere n) : Ambient n) = 0 :=
    (Lq n).map_eq_zero_iff.mp h
  exact Subtype.ext ((stereo_eq_zero_iff (norm_eq_of_mem_sphere _)
    (fun h => x.2 (Subtype.ext h))).mp h1)

theorem gσ_gσinv : (gσ n).comp (gσinv n) = ContinuousMap.id _ := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  change stereoInvFun norm_neg_e₀ ((Lq n).symm (Lq n (stereoToFun (-e₀)
    ((x : Sphere n) : Ambient n)))) = (x : Sphere n)
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact stereo_left_inv norm_neg_e₀ (fun h => x.2 (Subtype.ext h))

theorem gσinv_gσ (y : (univ : Set (TopCat.of (Fin n → ℝ)))) : gσinv n (gσ n y) = y := by
  apply Subtype.ext
  change Lq n (stereoToFun (-e₀) (stereoInvFun norm_neg_e₀ ((Lq n).symm y.1) : Ambient n)) = y.1
  rw [stereo_right_inv, ContinuousLinearEquiv.apply_symm_apply]

/-- The stereographic projection as a map of pairs. -/
def σP (n : ℕ) : pairOf (hR (n := n)) ⟶ pairOf (hσ (n := n)) :=
  pairMapX hR hσ (gσ n) gσ_mem

theorem σP_bijective (k : ℕ) : Function.Bijective (Hmap (trivHom (σP n)) k) := by
  let F : ((gσinv n).comp (gσ n)).Homotopy (ContinuousMap.id _) :=
    { toFun := fun q => q.2
      continuous_toFun := continuous_snd
      map_zero_left := fun y => (gσinv_gσ y).symm
      map_one_left := fun _ => rfl }
  exact bijective_Hmap_of_section hR hσ (gσ n) (gσinv n) gσ_mem gσinv_mem gσ_gσinv F
    (fun _ _ hy => hy) k

/-- The excision of the pole −e₀. -/
theorem exc_bijective (k : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair (hσ (n := n)) (htS (n := n)) inter_subset_left
      (subset_univ _))) k) :=
  bijective_Hmap_excision (hσ (n := n)) (htS (n := n)) inter_subset_left (subset_univ _)
    (fun _ h1 h2 => ⟨h2, h1⟩) ({pS n}ᶜ) ({qS n}ᶜ) isOpen_compl_singleton isOpen_compl_singleton
    (fun x _ => by
      by_cases h : x = pS n
      · right
        rw [h]
        exact pS_ne_qS
      · left
        exact h) (fun _ h => h.1) (fun _ h => h.1) k

theorem slice_comp (a : sphere (0 : Kq n) 1) :
    sliceP a ≫ πA n = σP n ≫ inclPair (hσ (n := n)) (htS (n := n)) inter_subset_left
      (subset_univ _) := by
  ext : 2 <;> rfl

/-- **π̂^* is injective in degree n.** -/
theorem πA_injective (hn : 2 ≤ n) (k : ℕ) : Function.Injective (Hmap (trivHom (πA n)) k) := by
  obtain ⟨a⟩ := exists_a hn
  rw [injective_iff_map_eq_zero]
  intro z hz
  have h1 : Hmap (trivHom (sliceP a ≫ πA n)) k z = 0 := by
    rw [Hmap_comp_apply, hz, map_zero]
  rw [slice_comp, Hmap_comp_apply] at h1
  have h2 := (σP_bijective k).1 (h1.trans (map_zero _).symm)
  exact (exc_bijective k).1 (h2.trans (map_zero _).symm)

/-! ### Injectivity of π^* and the cup with π^*[Sⁿ] -/

/-- **π^* : Hⁿ(Sⁿ) → Hⁿ(V₂) is injective.** -/
theorem π0_injective (hn : 2 ≤ n) : Function.Injective (Hmap (trivHom (π0 n)) n) := by
  obtain ⟨q, hq⟩ : ∃ q, q + 1 = n := ⟨n - 1, by omega⟩
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨z, rfl⟩ := jS_surjective (by omega) y
  have h1 : Hmap (trivHom (relPair (hst (n := n)) (subset_univ (AP (n := n))) ≫ πA n)) n z = 0 := by
    rw [← square, Hmap_comp_apply]
    exact hy
  rw [Hmap_comp_apply] at h1
  have hj := j_injective hn q hq
  rw [hq] at hj
  have h2 := hj (h1.trans (map_zero _).symm)
  rw [πA_injective hn n (h2.trans (map_zero _).symm), map_zero]

theorem sphere_H0_le (hn : 1 ≤ n) :
    Module.Finite (ZMod 2) (H (triv (emptyPair (Finsler.BorelEvaluation.sphere n))) 0) ∧
      finrank (ZMod 2) (H (triv (emptyPair (Finsler.BorelEvaluation.sphere n))) 0) ≤ 1 := by
  have hE : finrank ℝ (Ambient n) = n + 1 := finrank_euclideanSpace_fin
  have h := finite_finrank (Finsler.BorelEvaluation.sphere n) 0 (sphere_Hq_zero_deg hE hn).1
  exact ⟨h.1, (h.2.trans (sphere_Hq_zero_deg hE hn).2).le⟩

/-- **The cup with π^*[Sⁿ] annihilates no nonzero class of H⁰(V₂)** (n ≥ 2). -/
theorem eV_cupInj (hn : 2 ≤ n) :
    CupInjW (eV n (by omega)) (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ) 0 := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hfinS, hdimS⟩ := sphere_H0_le hn1
  haveI := hfinS
  have hS := cupInjW_zero (Finsler.BorelEvaluation.sphere n)
    (Finsler.SphereTopClass.topClass n hn1) (pS n) hdimS
    (res_univ_ne_zero _ (Finsler.SphereTopClass.topClass_ne_zero n hn1))
  -- a point of V₂
  obtain ⟨a⟩ := exists_a hn
  let z₀ : V2T n := (chartInv (a, 0) : V2T n)
  haveI := Finsler.RoundV2Finite.V2_finite (n := n) 0
  -- transport from the sphere
  intro x hx
  have hux := eq_of_ne_zero_dim (V2_finrank_le_one hn 0) hx (unitH_ne_zero (V2T n) z₀)
  rw [hux, ← unitH_natural (V2T n) (π0 n)]
  have hab : (cohPullback (TopPair.Hom.fst (π0 n)) n).hom
      (res (Finsler.SphereTopClass.topClass n hn1) (univ : Set (SP n))) =
        res (eV n (by omega)) (univ : Set (V2T n)) :=
    res_pull_over (piV n) (Finsler.SphereTopClass.topClass n hn1) (π0 n) rfl
  rw [← hab, ← cupH_natural]
  intro h0
  have h1 := π0_injective hn (h0.trans (map_zero _).symm)
  exact hS _ (unitH_ne_zero _ (pS n)) h1

end

end Finsler.V2Euler
