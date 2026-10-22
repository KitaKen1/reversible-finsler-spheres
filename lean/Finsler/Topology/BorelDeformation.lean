module

public import Finsler.Topology.BorelCrossingK
public import Finsler.Topology.BorelInvariance

/-! Deformations of pairs and Borel cohomology. For pairs of subsets (t, s) ⊆ (t', s') of a
space, a homotopy of t' from the identity to a map taking t' into t and s' into s, under which
s', t and s are invariant at all times, makes the inclusion of pairs (t, s) → (t', s') a homotopy
equivalence of pairs, hence an isomorphism on actual relative cohomology. Two cases are used:
nested sets s ⊆ t ⊆ u with the inclusion (t, s) → (u, s), and nested sets s ⊆ y ⊆ u with the map
(u, s) → (u, y) which is the identity of u. The inclusions are equivariant for every involution
preserving the sets, so they induce isomorphisms on reflection Borel cohomology and on the
iterated Borel cohomology; the deformation itself need not be equivariant. For Finsler levels
a ≤ b: if t_b deforms into t_a keeping t_a and the constant loops, then restriction from
(t_b, M) to (t_a, M) is an isomorphism on ordinary, reflection and K-Borel cohomology. The
existence of such deformations between regular cuts is a separate geometric statement about a
descending flow and is not proved here. -/

@[expose] public section

namespace Finsler.BorelDeformation

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.BorelComparison Finsler.BorelIterate

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section General

variable {X : TopCat.{0}}

/-- A homotopy between maps t → t' which keeps s inside s' at all times, as a homotopy between
the maps of pairs (t, s) → (t', s'). The construction is the one of Tau Ceti's
`TopPair.ofInclusionHomotopy`, stated for the pair maps of this project. -/
def pairHomotopy {s t s' t' : Set X} (hst : s ⊆ t) (hst' : s' ⊆ t') {g₀ g₁ : C(t, t')}
    (F : g₀.Homotopy g₁)
    (hF : ∀ (τ : unitInterval) (x : t), (x : X) ∈ s → (F (τ, x) : X) ∈ s') :
    TopPair.Homotopy (pairMap hst hst' g₀ fun x hx ↦ F.apply_zero x ▸ hF 0 x hx)
      (pairMap hst hst' g₁ fun x hx ↦ F.apply_one x ▸ hF 1 x hx) where
  fst := F
  snd :=
    { toFun (p : unitInterval × s) := ⟨F (p.1, ⟨p.2.1, hst p.2.2⟩), hF p.1 _ p.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left x := Subtype.ext (congrArg Subtype.val (F.apply_zero ⟨x.1, hst x.2⟩) :)
      map_one_left x := Subtype.ext (congrArg Subtype.val (F.apply_one ⟨x.1, hst x.2⟩) :) }

/-- A deformation of the pair (t', s') into the pair (t, s): a homotopy of t' from the identity
to a map taking t' into t and s' into s, under which s', t and s are invariant at all times. -/
structure PairDeformation (s t s' t' : Set X) where
  r : C(t', t')
  H : (ContinuousMap.id t').Homotopy r
  r_mem : ∀ x : t', (r x : X) ∈ t
  r_sub : ∀ x : t', (x : X) ∈ s' → (r x : X) ∈ s
  keep_sub' : ∀ (τ : unitInterval) (x : t'), (x : X) ∈ s' → (H (τ, x) : X) ∈ s'
  keep : ∀ (τ : unitInterval) (x : t'), (x : X) ∈ t → (H (τ, x) : X) ∈ t
  keep_sub : ∀ (τ : unitInterval) (x : t'), (x : X) ∈ s → (H (τ, x) : X) ∈ s

section Pair

variable {s t s' t' : Set X} (hst : s ⊆ t) (hst' : s' ⊆ t') (hss : s ⊆ s') (htt : t ⊆ t')
  (d : PairDeformation s t s' t')

/-- The inclusion of pairs (t, s) → (t', s'). -/
def inclPair : pairOf hst ⟶ pairOf hst' :=
  pairMap hst hst' (ContinuousMap.inclusion htt) (fun _ hx => hss hx)

/-- The end map of the deformation as a map t' → t. -/
def endMap : C(t', t) :=
  ⟨fun x => ⟨d.r x, d.r_mem x⟩, (continuous_subtype_val.comp d.r.continuous).subtype_mk _⟩

/-- The end map as a map of pairs (t', s') → (t, s). -/
def retract : pairOf hst' ⟶ pairOf hst :=
  pairMap hst' hst (endMap d) (fun x hx => d.r_sub x hx)

/-- The deformation restricted to t, reversed: from the end map to the identity of t. -/
def homT : ((endMap d).comp (ContinuousMap.inclusion htt)).Homotopy (ContinuousMap.id t) where
  toFun p := ⟨d.H (unitInterval.symm p.1, ⟨p.2, htt p.2.2⟩), d.keep _ _ p.2.2⟩
  continuous_toFun := by
    refine (continuous_subtype_val.comp (d.H.continuous.comp ?_)).subtype_mk _
    exact (unitInterval.continuous_symm.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  map_zero_left x := by
    apply Subtype.ext
    change (d.H (unitInterval.symm 0, ⟨x, htt x.2⟩) : X) = (d.r ⟨x, htt x.2⟩ : X)
    rw [unitInterval.symm_zero, d.H.apply_one]
  map_one_left x := by
    apply Subtype.ext
    change (d.H (unitInterval.symm 1, ⟨x, htt x.2⟩) : X) = (x : X)
    rw [unitInterval.symm_one, d.H.apply_zero]
    rfl

include d in
/-- The inclusion followed by the end map is homotopic to the identity of (t, s). -/
theorem nonempty_homotopy_left :
    Nonempty (TopPair.Homotopy (inclPair hst hst' hss htt ≫ retract hst hst' d)
      (𝟙 (pairOf hst))) := by
  have hF : ∀ (τ : unitInterval) (x : t), (x : X) ∈ s → (homT htt d (τ, x) : X) ∈ s :=
    fun τ x hx => d.keep_sub _ _ hx
  have H := pairHomotopy hst hst (homT htt d) hF
  have e1 : inclPair hst hst' hss htt ≫ retract hst hst' d =
      pairMap hst hst ((endMap d).comp (ContinuousMap.inclusion htt))
        (fun x hx => (homT htt d).apply_zero x ▸ hF 0 x hx) :=
    (pairMap_comp hst hst' hst (ContinuousMap.inclusion htt) (endMap d)
      (fun _ hx => hss hx) (fun x hx => d.r_sub x hx)).symm
  have e2 : 𝟙 (pairOf hst) = pairMap hst hst (ContinuousMap.id t)
      (fun x hx => (homT htt d).apply_one x ▸ hF 1 x hx) :=
    (pairMap_id hst).symm
  rw [e1, e2]
  exact ⟨H⟩

include d in
/-- The end map followed by the inclusion is homotopic to the identity of (t', s'). -/
theorem nonempty_homotopy_right :
    Nonempty (TopPair.Homotopy (retract hst hst' d ≫ inclPair hst hst' hss htt)
      (𝟙 (pairOf hst'))) := by
  have hF : ∀ (τ : unitInterval) (x : t'), (x : X) ∈ s' → (d.H.symm (τ, x) : X) ∈ s' :=
    fun τ x hx => d.keep_sub' _ _ hx
  have H := pairHomotopy hst' hst' d.H.symm hF
  have hcomp : (ContinuousMap.inclusion htt).comp (endMap d) = d.r := by
    ext x
    rfl
  have e1 : retract hst hst' d ≫ inclPair hst hst' hss htt =
      pairMap hst' hst' d.r (fun x hx => d.H.symm.apply_zero x ▸ hF 0 x hx) :=
    (pairMap_comp hst' hst hst' (endMap d) (ContinuousMap.inclusion htt)
      (fun x hx => d.r_sub x hx) (fun _ hx => hss hx)).symm.trans
      (pairMap_congr _ _ hcomp _ _)
  have e2 : 𝟙 (pairOf hst') = pairMap hst' hst' (ContinuousMap.id t')
      (fun x hx => d.H.symm.apply_one x ▸ hF 1 x hx) :=
    (pairMap_id hst').symm
  rw [e1, e2]
  exact ⟨H⟩

include d in
/-- The inclusion (t, s) → (t', s') is an isomorphism on actual relative singular cohomology. -/
theorem bijective_nativePull_inclPair (q : ℕ) :
    Function.Bijective (nativePull (inclPair hst hst' hss htt) q) := by
  obtain ⟨H₁⟩ := nonempty_homotopy_left hst hst' hss htt d
  obtain ⟨H₂⟩ := nonempty_homotopy_right hst hst' hss htt d
  exact BorelInvariance.bijective_nativePull_of_homotopyEquiv (inclPair hst hst' hss htt)
    (retract hst hst' d) H₁ H₂ q

end Pair

/-- If u deforms into itself taking y into s and keeping y and s, the map of pairs
(u, s) → (u, y) which is the identity of u is an isomorphism on actual relative singular
cohomology. -/
theorem bijective_nativePull_relPair {s y u : Set X} (hsy : s ⊆ y) (hyu : y ⊆ u)
    (d : PairDeformation s u y u) (q : ℕ) :
    Function.Bijective (nativePull (relPair hsy hyu) q) := by
  have h : relPair hsy hyu = inclPair (hsy.trans hyu) hyu hsy subset_rfl := by
    ext : 2 <;> rfl
  rw [h]
  exact bijective_nativePull_inclPair (hsy.trans hyu) hyu hsy subset_rfl d q

/-- A deformation of u into t keeping s and t: a homotopy of u from the identity to a map with
values in t, under which s and t are invariant at all times. -/
structure Deformation (s t u : Set X) where
  r : C(u, u)
  H : (ContinuousMap.id u).Homotopy r
  r_mem : ∀ x : u, (r x : X) ∈ t
  keep_s : ∀ (τ : unitInterval) (x : u), (x : X) ∈ s → (H (τ, x) : X) ∈ s
  keep_t : ∀ (τ : unitInterval) (x : u), (x : X) ∈ t → (H (τ, x) : X) ∈ t

/-- A deformation of u into t keeping s and t is a deformation of the pair (u, s) into the
pair (t, s). -/
def toPair {s t u : Set X} (d : Deformation s t u) : PairDeformation s t s u where
  r := d.r
  H := d.H
  r_mem := d.r_mem
  r_sub x hx := by
    have h := d.keep_s 1 x hx
    rw [d.H.apply_one] at h
    exact h
  keep_sub' := d.keep_s
  keep := d.keep_t
  keep_sub := d.keep_s

/-- If u deforms into t keeping s and t, the inclusion (t, s) → (u, s) is an isomorphism on
actual relative singular cohomology. -/
theorem bijective_nativePull {s t u : Set X} (hst : s ⊆ t) (htu : t ⊆ u)
    (d : Deformation s t u) (q : ℕ) : Function.Bijective (nativePull (incPair hst htu) q) :=
  bijective_nativePull_inclPair hst (hst.trans htu) subset_rfl htu (toPair d) q

end General

variable {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) {a b : ℝ} (hab : a ≤ b)
  (d : Deformation (consts n) (lev F a) (lev F b))

include d in
/-- If t_b deforms into t_a keeping t_a and the constant loops, the ordinary restriction
A_b → A_a is an isomorphism. -/
theorem cut_bijective_ordinary (q : ℕ) : Function.Bijective (Hmap (cutHom F hab) q) :=
  BorelInvariance.bijective_Hmap (revPair_sq F a) (revPair_sq F b) (cutPair F hab)
    (cutPair_equivariant F hab)
    (fun k => bijective_nativePull (consts_subset_lev F a) (lev_mono F hab) d k) q

include d in
/-- Under the same deformation the reflection Borel restriction B_b → B_a is an isomorphism. -/
theorem cut_bijective (q : ℕ) : Function.Bijective (HRmap (cutHom F hab) q) :=
  BorelInvariance.bijective_HRmap (revPair_sq F a) (revPair_sq F b) (cutPair F hab)
    (cutPair_equivariant F hab)
    (fun k => bijective_nativePull (consts_subset_lev F a) (lev_mono F hab) d k) q

include d in
/-- Under the same deformation the K-Borel restriction is an isomorphism. -/
theorem cut_bijective_K (q : ℕ) :
    Function.Bijective (HRmap (borelHom (Finsler.BorelK.cutComm F hab)) q) :=
  BorelQuasiIso.bijective_iterated (Finsler.BorelK.cutComm F hab)
    (fun k => cut_bijective_ordinary F hab d k) q

include hab d in
/-- Under the same deformation a global reflection class is zero at a exactly when it is zero
at b. -/
theorem res_eq_zero_iff (q : ℕ) (x : HR (fullComplex n) q) :
    HRmap (resHom F a) q x = 0 ↔ HRmap (resHom F b) q x = 0 := by
  have hnat : HRmap (cutHom F hab) q (HRmap (resHom F b) q x) = HRmap (resHom F a) q x := by
    rw [← HRmap_comp]
    exact HRmap_congr (cut_res_f F hab) q x
  constructor
  · intro h
    apply (cut_bijective F hab d q).1
    rw [hnat, h, map_zero]
  · intro h
    rw [← hnat, h, map_zero]

end

end Finsler.BorelDeformation
