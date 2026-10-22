module

public import Finsler.Topology.GradedDelta
public import Finsler.Topology.DiagonalCohomology

/-! Cup with absolute classes along isomorphisms of relative cohomology (transport of e).

For a pair P and a class a of degree p on its ambient space, `CupInj P a q` says that the
relative cup with a annihilates no nonzero class of the cohomology of P in degree q. It
transports along every map of pairs which is bijective on cohomology in the degrees q and p + q
when the classes correspond under pullback (naturality of the relative cup), and along bijective
connecting maps of triples (the connecting map is linear over cup with absolute cocycles,
`GradedDelta.tripleDelta_cup`). For pairs of subsets of one space with a global class
(`CupInjW`), every map of pairs over the ambient space (inclusions of pairs) which is bijective
on cohomology transports it. Two maps into a sphere which are never antipodal pull back the same
classes. -/

@[expose] public section

namespace Finsler.ECup

open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelComparison Finsler.PairTriple Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.GradedDelta Finsler.BorelDeformation Finsler.SphereGeometry
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! ### Cup with an absolute class -/

/-- The relative cup with an absolute class on the ordinary cohomology of a pair. -/
abbrev cupH (P : TopPair.{0}) {p : ℕ} (a : cohomologyZMod2 P.fst p) (q : ℕ)
    (x : H (triv P) q) : H (triv P) (p + q) :=
  ordinaryCup P (𝟙 P) (Category.comp_id _) p q a x

theorem cupH_zero (P : TopPair.{0}) {p : ℕ} (a : cohomologyZMod2 P.fst p) (q : ℕ) :
    cupH P a q 0 = 0 := by
  have h := ordinaryCup_smul_right P (𝟙 P) (Category.comp_id _) p q 0 a 0
  rw [zero_smul, zero_smul] at h
  exact h

/-- No nonzero class of degree q is annihilated by the cup with a. -/
def CupInj (P : TopPair.{0}) {p : ℕ} (a : cohomologyZMod2 P.fst p) (q : ℕ) : Prop :=
  ∀ x : H (triv P) q, x ≠ 0 → cupH P a q x ≠ 0

theorem cupH_natural {P Q : TopPair.{0}} (f : P ⟶ Q) {p : ℕ} (a : cohomologyZMod2 Q.fst p)
    (q : ℕ) (x : H (triv Q) q) :
    Hmap (trivHom f) (p + q) (cupH Q a q x) =
      cupH P ((cohPullback (TopPair.Hom.fst f) p).hom a) q (Hmap (trivHom f) q x) :=
  ordinaryCup_natural _ _ f _ p q a x

/-- **Transport along a map of pairs** which is bijective in the degrees q and p + q. -/
theorem cupInj_iff {P Q : TopPair.{0}} (f : P ⟶ Q) {p : ℕ} {a : cohomologyZMod2 Q.fst p}
    {b : cohomologyZMod2 P.fst p} (hab : (cohPullback (TopPair.Hom.fst f) p).hom a = b)
    {q : ℕ} (h₁ : Function.Bijective (Hmap (trivHom f) q))
    (h₂ : Function.Bijective (Hmap (trivHom f) (p + q))) :
    CupInj Q a q ↔ CupInj P b q := by
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := h₁.2 y
    have hx : x ≠ 0 := fun h0 => hy (by rw [h0, map_zero])
    rw [← hab, ← cupH_natural]
    intro h0
    exact h x hx (h₂.1 (h0.trans (map_zero _).symm))
  · intro h x hx h0
    have hy : Hmap (trivHom f) q x ≠ 0 := fun h1 => hx (h₁.1 (h1.trans (map_zero _).symm))
    apply h _ hy
    rw [← hab, ← cupH_natural, h0, map_zero]

/-- The graded cup by a cocycle acts on cohomology as the cup with its class. -/
theorem onH_gradedCup (P : TopPair.{0}) {p : ℕ} (α : singularCochainGroup (ZMod 2) P.fst p)
    (hα : cochainCoboundary (ZMod 2) P.fst p α = 0) (q : ℕ) (x : H (triv P) q) :
    onH (BorelCup.gradedCup P (𝟙 P) (Category.comp_id _) p α hα (cochain_id p α)) q x =
      cupH P (CochainClass.classOf (cochainCxZMod2 P.fst) p α hα) q x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [cupH, BorelCup.ordinaryCup_mk]
  rfl

/-! ### Pairs of subsets of one space with a global class -/

section World

variable {W : TopCat.{0}}

/-- The inclusion of a subset into the ambient space. -/
def incl (t : Set W) : TopCat.of ↥t ⟶ W := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction of an ambient class to a subset. -/
def res {p : ℕ} (b : cohomologyZMod2 W p) (t : Set W) : cohomologyZMod2 (TopCat.of ↥t) p :=
  (cohPullback (incl t) p).hom b

/-- The cup with a global class annihilates no nonzero class of the pair (t, s) in degree q. -/
def CupInjW {p : ℕ} (b : cohomologyZMod2 W p) {s t : Set W} (h : s ⊆ t) (q : ℕ) : Prop :=
  CupInj (pairOf h) (res b t) q

theorem res_pull {p : ℕ} (b : cohomologyZMod2 W p) {s t s' t' : Set W} {h : s ⊆ t}
    {h' : s' ⊆ t'} (f : pairOf h ⟶ pairOf h')
    (hf : TopPair.Hom.fst f ≫ incl t' = incl t) :
    (cohPullback (TopPair.Hom.fst f) p).hom (res b t') = res b t := by
  unfold res
  exact (Finsler.Cup.pullback_comp _ _ p b).symm.trans
    (congrArg (fun g => (cohPullback g p).hom b) hf)

/-- **Transport along a map of pairs over the ambient space.** -/
theorem cupInjW_iff {p : ℕ} (b : cohomologyZMod2 W p) {s t s' t' : Set W} {h : s ⊆ t}
    {h' : s' ⊆ t'} (f : pairOf h ⟶ pairOf h') (hf : TopPair.Hom.fst f ≫ incl t' = incl t)
    {q : ℕ} (h₁ : Function.Bijective (Hmap (trivHom f) q))
    (h₂ : Function.Bijective (Hmap (trivHom f) (p + q))) :
    CupInjW b h' q ↔ CupInjW b h q :=
  cupInj_iff f (res_pull b f hf) h₁ h₂

theorem res_pull_over {W' : TopCat.{0}} (φ : W ⟶ W') {p : ℕ} (b : cohomologyZMod2 W' p)
    {s t : Set W} {s' t' : Set W'} {h : s ⊆ t} {h' : s' ⊆ t'} (f : pairOf h ⟶ pairOf h')
    (hf : TopPair.Hom.fst f ≫ incl t' = incl t ≫ φ) :
    (cohPullback (TopPair.Hom.fst f) p).hom (res b t') = res ((cohPullback φ p).hom b) t := by
  unfold res
  exact (Finsler.Cup.pullback_comp _ _ p b).symm.trans
    ((congrArg (fun g => (cohPullback g p).hom b) hf).trans (Finsler.Cup.pullback_comp _ _ p b))

/-- **Transport along a map of pairs over a map of the ambient spaces.** -/
theorem cupInjW_over {W' : TopCat.{0}} (φ : W ⟶ W') {p : ℕ} (b : cohomologyZMod2 W' p)
    {s t : Set W} {s' t' : Set W'} {h : s ⊆ t} {h' : s' ⊆ t'} (f : pairOf h ⟶ pairOf h')
    (hf : TopPair.Hom.fst f ≫ incl t' = incl t ≫ φ) {q : ℕ}
    (h₁ : Function.Bijective (Hmap (trivHom f) q))
    (h₂ : Function.Bijective (Hmap (trivHom f) (p + q))) :
    CupInjW b h' q ↔ CupInjW ((cohPullback φ p).hom b) h q :=
  cupInj_iff f (res_pull_over φ b f hf) h₁ h₂

/-- **Transport along a map of pairs over a common target of the ambient spaces.** -/
theorem cupInjW_common {W' V : TopCat.{0}} (ψ : W ⟶ V) (ψ' : W' ⟶ V) {p : ℕ}
    (e : cohomologyZMod2 V p) {s t : Set W} {s' t' : Set W'} {h : s ⊆ t} {h' : s' ⊆ t'}
    (f : pairOf h ⟶ pairOf h') (hf : TopPair.Hom.fst f ≫ incl t' ≫ ψ' = incl t ≫ ψ) {q : ℕ}
    (h₁ : Function.Bijective (Hmap (trivHom f) q))
    (h₂ : Function.Bijective (Hmap (trivHom f) (p + q))) :
    CupInjW ((cohPullback ψ' p).hom e) h' q ↔ CupInjW ((cohPullback ψ p).hom e) h q := by
  refine cupInj_iff f ?_ h₁ h₂
  unfold res
  exact (congrArg (cohPullback (TopPair.Hom.fst f) p).hom
    (Finsler.Cup.pullback_comp (incl t') ψ' p e).symm).trans
    ((Finsler.Cup.pullback_comp _ _ p e).symm.trans
      ((congrArg (fun g => (cohPullback g p).hom e) hf).trans (Finsler.Cup.pullback_comp _ _ p e)))

theorem inclPair_over {s t s' t' : Set W} (hst : s ⊆ t) (hst' : s' ⊆ t') (hss : s ⊆ s')
    (htt : t ⊆ t') : TopPair.Hom.fst (inclPair hst hst' hss htt) ≫ incl t' = incl t := rfl

theorem relPair_over {s t u : Set W} (hst : s ⊆ t) (htu : t ⊆ u) :
    TopPair.Hom.fst (relPair hst htu) ≫ incl u = incl u := rfl

theorem incPair_over {s t u : Set W} (hst : s ⊆ t) (htu : t ⊆ u) :
    TopPair.Hom.fst (incPair hst htu) ≫ incl u = incl t := rfl

/-- Transport along an inclusion of pairs. -/
theorem cupInjW_incl {p : ℕ} (b : cohomologyZMod2 W p) {s t s' t' : Set W} (hst : s ⊆ t)
    (hst' : s' ⊆ t') (hss : s ⊆ s') (htt : t ⊆ t') {q : ℕ}
    (h₁ : Function.Bijective (Hmap (trivHom (inclPair hst hst' hss htt)) q))
    (h₂ : Function.Bijective (Hmap (trivHom (inclPair hst hst' hss htt)) (p + q))) :
    CupInjW b hst' q ↔ CupInjW b hst q :=
  cupInjW_iff b _ (inclPair_over hst hst' hss htt) h₁ h₂

/-- Transport along the map (u, s) → (u, t). -/
theorem cupInjW_rel {p : ℕ} (b : cohomologyZMod2 W p) {s t u : Set W} (hst : s ⊆ t)
    (htu : t ⊆ u) {q : ℕ}
    (h₁ : Function.Bijective (Hmap (trivHom (relPair hst htu)) q))
    (h₂ : Function.Bijective (Hmap (trivHom (relPair hst htu)) (p + q))) :
    CupInjW b htu q ↔ CupInjW b (hst.trans htu) q :=
  cupInjW_iff b _ (relPair_over hst htu) h₁ h₂

/-- Transport along the connecting map of a triple. -/
theorem cupInjW_delta {p : ℕ} (b : cohomologyZMod2 W p) {s t u : Set W} (hst : s ⊆ t)
    (htu : t ⊆ u) {q : ℕ} (h₁ : Function.Bijective (tripleDelta hst htu q))
    (h₂ : Function.Bijective (tripleDelta hst htu (p + q))) :
    CupInjW b hst q ↔ CupInjW b htu (q + 1) := by
  let α := CochainClass.representative (cochainCxZMod2 (TopCat.of ↥u)) p (res b u)
  have hα : cochainCoboundary (ZMod 2) (TopCat.of ↥u) p α = 0 :=
    CochainClass.representative_closed _ p (res b u)
  have hcu : CochainClass.classOf (cochainCxZMod2 (TopCat.of ↥u)) p α hα = res b u :=
    CochainClass.classOf_representative _ p (res b u)
  have hct : CochainClass.classOf (cochainCxZMod2 (pairOf hst).fst) p (resα hst htu α)
      (resα_cocycle hst htu α hα) = res b t := by
    rw [← res_pull b (incPair hst htu) (incPair_over hst htu), ← hcu]
    exact (cohPullback_cocycleClass (TopPair.Hom.fst (incPair hst htu)) p α hα).symm
  have key : ∀ x : H (triv (pairOf hst)) q,
      tripleDelta hst htu (p + q) (cupH (pairOf hst) (res b t) q x) =
        cupH (pairOf htu) (res b u) (q + 1) (tripleDelta hst htu q x) := by
    intro x
    have h := tripleDelta_cup hst htu α hα q x
    have e1 : onH (cupTS hst htu α hα) q x = cupH (pairOf hst) (res b t) q x := by
      rw [← hct]
      exact onH_gradedCup _ _ _ q x
    have e2 : onH (cupUT htu α hα) (q + 1) (tripleDelta hst htu q x) =
        cupH (pairOf htu) (res b u) (q + 1) (tripleDelta hst htu q x) := by
      rw [← hcu]
      exact onH_gradedCup _ _ _ (q + 1) _
    rw [e1, e2] at h
    exact h
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := h₁.2 y
    have hx : x ≠ 0 := fun h0 => hy (by rw [h0, map_zero])
    rw [← key]
    intro h0
    exact h x hx (h₂.1 (h0.trans (map_zero _).symm))
  · intro h x hx h0
    have hy : tripleDelta hst htu q x ≠ 0 := fun h1 => hx (h₁.1 (h1.trans (map_zero _).symm))
    apply h _ hy
    rw [← key, h0, map_zero]

end World

/-! ### Maps into a sphere which are never antipodal -/

theorem comb_ne_zero {n : ℕ} (s : unitInterval) (u v : Sphere n)
    (h : (v : Ambient n) ≠ -(u : Ambient n)) :
    (1 - (s : ℝ)) • (u : Ambient n) + (s : ℝ) • (v : Ambient n) ≠ 0 := by
  intro h0
  have he : (1 - (s : ℝ)) • (u : Ambient n) = (s : ℝ) • (-(v : Ambient n)) := by
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left h0
  rcases eq_or_lt_of_le s.property.1 with hs | hs
  · rw [← hs, sub_zero, one_smul, zero_smul] at he
    have := Finsler.DiagonalGeometry.sphere_norm u
    rw [he, norm_zero] at this
    exact zero_ne_one this
  · have hnv : ‖-(v : Ambient n)‖ = 1 := by
      rw [norm_neg]
      exact Finsler.DiagonalGeometry.sphere_norm v
    have := Finsler.DiagonalGeometry.unit_ray_eq hnv (Finsler.DiagonalGeometry.sphere_norm u)
      (sub_nonneg.mpr s.property.2) hs he
    exact h (by rw [this, neg_neg])

/-- The straight homotopy between two maps into the sphere which are never antipodal. -/
def straight {X : TopCat.{0}} {n : ℕ} (f g : X ⟶ Finsler.BorelEvaluation.sphere n)
    (h : ∀ x, (g x : Ambient n) ≠ -(f x : Ambient n)) : TopCat.Homotopy f g where
  toFun p := Finsler.DiagonalGeometry.normalize
    ((1 - (p.1 : ℝ)) • (f p.2 : Ambient n) + (p.1 : ℝ) • (g p.2 : Ambient n))
    (comb_ne_zero p.1 (f p.2) (g p.2) (h p.2))
  continuous_toFun := by
    have hs : Continuous (fun p : unitInterval × X => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hf : Continuous (fun p : unitInterval × X => (f p.2 : Ambient n)) :=
      continuous_subtype_val.comp (f.hom.continuous.comp continuous_snd)
    have hg : Continuous (fun p : unitInterval × X => (g p.2 : Ambient n)) :=
      continuous_subtype_val.comp (g.hom.continuous.comp continuous_snd)
    have hc : Continuous (fun p : unitInterval × X =>
        (1 - (p.1 : ℝ)) • (f p.2 : Ambient n) + (p.1 : ℝ) • (g p.2 : Ambient n)) :=
      ((continuous_const.sub hs).smul hf).add (hs.smul hg)
    have hi : Continuous (fun p : unitInterval × X =>
        ‖(1 - (p.1 : ℝ)) • (f p.2 : Ambient n) + (p.1 : ℝ) • (g p.2 : Ambient n)‖⁻¹) :=
      hc.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (comb_ne_zero p.1 (f p.2) (g p.2) (h p.2)))
    exact (hi.smul hc).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    change ‖(1 - ((0 : unitInterval) : ℝ)) • (f x : Ambient n) +
        ((0 : unitInterval) : ℝ) • (g x : Ambient n)‖⁻¹ •
      ((1 - ((0 : unitInterval) : ℝ)) • (f x : Ambient n) +
        ((0 : unitInterval) : ℝ) • (g x : Ambient n)) = (f x : Ambient n)
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, one_smul, zero_smul, add_zero,
      Finsler.DiagonalGeometry.sphere_norm, inv_one, one_smul]
  map_one_left x := by
    apply Subtype.ext
    change ‖(1 - ((1 : unitInterval) : ℝ)) • (f x : Ambient n) +
        ((1 : unitInterval) : ℝ) • (g x : Ambient n)‖⁻¹ •
      ((1 - ((1 : unitInterval) : ℝ)) • (f x : Ambient n) +
        ((1 : unitInterval) : ℝ) • (g x : Ambient n)) = (g x : Ambient n)
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_smul, one_smul, zero_add,
      Finsler.DiagonalGeometry.sphere_norm, inv_one, one_smul]

/-- **Two maps into the sphere which are never antipodal pull back the same classes.** -/
theorem pullback_eq_of_ne_neg {X : TopCat.{0}} {n k : ℕ}
    (f g : X ⟶ Finsler.BorelEvaluation.sphere n)
    (h : ∀ x, (g x : Ambient n) ≠ -(f x : Ambient n))
    (a : cohomologyZMod2 (Finsler.BorelEvaluation.sphere n) k) :
    (cohPullback f k).hom a = (cohPullback g k).hom a :=
  Finsler.DiagonalCohomology.homotopy_pullback (straight f g h) k a

end

end Finsler.ECup
