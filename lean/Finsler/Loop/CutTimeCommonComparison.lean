module

public import Finsler.Loop.CylinderCommonCover
public import Finsler.Topology.CutDomainTimePrism
public import Finsler.Topology.NestedCapRefinement
public import Finsler.Topology.RetainedTimeAlignment
public import Finsler.Topology.PrismRefinementHomology

/-! Compare an actual cut-domain time operation with a second source
model using one common cylinder cover. The actual collar constructs a
closed intermediate operation. Both relative refinement comparisons
stay in the prescribed target complexes, including output degree zero. -/

@[expose] public section
namespace Finsler.CutTimeCommonComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree TauCeti
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem homology_eq (X Z : TopCat.{0}) {ι κ : Type*}
    (U : ι → Set (ClosedInterval × X)) (V : κ → Set Z)
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
    (hV : ∀ j, IsOpen (V j)) (hcV : ⋃ j, V j = Set.univ)
    (f : TopCat.of (ClosedInterval × X) ⟶ Z)
    (E F : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (j : E ⟶ F) (m p : ℕ)
    (c : ∀ q, (small (TopCat.of (ClosedInterval × X)) U).X ((m + 1) + (p + q)) ⟶ E.X q)
    (hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
      (small (TopCat.of (ClosedInterval × X)) U).d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q)
    (A : Set (ClosedInterval × X))
    (φ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) (m + 1))
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) p)
    (hφ : cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) A) (m + 1) φ = 0)
    (b : E ⟶ chains (TopCat.of (ClosedInterval × X))) (hb : ∀ q, Mono (b.f q))
    (hi : ∀ q, c q ≫ b.f q =
      (inclusion (TopCat.of (ClosedInterval × X)) U).f ((m + 1) + (p + q)) ≫
        PartialDoubleCap.cap (TopCat.of (ClosedInterval × X)) (m + 1) p q φ ψ)
    (h₀ : ∀ x, ((0 : ClosedInterval), x) ∈ A) (h₁ : ∀ x, ((1 : ClosedInterval), x) ∈ A)
    (d : ∀ q, (small Z V).X ((m + 1) + (p + q)) ⟶ F.X q)
    (hd : ∀ q, d (q + 1) ≫ F.d (q + 1) q =
      (small Z V).d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ d q)
    (hcap : ∀ q,
      (CylinderCommonCover.toSource (X := TopCat.of (ClosedInterval × X)) (Y := Z) U V f).f
        ((m + 1) + (p + q)) ≫ c q ≫ j.f q =
      (CylinderCommonCover.toTarget (X := TopCat.of (ClosedInterval × X)) (Y := Z) U V f).f
        ((m + 1) + (p + q)) ≫ d q)
    (w : DegreeLoweringHomology.Map (chains X) E (m + p))
    (hw : ∀ q, w.component q = AnnularTimeTrim.prism X ((m + p) + q) ≫
      ClosedCapDegreeTransport.align m p (CutDomainTimePrism.retracted X U hU hcU E m p c) q)
    (v : DegreeLoweringHomology.Map (chains X) F (m + p))
    (hv : ∀ q, v.component q = AnnularTimeTrim.prism X ((m + p) + q) ≫
      (push f ≫ smallSingularRetraction (X := Z) coeff V hV hcV).f ((m + p) + q + 1) ≫
        ClosedCapDegreeTransport.align m p d q) (q : ℕ) :
    (w.post j).homology q = v.homology q := by
  let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
  let W := CylinderCommonCover.cover (X := C) (Y := Z) U V f
  let hW := CylinderCommonCover.cover_open (X := C) (Y := Z) U V f hU hV
  let hcW := CylinderCommonCover.cover_univ (X := C) (Y := Z) U V f hcU hcV
  let Ms := CylinderCommonCover.toSource (X := C) (Y := Z) U V f
  let Mt := CylinderCommonCover.toTarget (X := C) (Y := Z) U V f
  let R := smallSingularRetraction (X := C) coeff W hW hcW
  let c' := NestedCapRefinement.pre (m + 1) p Ms c
  have hc' := NestedCapRefinement.pre_comm (m + 1) p Ms c hc
  have hi' := NestedCapRefinement.pre_inclusion C U W Ms
    (CylinderCommonCover.toSource_inclusion (X := C) (Y := Z) U V f) E b (m + 1) p φ ψ c hi
  let w' := CutDomainTimePrism.operation X W hW hcW E m p c' A φ ψ hφ b hb hi' hc' h₀ h₁
  have hrW : CutDomainTimePrism.retracted X W hW hcW E m p c' =
      (fun t => R.f ((m + 1) + (p + t)) ≫ c' t) := rfl
  have hw' (t : ℕ) : w'.component t = AnnularTimeTrim.prism X ((m + p) + t) ≫
      (R ≫ Ms).f ((m + p) + t + 1) ≫ ClosedCapDegreeTransport.align m p c t := by
    change AnnularTimeTrim.prism X ((m + p) + t) ≫
      ClosedCapDegreeTransport.align m p (CutDomainTimePrism.retracted X W hW hcW E m p c') t = _
    rw [hrW]
    have he := ClosedCapFunctoriality.align_pre (R ≫ Ms) m p c t
    simpa only [CutDomainTimePrism.retracted, R, C, c', NestedCapRefinement.pre,
      HomologicalComplex.comp_f, Category.assoc] using
      congrArg (fun z => AnnularTimeTrim.prism X ((m + p) + t) ≫ z) he
  have hid : push (𝟙 C) = 𝟙 (chains C) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 C)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have hfirst : w.homology q = w'.homology q := by
    apply PrismRefinementHomology.homology_eq X C W U hW hcW hU hcU (𝟙 C) Prod.fst
      (fun _ _ hz => hz.1) E (m + p) (ClosedCapDegreeTransport.align m p c)
      (ClosedCapDegreeTransport.align_comm m p c hc) w w'
    · intro t
      rw [hw t, hid, Category.id_comp]
      have hrU : CutDomainTimePrism.retracted X U hU hcU E m p c =
          (fun s => (smallSingularRetraction (X := C) coeff U hU hcU).f ((m + 1) + (p + s)) ≫ c s) := rfl
      rw [hrU, ClosedCapFunctoriality.align_pre]
    · intro t
      exact hw' t
  have hcap' (t : ℕ) : c' t ≫ j.f t = Mt.f ((m + 1) + (p + t)) ≫ d t := by
    exact hcap t
  have hwj (t : ℕ) : (w'.post j).component t = AnnularTimeTrim.prism X ((m + p) + t) ≫
      (R ≫ Mt).f ((m + p) + t + 1) ≫ ClosedCapDegreeTransport.align m p d t := by
    have he := RetainedTimeAlignment.agreement R Mt j m p c' d hcap' t
    change (AnnularTimeTrim.prism X ((m + p) + t) ≫
      ClosedCapDegreeTransport.align m p (CutDomainTimePrism.retracted X W hW hcW E m p c') t) ≫ j.f t = _
    rw [hrW]
    simpa only [Category.assoc] using
      congrArg (fun z => AnnularTimeTrim.prism X ((m + p) + t) ≫ z) he
  have hsecond : v.homology q = (w'.post j).homology q :=
    PrismRefinementHomology.homology_eq X Z W V hW hcW hV hcV f Prod.snd
      (fun _ _ hz => hz.2) F (m + p) (ClosedCapDegreeTransport.align m p d)
      (ClosedCapDegreeTransport.align_comm m p d hd) v (w'.post j) hv hwj q
  rw [DegreeLoweringHomology.Map.post_homology, hfirst, ← DegreeLoweringHomology.Map.post_homology]
  exact hsecond.symm

end
end Finsler.CutTimeCommonComparison
