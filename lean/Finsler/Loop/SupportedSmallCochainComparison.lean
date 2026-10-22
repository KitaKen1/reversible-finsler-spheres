module

public import Finsler.Loop.SupportedCutCochainCarrierZero
public import Finsler.Topology.CochainClassExact
import all TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-! A closed cochain vanishing on an actual open-cover small-chain
complex has an EXPLICIT subdivision-prism primitive. The primitive
preserves every independent support complement. Consequently equality
on small chains detects equality of genuine RELATIVE cohomology classes. -/
@[expose] public section
namespace Finsler.SupportedSmallCochainComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Simplicial
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

variable {X : TopCat.{0}} {ι : Type*} (U : ι → Set X)

def primitive (n : ℕ) (φ : singularCochainGroup (ZMod 2) X (n + 1)) :
    singularCochainGroup (ZMod 2) X n :=
  TauCeti.singularSmallApproxHom coeff U n (n + 1) ≫ φ

theorem primitive_boundary (hU : ∀ i, IsOpen (U i)) (hc : ⋃ i, U i = Set.univ)
    (n : ℕ) (φ : singularCochainGroup (ZMod 2) X (n + 1))
    (hφ : cochainCoboundary (ZMod 2) X (n + 1) φ = 0)
    (hsmall : (SmallChainCarrier.inclusion X U).f (n + 1) ≫ φ = 0) :
    cochainCoboundary (ZMod 2) X n (primitive U n φ) = φ := by
  have hr : (TauCeti.singularSmallApprox coeff U).f (n + 1) =
      (TauCeti.smallSingularRetraction coeff U hU hc).f (n + 1) ≫
        (SmallChainCarrier.inclusion X U).f (n + 1) :=
    (congrArg (fun f => f.f (n + 1)) (TauCeti.smallSingularRetraction_comp_ι coeff U hU hc)).symm
  have hz : (TauCeti.singularSmallApprox coeff U).f (n + 1) ≫ φ = 0 := by
    rw [hr, Category.assoc, hsmall, comp_zero]
  have he : (𝟙 (chains X) : chains X ⟶ chains X).f (n + 1) - (TauCeti.singularSmallApprox coeff U).f (n + 1) =
      (chains X).d (n + 1) n ≫ TauCeti.singularSmallApproxHom coeff U n (n + 1) +
      TauCeti.singularSmallApproxHom coeff U (n + 1) (n + 2) ≫ (chains X).d (n + 2) (n + 1) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, TauCeti.singularSmallApproxHomotopy] using
      (TauCeti.singularSmallApproxHomotopy coeff U).comm (n + 1)
  have hb := congrArg (fun f => f ≫ φ) he
  have hφ' : (chains X).d (n + 2) (n + 1) ≫ φ = 0 := hφ
  simp only [Preadditive.sub_comp, HomologicalComplex.id_f, Category.id_comp, hz, sub_zero,
    Preadditive.add_comp, Category.assoc, hφ', comp_zero, add_zero] at hb
  exact hb.symm

theorem primitive_support_zero (C : Set X) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X (n + 1))
    (hφ : cochainPullback (SupportedCap.subspaceMap X C) (n + 1) φ = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) n (primitive U n φ) = 0 := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (TopCat.of C)) (R := coeff)
  intro σ
  change (TopCat.toSSet.obj (TopCat.of C)).ιChainComplex σ ≫
    ((push (SupportedCap.subspaceMap X C)).f n ≫
      (TauCeti.singularSmallApproxHom coeff U n (n + 1) ≫ φ)) = 0
  rw [← Category.assoc, push, SSet.ι_chainComplexMap_f]
  let τ := (TopCat.toSSet.map (SupportedCap.subspaceMap X C)).app _ σ
  have ht : τ ∈ (X.smallSingularSubcomplex (fun _ : Unit => C)).obj (Opposite.op ⦋n⦌) :=
    (TopCat.mem_smallSingularSubcomplex_iff X (fun _ : Unit => C) τ).mpr
      ⟨(), TubeCochainExtension.included_range X C σ⟩
  have hp := approximationPrism_preserves U (fun _ : Unit => C)
    (TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff) ⟨τ, ht⟩)
  simpa only [Category.assoc] using
    (CarrierCochainZero.carried_zero (fun _ : Unit => C) (n + 1) φ (fun _ => hφ) hp)

theorem relative_class_eq (C : Set X) (hU : ∀ i, IsOpen (U i)) (hc : ⋃ i, U i = Set.univ)
    (n : ℕ) (φ ψ : RelativeCupCochain.relative (TopPair.ofSubset C) (n + 1))
    (hφ : RelativeCupCochain.differential (TopPair.ofSubset C) (n + 1) φ = 0)
    (hψ : RelativeCupCochain.differential (TopPair.ofSubset C) (n + 1) ψ = 0)
    (he : (SmallChainCarrier.inclusion X U).f (n + 1) ≫ RelativeCupCochain.toAmbient (TopPair.ofSubset C) (n + 1) φ =
      (SmallChainCarrier.inclusion X U).f (n + 1) ≫ RelativeCupCochain.toAmbient (TopPair.ofSubset C) (n + 1) ψ) :
    CochainClass.classOf (RelativeCup.cx (TopPair.ofSubset C)) (n + 1) φ hφ =
      CochainClass.classOf (RelativeCup.cx (TopPair.ofSubset C)) (n + 1) ψ hψ := by
  let P := TopPair.ofSubset C
  let δ := RelativeCupCochain.toAmbient P (n + 1) φ - RelativeCupCochain.toAmbient P (n + 1) ψ
  have hδ : cochainCoboundary (ZMod 2) X (n + 1) δ = 0 := by
    change ((cochainCxZMod2 X).d (n + 1) (n + 2)).hom (_ - _) = 0
    rw [map_sub]
    have hf : cochainCoboundary (ZMod 2) X (n + 1) (RelativeCupCochain.toAmbient P (n + 1) φ) = 0 :=
      (RelativeCupCochain.toAmbient_differential P (n + 1) φ).symm.trans
        ((congrArg (RelativeCupCochain.toAmbient P (n + 2)) hφ).trans (map_zero _))
    have hg : cochainCoboundary (ZMod 2) X (n + 1) (RelativeCupCochain.toAmbient P (n + 1) ψ) = 0 :=
      (RelativeCupCochain.toAmbient_differential P (n + 1) ψ).symm.trans
        ((congrArg (RelativeCupCochain.toAmbient P (n + 2)) hψ).trans (map_zero _))
    change cochainCoboundary (ZMod 2) X (n + 1) (RelativeCupCochain.toAmbient P (n + 1) φ) -
      cochainCoboundary (ZMod 2) X (n + 1) (RelativeCupCochain.toAmbient P (n + 1) ψ) = 0
    rw [hf, hg, sub_self]
  have hs : (SmallChainCarrier.inclusion X U).f (n + 1) ≫ δ = 0 := by
    change _ ≫ (_ - _) = 0
    rw [Preadditive.comp_sub, he, sub_self]
  have hC : cochainPullback (SupportedCap.subspaceMap X C) (n + 1) δ = 0 := by
    change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X C).op).f (n + 1)).hom (_ - _) = 0
    rw [map_sub]
    change cochainPullback P.map (n + 1) (RelativeCupCochain.toAmbient P (n + 1) φ) -
      cochainPullback P.map (n + 1) (RelativeCupCochain.toAmbient P (n + 1) ψ) = 0
    rw [RelativeCupCochain.restriction_toAmbient, RelativeCupCochain.restriction_toAmbient, sub_self]
  obtain ⟨η, hη⟩ := RelativeCupCochain.exists_lift P n (primitive U n δ) (primitive_support_zero U C n δ hC)
  have hb : RelativeCupCochain.differential P n η = φ - ψ := by
    apply RelativeCupCochain.toAmbient_injective P (n + 1)
    rw [RelativeCupCochain.toAmbient_differential, hη, map_sub]
    exact primitive_boundary U hU hc n δ hδ hs
  exact RelativeCupCommutativity.classOf_eq_of_boundary (RelativeCup.cx P) n (n + 1) η φ ψ hφ hψ hb.symm

theorem relative_class_eq_positive (C : Set X) (hU : ∀ i, IsOpen (U i)) (hc : ⋃ i, U i = Set.univ)
    (N : ℕ) (hN : 1 ≤ N) (φ ψ : RelativeCupCochain.relative (TopPair.ofSubset C) N)
    (hφ : RelativeCupCochain.differential (TopPair.ofSubset C) N φ = 0)
    (hψ : RelativeCupCochain.differential (TopPair.ofSubset C) N ψ = 0)
    (he : (SmallChainCarrier.inclusion X U).f N ≫ RelativeCupCochain.toAmbient (TopPair.ofSubset C) N φ =
      (SmallChainCarrier.inclusion X U).f N ≫ RelativeCupCochain.toAmbient (TopPair.ofSubset C) N ψ) :
    CochainClass.classOf (RelativeCup.cx (TopPair.ofSubset C)) N φ hφ =
      CochainClass.classOf (RelativeCup.cx (TopPair.ofSubset C)) N ψ hψ := by
  cases N with
  | zero => omega
  | succ n => exact relative_class_eq U C hU hc n φ ψ hφ hψ he

end
end Finsler.SupportedSmallCochainComparison
