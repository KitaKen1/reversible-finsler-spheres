module

public import Finsler.Topology.RelativeCapBoundary

/-! Identify the actual relative cap product with the dual of the existing relative cup action. -/

@[expose] public section

namespace Finsler.RelativeCapDual

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open SphereOddDegree Finsler.CochainComparison Finsler.RelativeCap
open Finsler.RelativeCapAssociativity

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem absolute_chain_dual (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    absoluteChain X p q (p + q) rfl φ ≫ ψ = cochainCup p q φ ψ := by
  have hn : absoluteChain X p q (p + q) rfl φ ≫ ψ =
      PoolCupComparison.nativeCup X p q φ ψ := by
    unfold absoluteChain PoolCupComparison.nativeCup
    rw [RelativeCapAbsolute.pairing_eq_action]
    rw [TauCeti.ChainComplex.capChain_apply, TauCeti.ChainComplex.cupCochain_apply,
      Category.assoc, TauCeti.ChainComplex.tensorCochain_comp]
    change (diagonal X).f (p + q) ≫
        TauCeti.ChainComplex.tensorCochain ((λ_ ((absolute X).X q)).hom ≫ ψ) φ (𝟙 _) (p + q) =
      (diagonal X).f (p + q) ≫
        TauCeti.ChainComplex.tensorCochain (ρ_ coeff).hom φ ψ (p + q)
    have hu : (λ_ ((absolute X).X q)).hom ≫ ψ = (coeff ◁ ψ) ≫ (λ_ coeff).hom :=
      (leftUnitor_naturality (show (absolute X).X q ⟶ coeff from ψ)).symm
    refine (congrArg (fun μ => (diagonal X).f (p + q) ≫
      TauCeti.ChainComplex.tensorCochain μ φ (𝟙 ((absolute X).X q)) (p + q)) hu).trans ?_
    rw [TauCeti.ChainComplex.tensorCochain_whiskerLeft_comp, Category.id_comp]
    exact congrArg (fun μ => (diagonal X).f (p + q) ≫
      TauCeti.ChainComplex.tensorCochain μ φ ψ (p + q))
      (show (λ_ coeff).hom = (ρ_ coeff).hom from unitors_equal (C := ModuleCat (ZMod 2)))
  exact hn.trans (PoolCupComparison.cochain_comparison X p q φ ψ)

theorem relative_chain_dual (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : RelativeCupCochain.relative P q) :
    chain P p q (p + q) rfl φ ≫ ψ = RelativeCupCochain.cup P p q φ ψ := by
  have : Epi (quotient P) := (P.shortExact_singularChainComplexShortComplex coeff).epi_g
  apply (cancel_epi ((quotient P).f (p + q))).mp
  have hq := RelativeCapAbsolute.quotient_capChain P p q (p + q) rfl φ
  have hc := absolute_chain_dual P.fst p q φ (RelativeCupCochain.toAmbient P q ψ)
  have hi := RelativeCupCochain.toAmbient_cup P p q φ ψ
  calc
    (quotient P).f (p + q) ≫ (chain P p q (p + q) rfl φ ≫ ψ) =
        (absoluteChain P.fst p q (p + q) rfl φ ≫ (quotient P).f q) ≫ ψ := by
      rw [hq, Category.assoc]
    _ = absoluteChain P.fst p q (p + q) rfl φ ≫ RelativeCupCochain.toAmbient P q ψ :=
      Category.assoc _ _ _
    _ = cochainCup p q φ (RelativeCupCochain.toAmbient P q ψ) := hc
    _ = (quotient P).f (p + q) ≫ RelativeCupCochain.cup P p q φ ψ := hi.symm

/-- Evaluation of an existing relative cup class equals evaluation after the actual cap. -/
theorem cup_cap (P : TopPair.{0}) (p q : ℕ)
    (a : cohomologyZMod2 P.fst p) (b : RelativeCup.cohomology P q)
    (x : P.singularHomology (C := ModuleCat (ZMod 2)) coeff (p + q)) :
    RelativeKronecker.comparison P (p + q) (RelativeCup.cup P p q a b) x =
      RelativeKronecker.comparison P q b (RelativeCap.cap P p q (p + q) rfl a x) := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective P.fst p a
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ : RelativeCupCochain.relative P q,
      ∃ hψ : RelativeCupCochain.differential P q ψ = 0,
        CochainClass.classOf (RelativeCup.cx P) q ψ hψ = b :=
    ⟨CochainClass.representative (RelativeCup.cx P) q b,
      CochainClass.representative_closed (RelativeCup.cx P) q b,
      CochainClass.classOf_representative (RelativeCup.cx P) q b⟩
  obtain ⟨z, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective (relative P) (p + q) x
  have hc := ConcreteCategory.congr_hom (RelativeCap.cap_class P p q (p + q) rfl φ hφ) z
  change RelativeCap.cap P p q (p + q) rfl (cocycleClass P.fst p φ hφ)
      (((relative P).homologyπ (p + q)).hom z) =
    ((relative P).homologyπ q).hom ((cycleOf P p q (p + q) rfl φ hφ).hom z) at hc
  have hi : cycleOf P p q (p + q) rfl φ hφ ≫ (relative P).iCycles q =
      (relative P).iCycles (p + q) ≫ chain P p q (p + q) rfl φ := by
    refine (TauCeti.ChainComplex.capCycles_i (relativeDiagonal P) (unitAction P)
      p q (p + q) rfl ((native P.fst).cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)).trans ?_
    exact congrArg (fun η => (relative P).iCycles (p + q) ≫ chain P p q (p + q) rfl η)
      ((native P.fst).i_cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)
  have hcup := RelativeCup.cup_mk P p q φ hφ ψ hψ
  have hχ := RelativeCupCochain.preserves_cocycles P p q φ ψ hφ hψ
  refine ((congrArg (fun b => RelativeKronecker.comparison P (p + q) b
    (((relative P).homologyπ (p + q)).hom z)) hcup).trans
      (RelativeKronecker.comparison_classOf P (p + q) (RelativeCupCochain.cup P p q φ ψ)
        hχ z)).trans ?_
  calc
    (RelativeCupCochain.cup P p q φ ψ).hom (((relative P).iCycles (p + q)).hom z) =
        ψ.hom ((chain P p q (p + q) rfl φ).hom (((relative P).iCycles (p + q)).hom z)) :=
      (ConcreteCategory.congr_hom (relative_chain_dual P p q φ ψ)
        (((relative P).iCycles (p + q)).hom z)).symm
    _ = ψ.hom (((relative P).iCycles q).hom ((cycleOf P p q (p + q) rfl φ hφ).hom z)) :=
      congrArg ψ.hom (ConcreteCategory.congr_hom hi z).symm
    _ = RelativeKronecker.comparison P q
        (CochainClass.classOf (RelativeCup.cx P) q ψ hψ)
        (((relative P).homologyπ q).hom ((cycleOf P p q (p + q) rfl φ hφ).hom z)) :=
      (RelativeKronecker.comparison_classOf P q ψ hψ _).symm
    _ = _ := congrArg (RelativeKronecker.comparison P q
      (CochainClass.classOf (RelativeCup.cx P) q ψ hψ)) hc.symm

/-- The previously constructed action on the homology dual is precomposition by actual cap. -/
theorem cupDual_cap (P : TopPair.{0}) (p q : ℕ) (a : cohomologyZMod2 P.fst p)
    (φ : RelativeDual.relative (ZMod 2) P q)
    (x : P.singularHomology (C := ModuleCat (ZMod 2)) coeff (p + q)) :
    RelativeKronecker.cupDual P p q a φ x = φ (RelativeCap.cap P p q (p + q) rfl a x) := by
  obtain ⟨b, rfl⟩ := (RelativeKronecker.equiv P q).surjective φ
  rw [RelativeKronecker.cupDual_comparison, RelativeKronecker.equiv_apply,
    RelativeKronecker.equiv_apply]
  exact cup_cap P p q a b x


end
end Finsler.RelativeCapDual
