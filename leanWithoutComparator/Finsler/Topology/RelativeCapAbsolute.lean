module

public import Finsler.Topology.RelativeCap

/-! compare relative cap with ordinary cap through
the actual quotient from ambient to relative singular chains. -/

@[expose] public section

namespace Finsler.RelativeCapAbsolute

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open SphereOddDegree Finsler.CochainComparison Finsler.RelativeCap

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def absoluteAction (X : TopCat.{0}) :
    ((tensorLeft coeff).mapHomologicalComplex (ComplexShape.down ℕ)).obj (absolute X) ⟶
      absolute X where
  f q := (λ_ ((absolute X).X q)).hom
  comm' i j _ := by exact (leftUnitor_naturality ((absolute X).d i j)).symm

theorem pairing_eq_action (X : TopCat.{0}) :
    (TopCat.toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom =
      absoluteAction X := by
  ext q : 1
  apply (cancel_epi (λ_ ((absolute X).X q)).inv).mp
  apply SSet.chainComplex_hom_ext
  intro σ
  change (TopCat.toSSet.obj X).ιChainComplex σ ≫ (λ_ ((absolute X).X q)).inv ≫
      ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom).f q =
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (λ_ ((absolute X).X q)).inv ≫
      (λ_ ((absolute X).X q)).hom
  rw [leftUnitor_inv_naturality_assoc,
    SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f,
    ← unitors_equal]
  simp only [Iso.inv_hom_id, Category.comp_id]
  change (λ_ coeff).inv ≫ (λ_ coeff).hom ≫ _ = _
  exact Iso.inv_hom_id_assoc _ _

theorem quotient_action (P : TopPair.{0}) :
    (TopCat.toSSet.obj P.fst).chainComplexPairing (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom ≫
        quotient P =
      ((tensorLeft coeff).mapHomologicalComplex (ComplexShape.down ℕ)).map (quotient P) ≫
        unitAction P := by
  rw [pairing_eq_action]
  ext q : 1
  exact (leftUnitor_naturality ((quotient P).f q)).symm

theorem quotient_capChain (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) P.fst p) :
    TauCeti.ChainComplex.capChain (ZMod 2) (diagonal P.fst)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing
          (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom) p q n h φ ≫ (quotient P).f q =
      (quotient P).f n ≫ TauCeti.ChainComplex.capChain (ZMod 2)
        (relativeDiagonal P) (unitAction P) p q n h φ := by
  exact TauCeti.ChainComplex.capChain_naturality (k := ZMod 2)
    (relativeDiagonal P) (unitAction P) (diagonal P.fst)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing
      (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom)
    (quotient P) (𝟙 _) (quotient P) (quotient P) (quotient_diagonal P)
    (quotient_action P) p q n h φ

theorem quotient_cap (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (a : cohomologyZMod2 P.fst p) (x : Finsler.PoolCap.homology P.fst n) :
    (P.singularHomologyπ coeff q).hom (Finsler.PoolCap.cap P.fst p q n h a x) =
      Finsler.RelativeCap.cap P p q n h a ((P.singularHomologyπ coeff n).hom x) := by
  have hn := TauCeti.ChainComplex.cap_naturality (k := ZMod 2)
      (relativeDiagonal P) (unitAction P) (diagonal P.fst)
      ((TopCat.toSSet.obj P.fst).chainComplexPairing
        (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom)
      (quotient P) (𝟙 _) (quotient P) (quotient P) (quotient_diagonal P)
      (quotient_action P) p q n h (cohomologyEquiv P.fst p a)
  let F := TauCeti.ChainComplex.linearYonedaFunctor (C := ModuleCat (ZMod 2))
    (α := ℕ) (ZMod 2) coeff
  have hi : (HomologicalComplex.homologyMap
      (F.map (𝟙 (absolute P.fst)).op) p).hom (cohomologyEquiv P.fst p a) =
        cohomologyEquiv P.fst p a :=
    ConcreteCategory.congr_hom
      ((F ⋙ HomologicalComplex.homologyFunctor _ _ p).map_id
        (Opposite.op (absolute P.fst))) (cohomologyEquiv P.fst p a)
  have he := congrArg (fun z => TauCeti.ChainComplex.cap (ZMod 2) (diagonal P.fst)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing
      (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom) p q n h z ≫
        HomologicalComplex.homologyMap (quotient P) q) hi
  let S := P.fst.singularCap (ZMod 2) (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv
    (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom p q n h
  let G := TauCeti.ChainComplex.cap (ZMod 2) (diagonal P.fst)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing
      (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom) p q n h
  have hs : S (cohomologyEquiv P.fst p a) = G (cohomologyEquiv P.fst p a) := by
    obtain ⟨φ, hφ⟩ := HomologicalComplex.moduleCat_homologyπ_surjective (native P.fst) p
      (cohomologyEquiv P.fst p a)
    have hm : S (((native P.fst).homologyπ p).hom φ) =
        G (((native P.fst).homologyπ p).hom φ) := by
      apply (cancel_epi ((absolute P.fst).homologyπ n)).mp
      exact (TopCat.singularCap_homologyπ P.fst (ZMod 2)
        (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom
        p q n h φ).trans
          (TauCeti.ChainComplex.cap_homologyπ (diagonal P.fst)
            ((TopCat.toSSet.obj P.fst).chainComplexPairing
              (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom) p q n h φ).symm
    exact (congrArg S hφ).symm.trans (hm.trans (congrArg G hφ))
  unfold Finsler.PoolCap.cap Finsler.RelativeCap.cap
  exact (congrArg (fun z => (P.singularHomologyπ coeff q).hom (z.hom x)) hs).trans
    (ConcreteCategory.congr_hom (he.symm.trans hn) x)

end

end Finsler.RelativeCapAbsolute
