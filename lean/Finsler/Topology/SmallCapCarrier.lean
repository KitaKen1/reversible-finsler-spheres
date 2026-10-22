module

public import Finsler.Topology.SmallChainCarrier
public import Finsler.Topology.RelativeCapBoundary

/-! The actual Alexander--Whitney cap preserves every carrier family.
Its restriction to small chains is given by the same front evaluation and
back face, and obeys the boundary identity for a closed F₂ cochain. -/

@[expose] public section

namespace Finsler.SmallCapCarrier

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology Simplicial
open SphereOddDegree Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def weight (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p) (σ : TopCat.toSSet.obj X _⦋n⦌) : coeff ⟶ coeff :=
  (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv ≫
    (((TopCat.toSSet.obj X).ιChainComplex
      ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ▷
        (𝟙_ (ModuleCat (ZMod 2)))) ≫
    (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom

theorem cap_simplex (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p) (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X p q n h φ =
      weight X p q n h φ σ ≫ (TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) := by
  simpa only [absoluteChain, Finsler.RelativeCap.diagonal, weight, Category.assoc] using
    TopCat.ιChainComplex_capChain_alexanderWhitneyDiagonal X
      (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom p q n h φ σ

def smallCap (X : TopCat.{0}) {ι : Type*} (V : ι → Set X)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) X p) :
    (small X V).X n ⟶ (small X V).X q :=
  Cofan.IsColimit.desc ((X.smallSingularSubcomplex V : SSet).isColimitChainComplexXCofan coeff n)
    fun σ => weight X p q n h φ σ.val ≫ (X.smallSingularSubcomplex V : SSet).ιChainComplex
      ((X.smallSingularSubcomplex V : SSet).map (SimplexCategory.subinterval p q (by omega)).op σ)

theorem smallCap_inclusion (X : TopCat.{0}) {ι : Type*} (V : ι → Set X)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) X p) :
    smallCap X V p q n h φ ≫ (inclusion X V).f q =
      (inclusion X V).f n ≫ absoluteChain X p q n h φ := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex V : SSet)) (R := coeff)
  intro σ
  have hc : (X.smallSingularSubcomplex V : SSet).ιChainComplex σ ≫
      smallCap X V p q n h φ = weight X p q n h φ σ.val ≫
        (X.smallSingularSubcomplex V : SSet).ιChainComplex
          ((X.smallSingularSubcomplex V : SSet).map
            (SimplexCategory.subinterval p q (by omega)).op σ) :=
    Cofan.IsColimit.fac _ _ σ
  rw [← Category.assoc, hc, Category.assoc]
  simp only [inclusion, SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f_assoc]
  exact (cap_simplex X p q n h φ σ.val).symm

theorem cap_preserves {X : TopCat.{0}} {ι : Type*} (V : ι → Set X)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) X p)
    {c : coeff ⟶ (chains X).X n} (hc : c ∈ supported X V n) :
    c ≫ absoluteChain X p q n h φ ∈ supported X V q := by
  obtain ⟨g, rfl⟩ := (TauCeti.mem_smallSingularChains_iff _).mp hc
  refine (TauCeti.mem_smallSingularChains_iff _).mpr ⟨g ≫ smallCap X V p q n h φ, ?_⟩
  rw [Category.assoc, smallCap_inclusion, ← Category.assoc]

theorem cap_parent {X : TopCat.{0}} (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p) (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X p q n h φ ∈
      supported X (parentFamily σ) q :=
  cap_preserves (parentFamily σ) p q n h φ (simplex_parent σ)

theorem smallCap_boundary (X : TopCat.{0}) {ι : Type*} (V : ι → Set X)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    smallCap X V p (q + 1) (n + 1) (by omega) φ ≫ (small X V).d (q + 1) q =
      (small X V).d (n + 1) n ≫ smallCap X V p q n h φ := by
  letI : Mono ((inclusion X V).f q) :=
    inferInstanceAs (Mono ((sigmaConst.obj coeff).map
      ((X.smallSingularSubcomplex V).ι.app (Opposite.op ⦋q⦌))))
  apply (cancel_mono ((inclusion X V).f q)).mp
  calc
    _ = smallCap X V p (q + 1) (n + 1) (by omega) φ ≫
        ((inclusion X V).f (q + 1) ≫ (chains X).d (q + 1) q) := by
      rw [Category.assoc, ← HomologicalComplex.Hom.comm]
    _ = (inclusion X V).f (n + 1) ≫
        (absoluteChain X p (q + 1) (n + 1) (by omega) φ ≫ (chains X).d (q + 1) q) := by
      rw [← Category.assoc, smallCap_inclusion, Category.assoc]
    _ = (inclusion X V).f (n + 1) ≫
        ((chains X).d (n + 1) n ≫ absoluteChain X p q n h φ) := by
      rw [Finsler.RelativeCapBoundary.absolute_chain_boundary X p q n h φ hφ]
    _ = _ := by
      rw [← Category.assoc, HomologicalComplex.Hom.comm, Category.assoc,
        ← smallCap_inclusion, ← Category.assoc]


end
end Finsler.SmallCapCarrier
