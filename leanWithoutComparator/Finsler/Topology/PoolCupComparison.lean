module

public import Finsler.Topology.RelativeCup
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Associativity

/-! Compare the two actual Alexander–Whitney products on cochains and classes.
This supplies the missing comparison for applying Tau Ceti's singular cap product. -/

@[expose] public section

namespace Finsler.PoolCupComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open SphereOddDegree SphereOddDegree.AlexanderWhitney Finsler.CochainComparison

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem front_subinterval (p q : ℕ) :
    frontFace p q = SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ p + q) := by
  ext i : 3
  apply Fin.ext
  rw [frontFace_apply, SimplexCategory.val_subinterval_toOrderHom_apply]
  omega

theorem back_subinterval (p q : ℕ) :
    backFace p q = SimplexCategory.subinterval p q (by omega : p + q ≤ p + q) := by
  ext i : 3
  apply Fin.ext
  rw [backFace_apply, SimplexCategory.val_subinterval_toOrderHom_apply]

def nativeCup (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    singularCochainGroup (ZMod 2) X (p + q) :=
  TauCeti.ChainComplex.cupCochain (ZMod 2)
    (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv)
    (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom p q (p + q) rfl φ ψ

theorem cochain_comparison (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    nativeCup X p q φ ψ = cochainCup p q φ ψ := by
  apply cochain_ext
  intro σ
  rw [cochainCup_eval]
  unfold cochainEval
  change (((TopCat.toSSet.obj X).ιChainComplex σ ≫ nativeCup X p q φ ψ).hom 1) = _
  unfold nativeCup
  rw [TopCat.ιChainComplex_cupCochain_alexanderWhitneyDiagonal (k := ZMod 2) X
    (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom
    p q (p + q) rfl φ ψ σ]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [mul_comm]
  unfold frontSimplex backSimplex
  rw [front_subinterval, back_subinterval]
  rfl

theorem cohomology_cocycle (X : TopCat.{0}) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    cohomologyEquiv X p (cocycleClass X p φ hφ) =
      CochainClass.classOf (native X) p φ hφ := by
  change (HomologicalComplex.homologyMap (cochainIso X).hom p).hom
    (CochainClass.classOf (cochainCxZMod2 X) p φ hφ) = _
  exact CochainClass.classOf_map (cochainCxZMod2 X) (cochainIso X).hom p φ hφ hφ

theorem native_cup_class (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    X.singularCup (ZMod 2) (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv
        (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom p q (p + q) rfl
        (CochainClass.classOf (native X) p φ hφ)
        (CochainClass.classOf (native X) q ψ hψ) =
      CochainClass.classOf (native X) (p + q) (cochainCup p q φ ψ)
        (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ) := by
  unfold CochainClass.classOf
  refine (TopCat.singularCup_homologyπ X (ZMod 2)
    (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom
    p q (p + q) rfl
    ((native X).cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)
    ((native X).cyclesMk ψ (q + 1) (CochainClass.next_eq q) hψ)).trans ?_
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [TauCeti.ChainComplex.iCycles_cupCycles (k := ZMod 2)
    (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv)
    (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom p q (p + q) rfl]
  change nativeCup X p q
    (((native X).iCycles p).hom ((native X).cyclesMk φ (p + 1) _ hφ))
    (((native X).iCycles q).hom ((native X).cyclesMk ψ (q + 1) _ hψ)) =
      ((native X).iCycles (p + q)).hom ((native X).cyclesMk (cochainCup p q φ ψ)
        (p + q + 1) _ _)
  exact (congrArg₂ (nativeCup X p q)
    ((native X).i_cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)
    ((native X).i_cyclesMk ψ (q + 1) (CochainClass.next_eq q) hψ)).trans
      ((cochain_comparison X p q φ ψ).trans
        ((native X).i_cyclesMk (cochainCup p q φ ψ) (p + q + 1)
          (CochainClass.next_eq (p + q))
          (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ)).symm)

theorem cohomology_comparison (X : TopCat.{0}) (p q : ℕ)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) :
    cohomologyEquiv X (p + q) (cupZMod2 a b) =
      X.singularCup (ZMod 2) (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv
        (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom p q (p + q) rfl
        (cohomologyEquiv X p a) (cohomologyEquiv X q b) := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective X p a
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective X q b
  rw [cupZMod2_mk, cohomology_cocycle, cohomology_cocycle, cohomology_cocycle]
  exact (native_cup_class X p q φ ψ hφ hψ).symm

end

end Finsler.PoolCupComparison
