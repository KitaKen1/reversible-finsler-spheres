module

public import Finsler.Topology.AWInterchange
public import Finsler.Topology.SmallRectangleCross
public import Finsler.Topology.SupportedCapNaturality
public import TauCeti.AlgebraicTopology.Singular.EilenbergZilber

/-! Reuse the actual Alexander-Whitney interchange homotopy and both
genuine Eilenberg-Zilber inverses to interchange the actual shuffle.
Coefficient multiplication is retained throughout. -/

@[expose] public section
namespace Finsler.SingularShuffleSwap
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SingularChainCross
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

theorem coefficient_unit_braid : (β_ coeff coeff).hom ≫ (λ_ coeff).hom = (λ_ coeff).hom := by
  have he : (λ_ coeff).hom = (ρ_ coeff).hom := by
    change (λ_ (𝟙_ (ModuleCat (ZMod 2)))).hom = (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom
    exact unitors_equal
  rw [he]
  change (β_ (𝟙_ (ModuleCat (ZMod 2))) (𝟙_ (ModuleCat (ZMod 2)))).hom ≫
    (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom = (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom
  rw [braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id, Category.comp_id, unitors_equal]

theorem coefficient_braid_multiply (K : SSet.{0}) :
    coefficient K (β_ coeff coeff).hom ≫ coefficient K (λ_ coeff).hom =
      coefficient K (λ_ coeff).hom := by
  change (((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).map (β_ coeff coeff).hom) ≫
    ((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).map (λ_ coeff).hom)).app K = _
  rw [← CategoryTheory.Functor.map_comp, coefficient_unit_braid]
  rfl

def exchange (X Y : TopCat.{0}) :=
  coefficient (TopCat.toSSet.obj (X ⊗ Y)) (β_ coeff coeff).hom ≫
    SSet.chainComplexMap (TopCat.toSSet.map (β_ X Y).hom) (coeff ⊗ coeff)

theorem exchange_multiply (X Y : TopCat.{0}) :
    exchange X Y ≫ coefficient (TopCat.toSSet.obj (Y ⊗ X)) (λ_ coeff).hom =
      coefficient (TopCat.toSSet.obj (X ⊗ Y)) (λ_ coeff).hom ≫ push (β_ X Y).hom := by
  have hn := (((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).map (λ_ coeff).hom).naturality
    (TopCat.toSSet.map (β_ X Y).hom))
  change SSet.chainComplexMap (TopCat.toSSet.map (β_ X Y).hom) (coeff ⊗ coeff) ≫
      coefficient (TopCat.toSSet.obj (Y ⊗ X)) (λ_ coeff).hom =
    coefficient (TopCat.toSSet.obj (X ⊗ Y)) (λ_ coeff).hom ≫ push (β_ X Y).hom at hn
  rw [exchange, Category.assoc, hn, ← Category.assoc, coefficient_braid_multiply]

theorem shuffle_homology (X Y : TopCat.{0}) (k : ℕ) :
    homologyMap (TauCeti.NatChainComplex.koszulBraidingHom (chains X) (chains Y)) k ≫
      homologyMap (TopCat.shuffle Y X coeff coeff) k =
    homologyMap (TopCat.shuffle X Y coeff coeff) k ≫ homologyMap (exchange X Y) k := by
  have hl := (TopCat.shuffleAlexanderWhitneyHomotopy X Y coeff coeff).homologyMap_eq k
  rw [homologyMap_comp, homologyMap_id] at hl
  have hr := (TopCat.alexanderWhitneyShuffleHomotopy Y X coeff coeff).homologyMap_eq k
  rw [homologyMap_comp, homologyMap_id] at hr
  have hs : homologyMap (TopCat.alexanderWhitney X Y coeff coeff) k ≫
      homologyMap (TauCeti.NatChainComplex.koszulBraidingHom (chains X) (chains Y)) k =
    homologyMap (exchange X Y) k ≫ homologyMap (TopCat.alexanderWhitney Y X coeff coeff) k := by
    simpa only [exchange, coefficient, chains, homologyMap_comp, Category.assoc] using
      (AWInterchange.alexanderWhitneyKoszulBraidingHomotopy X Y coeff coeff).homologyMap_eq k
  calc
    _ = (homologyMap (TopCat.shuffle X Y coeff coeff) k ≫
        homologyMap (TopCat.alexanderWhitney X Y coeff coeff) k) ≫
        homologyMap (TauCeti.NatChainComplex.koszulBraidingHom (chains X) (chains Y)) k ≫
        homologyMap (TopCat.shuffle Y X coeff coeff) k := by rw [hl, Category.id_comp]
    _ = homologyMap (TopCat.shuffle X Y coeff coeff) k ≫
        (homologyMap (TopCat.alexanderWhitney X Y coeff coeff) k ≫
          homologyMap (TauCeti.NatChainComplex.koszulBraidingHom (chains X) (chains Y)) k) ≫
        homologyMap (TopCat.shuffle Y X coeff coeff) k := by simp only [Category.assoc]
    _ = homologyMap (TopCat.shuffle X Y coeff coeff) k ≫
        (homologyMap (exchange X Y) k ≫ homologyMap (TopCat.alexanderWhitney Y X coeff coeff) k) ≫
        homologyMap (TopCat.shuffle Y X coeff coeff) k := by rw [hs]
    _ = homologyMap (TopCat.shuffle X Y coeff coeff) k ≫ homologyMap (exchange X Y) k ≫
        (homologyMap (TopCat.alexanderWhitney Y X coeff coeff) k ≫
          homologyMap (TopCat.shuffle Y X coeff coeff) k) := by simp only [Category.assoc]
    _ = _ := by rw [hr, Category.comp_id]

theorem ambient_homology (X Y : TopCat.{0}) (k : ℕ) :
    homologyMap (TauCeti.NatChainComplex.koszulBraidingHom (chains X) (chains Y)) k ≫
      homologyMap (SmallRectangleCross.ambient Y X) k =
    homologyMap (SmallRectangleCross.ambient X Y) k ≫ homologyMap (push (β_ X Y).hom) k := by
  simp only [SmallRectangleCross.ambient, homologyMap_comp]
  rw [← Category.assoc, shuffle_homology, Category.assoc,
    ← homologyMap_comp, exchange_multiply, homologyMap_comp, Category.assoc]

end
end Finsler.SingularShuffleSwap
