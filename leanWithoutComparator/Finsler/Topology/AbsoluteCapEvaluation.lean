module

public import Finsler.Topology.ChainEvaluation
public import Finsler.Topology.RelativeCapDual

/-! Absolute cap is the genuine Kronecker dual of the existing cup product.
The proof compares the actual cap/cup cochains on cycles and then uses the
existing homology quotient and the actual Kronecker map. -/

@[expose] public section

namespace Finsler.AbsoluteCapEvaluation

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.RelativeCapAssociativity
open Finsler.ChainEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem cochain_duality (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    ModuleCat.ofHom (PoolCap.cap X p q (p + q) rfl (cocycleClass X p φ hφ)) ≫
      evaluation (chainCxZMod2 X) q ψ hψ =
      evaluation (chainCxZMod2 X) (p + q) (cochainCup p q φ ψ)
        (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ) := by
  apply (cancel_epi ((chainCxZMod2 X).homologyπ (p + q))).mp
  calc
    _ = RelativeCapBoundary.absoluteCycleOf X p q (p + q) rfl φ hφ ≫
        ((chainCxZMod2 X).homologyπ q ≫ evaluation (chainCxZMod2 X) q ψ hψ) := by
      rw [← Category.assoc]
      exact (congrArg (fun f => f ≫ evaluation (chainCxZMod2 X) q ψ hψ)
        (RelativeCapBoundary.absolute_cap_class X p q (p + q) rfl φ hφ)).trans
          (Category.assoc _ _ _)
    _ = RelativeCapBoundary.absoluteCycleOf X p q (p + q) rfl φ hφ ≫
        ((chainCxZMod2 X).iCycles q ≫ ψ) := by rw [homologyπ_evaluation]
    _ = (chainCxZMod2 X).iCycles (p + q) ≫
        (absoluteChain X p q (p + q) rfl φ ≫ ψ) := by
      rw [← Category.assoc]
      exact (congrArg (fun f => f ≫ ψ)
        (RelativeCapBoundary.absolute_cycle_i X p q (p + q) rfl φ hφ)).trans
          (Category.assoc _ _ _)
    _ = (chainCxZMod2 X).iCycles (p + q) ≫ cochainCup p q φ ψ := by
      rw [RelativeCapDual.absolute_chain_dual]
    _ = _ := (homologyπ_evaluation (chainCxZMod2 X) (p + q) (cochainCup p q φ ψ)
      (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ)).symm

theorem cup_cap (X : TopCat.{0}) (p q : ℕ) (a : cohomologyZMod2 X p)
    (b : cohomologyZMod2 X q) (x : PoolCap.homology X (p + q)) :
    (kroneckerMap X (p + q)).hom (cupZMod2 a b) x =
      (kroneckerMap X q).hom b (PoolCap.cap X p q (p + q) rfl a x) := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective X p a
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective X q b
  have he := ConcreteCategory.congr_hom (cochain_duality X p q φ ψ hφ hψ) x
  rw [pool_comparison, pool_comparison] at he
  rw [cupZMod2_mk]
  exact he.symm


end
end Finsler.AbsoluteCapEvaluation
