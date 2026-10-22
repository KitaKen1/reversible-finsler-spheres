module

public import Finsler.Loop.CupCapOrder
public import Finsler.Topology.PartialDoubleCap

/-! Exact flat cup cap versus the project's genuine nested two-cap
formula, including the source degree transport and no closure premise. -/

@[expose] public section
namespace Finsler.CapCupNested

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem transport (X : TopCat.{0}) (d q i j : ℕ) (hi : d + q = i) (hj : d + q = j)
    (hij : i = j) (ξ : singularCochainGroup (ZMod 2) X d) :
    eqToHom (congrArg (chains X).X hij) ≫ absoluteChain X d q j hj ξ = absoluteChain X d q i hi ξ := by
  cases hij
  exact Category.id_comp _

theorem flat_nested (X : TopCat.{0}) (a b q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X a) (ψ : singularCochainGroup (ZMod 2) X b) :
    absoluteChain X (a + b) q ((a + b) + q) rfl (cochainCup a b φ ψ) =
      eqToHom (congrArg (chains X).X (Nat.add_assoc a b q)) ≫ PartialDoubleCap.cap X a b q φ ψ := by
  have ha := CupCapOrder.cap_cup X a b (a + b) q rfl φ ψ
  rw [CupOne.cup_comparison] at ha
  rw [PartialDoubleCap.cap, ← Category.assoc,
    transport X a (b + q) ((a + b) + q) (a + (b + q)) (by omega) rfl (Nat.add_assoc a b q)]
  exact ha.symm

end
end Finsler.CapCupNested
