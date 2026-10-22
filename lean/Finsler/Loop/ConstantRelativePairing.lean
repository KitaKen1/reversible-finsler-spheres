module

public import Finsler.Loop.ConstantRelativeLift
public import Finsler.Topology.RelativeKronecker
public import Finsler.Topology.SupportedCapNaturality

/-! Evaluate the canonical high-degree relative lift on actual relative
homology classes, obtained by the ORIGINAL fullPair quotient map.
The actual relative Kronecker pairing equals the raw absolute pairing. -/

@[expose] public section
namespace Finsler.ConstantRelativePairing
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def homologyToRelative (n k : ℕ) :
    homologyZMod2 (Loops n) k →ₗ[ZMod 2]
      ((fullPair n).singularHomology coeff k : ModuleCat.{0} (ZMod 2)) :=
  ((fullPair n).singularHomologyπ coeff k).hom.comp
    (HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k).hom

theorem homology_roundtrip (n k : ℕ) (z : homologyZMod2 (Loops n) k) :
    (HomologicalComplex.homologyMap (push (FullLoopModel.forget n)) k).hom
      ((HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k).hom z) = z := by
  change (HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k ≫
    HomologicalComplex.homologyMap (push (FullLoopModel.forget n)) k).hom z = z
  rw [← HomologicalComplex.homologyMap_comp, ← push_comp, FullLoopModel.include_forget]
  have hid : push (𝟙 (Loops n)) = 𝟙 (chains (Loops n)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map (TopCat.toSSet.map (𝟙 (Loops n))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, HomologicalComplex.homologyMap_id]
  rfl

theorem pairing (n k : ℕ) (hk : n + 1 < k) (a : cohomologyZMod2 (Loops n) k)
    (z : homologyZMod2 (Loops n) k) :
    RelativeKronecker.comparison (fullPair n) k (ConstantRelativeLift.lift n k hk a)
      (homologyToRelative n k z) = (kroneckerMap (Loops n) k).hom a z := by
  have h := congrArg
    (fun f : Module.Dual (ZMod 2) (homologyZMod2 (fullPair n).fst k) =>
      f ((HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k).hom z))
    (RelativeKronecker.fromRelative_comparison (fullPair n) k (ConstantRelativeLift.lift n k hk a))
  change RelativeKronecker.comparison (fullPair n) k (ConstantRelativeLift.lift n k hk a)
    (homologyToRelative n k z) = (kroneckerMap (fullPair n).fst k).hom
      ((relativeToPool (fullPair n) k).hom (ConstantRelativeLift.lift n k hk a))
        ((HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k).hom z) at h
  rw [ConstantRelativeLift.lift_spec, FullLoopModel.cohomology_apply, kroneckerMap_naturality_apply] at h
  change RelativeKronecker.comparison (fullPair n) k (ConstantRelativeLift.lift n k hk a)
    (homologyToRelative n k z) = (kroneckerMap (Loops n) k).hom a
      ((HomologicalComplex.homologyMap (push (FullLoopModel.forget n)) k).hom
        ((HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k).hom z)) at h
  rw [homology_roundtrip] at h
  exact h

end
end Finsler.ConstantRelativePairing
