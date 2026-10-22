module

public import Finsler.Loop.ConstantRelativePairing
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Every actual relative output class, including degree n, pairs
with the original constant-relative quotient through its TRUE absolute
class. No high-degree isomorphism, chosen generator or rank is assumed. -/
@[expose] public section
namespace Finsler.ConstantRelativeOutputPairing
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.BorelLoop Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def absolute (n k : ℕ) (a : RelativeCup.cohomology (fullPair n) k) : cohomologyZMod2 (Loops n) k :=
  (FullLoopModel.cohomologyEquiv n k).symm ((relativeToPool (fullPair n) k).hom a)

theorem absolute_full (n k : ℕ) (a : RelativeCup.cohomology (fullPair n) k) :
    (FullLoopModel.cohomologyEquiv n k) (absolute n k a) = (relativeToPool (fullPair n) k).hom a :=
  (FullLoopModel.cohomologyEquiv n k).apply_symm_apply _

theorem pairing (n k : ℕ) (a : RelativeCup.cohomology (fullPair n) k) (z : homologyZMod2 (Loops n) k) :
    RelativeKronecker.comparison (fullPair n) k a (ConstantRelativePairing.homologyToRelative n k z) =
      (kroneckerMap (Loops n) k).hom (absolute n k a) z := by
  have he := congrArg
    (fun f : Module.Dual (ZMod 2) (homologyZMod2 (fullPair n).fst k) =>
      f ((HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k).hom z))
    (RelativeKronecker.fromRelative_comparison (fullPair n) k a)
  change RelativeKronecker.comparison (fullPair n) k a (ConstantRelativePairing.homologyToRelative n k z) =
    (kroneckerMap (fullPair n).fst k).hom ((relativeToPool (fullPair n) k).hom a)
      ((HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k).hom z) at he
  rw [← absolute_full n k a, FullLoopModel.cohomology_apply, kroneckerMap_naturality_apply] at he
  change RelativeKronecker.comparison (fullPair n) k a (ConstantRelativePairing.homologyToRelative n k z) =
    (kroneckerMap (Loops n) k).hom (absolute n k a)
      ((HomologicalComplex.homologyMap (push (FullLoopModel.forget n)) k).hom
        ((HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k).hom z)) at he
  rw [ConstantRelativePairing.homology_roundtrip] at he
  exact he

theorem relative_zero_iff (P : TopPair.{0}) (k : ℕ) (z : (P.singularHomology coeff k : ModuleCat.{0} (ZMod 2))) :
    z = 0 ↔ ∀ a : RelativeCup.cohomology P k, RelativeKronecker.comparison P k a z = 0 := by
  constructor
  · intro hz a
    rw [hz, map_zero]
  · intro hz
    apply Module.eval_apply_injective (ZMod 2)
    apply LinearMap.ext
    intro φ
    obtain ⟨a, rfl⟩ := (RelativeKronecker.comparison_bijective P k).surjective φ
    change RelativeKronecker.comparison P k a z = RelativeKronecker.comparison P k a 0
    rw [hz, map_zero]

end
end Finsler.ConstantRelativeOutputPairing
