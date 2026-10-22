module

public import Finsler.Loop.FamilyLengthProductSwap

/-! The actual global genuine strict-length product is symmetric on
the full homology of its product source, after the actual source swap.
No compact lifting or separate cross-product symmetry premise is needed. -/

@[expose] public section
namespace Finsler.StrictLengthProductSwap
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.StrictLengthEnergyBridge Finsler.FarNormalizedDiagonalCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

variable {n : ℕ} (F : ReversibleMetric n)

def family (a : ℝ) : C(SelfCutOscillation.short F a, SphereLoop n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem pair_identity (a b : ℝ) : StrictLengthProductFamilies.pairInput (family F a) (family F b)
    F a b (fun z => z.property) (fun z => z.property) = 𝟙 (StrictLengthLoopProduct.pairSpace F a b) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem homology {m : ℕ} (F : ReversibleMetric (m + 1)) (hm : 1 ≤ m)
    {a b ε C : ℝ} (hε : 0 < ε) (hbudget : a + (b + ε) ≤ C) (k : ℕ) :
    (OriginalLengthProductBudget.operation F hbudget (dim_pos m) hε).homology k =
    HomologicalComplex.homologyMap (push (SmallThomSwap.swap
      (P := SelfCutOscillation.short F a) (Q := SelfCutOscillation.short F b))) ((m + 1) + k) ≫
      (OriginalLengthProductBudget.operation F (by linarith : b + (a + ε) ≤ C) (dim_pos m) hε).homology k := by
  have he := FamilyLengthProductSwap.homology (family F a) (family F b) F a b
    (fun z => z.property) (fun z => z.property) hε C hbudget hm k
  have hid (X : TopCat.{0}) : push (𝟙 X) = 𝟙 (chains X) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map (TopCat.toSSet.map (𝟙 X)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [pair_identity, pair_identity, DegreeLoweringHomology.Map.pre_homology,
    DegreeLoweringHomology.Map.pre_homology] at he
  change HomologicalComplex.homologyMap (push (𝟙 (StrictLengthLoopProduct.pairSpace F a b))) ((m + 1) + k) ≫
      (OriginalLengthProductBudget.operation F hbudget (dim_pos m) hε).homology k =
    HomologicalComplex.homologyMap (push (SmallThomSwap.swap
      (P := SelfCutOscillation.short F a) (Q := SelfCutOscillation.short F b))) ((m + 1) + k) ≫
      HomologicalComplex.homologyMap (push (𝟙 (StrictLengthLoopProduct.pairSpace F b a))) ((m + 1) + k) ≫
      (OriginalLengthProductBudget.operation F (by linarith : b + (a + ε) ≤ C) (dim_pos m) hε).homology k at he
  rw [hid (StrictLengthLoopProduct.pairSpace F a b), hid (StrictLengthLoopProduct.pairSpace F b a),
    HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_id] at he
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom he x

end
end Finsler.StrictLengthProductSwap
