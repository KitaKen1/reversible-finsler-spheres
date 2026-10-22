module

public import Finsler.Loop.StrictLengthProductFamilies
public import Finsler.Loop.StrictLengthProductCompatibility

/-! Include the actual genuine strict-length product in an arbitrary
larger strict input bound for canonical self-cut, using only its real
length margin. All real individual input bounds are allowed. -/

@[expose] public section
namespace Finsler.OriginalLengthProductBudget

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.StrictLengthEnergyBridge

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (F : ReversibleMetric n) {a b ε C : ℝ} (hbudget : a + (b + ε) ≤ C)

def outputInclusion : lengthSpace F (a + (b + ε)) ⟶ lengthSpace F C :=
  TopCat.ofHom ⟨fun u => ⟨u.val, u.property.trans_le hbudget⟩, continuous_subtype_val.subtype_mk _⟩

theorem output_source : outputInclusion F hbudget ≫
    SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F C) =
    SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F (a + (b + ε))) := rfl

def operation (hn : 1 ≤ n) (hε : 0 < ε) :=
  (StrictLengthLoopProduct.operation F hn (p := a) (q := b) hε).post (push (outputInclusion F hbudget))

theorem nonpos_homology (hn : 1 ≤ n) (hε : 0 < ε) (hpos : ¬ (0 < a ∧ 0 < b)) (k : ℕ) :
    (operation F hbudget hn hε).homology k = 0 := by
  rw [operation, DegreeLoweringHomology.Map.post_homology,
    StrictLengthProductCompatibility.nonpos_homology F hn hε hpos, zero_comp]

end
end Finsler.OriginalLengthProductBudget
