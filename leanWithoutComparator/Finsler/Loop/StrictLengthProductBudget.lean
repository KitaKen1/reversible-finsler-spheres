module

public import Finsler.Loop.StrictLengthProductFamilies
public import Finsler.Loop.CompactInputLengthBudget

/-! The actual separately filtered product after self-cut has a genuine
continuous output inclusion into the coupled length<A-L+5epsilon target.
All real input thresholds are allowed; nonpositive branches remain zero. -/

@[expose] public section
namespace Finsler.StrictLengthProductBudget

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.StrictLengthEnergyBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {n : ℕ} (F : ReversibleMetric n) {a b A L ε : ℝ}
  (hab : a + b < A) (hε : 0 < ε)

theorem output_bound (hab : a + b < A) (hε : 0 < ε) : (a - L + 3 * ε) + (b + ε) < A - L + 5 * ε := by
  have h := CompactInputLengthBudget.output_margin (L := L) hab hε
  linarith

def outputInclusion (hab : a + b < A) (hε : 0 < ε) : lengthSpace F ((a - L + 3 * ε) + (b + ε)) ⟶ lengthSpace F (A - L + 5 * ε) :=
  TopCat.ofHom ⟨fun u => ⟨u.val, lt_trans u.property (output_bound (L := L) hab hε)⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem outputInclusion_source : outputInclusion F (L := L) hab hε ≫
    SupportedCap.subspaceMap (TopCat.of (IntervalSobolev.SphereLoop n)) (SelfCutOscillation.short F (A - L + 5 * ε)) =
    SupportedCap.subspaceMap (TopCat.of (IntervalSobolev.SphereLoop n))
      (SelfCutOscillation.short F ((a - L + 3 * ε) + (b + ε))) := rfl

def operation (hn : 1 ≤ n) :=
  (StrictLengthLoopProduct.operation F hn (p := a - L + 3 * ε) (q := b) hε).post
    (push (outputInclusion F hab hε))

def product (hn : 1 ≤ n) (i j k : ℕ) (h : i + j = n + k) :=
  (StrictLengthLoopProduct.product F hn (p := a - L + 3 * ε) (q := b) hε i j k h).compr₂
    (PoolCap.push (outputInclusion F hab hε) k).hom

theorem product_apply (hn : 1 ≤ n) (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (lengthSpace F (a - L + 3 * ε)) i) (y : PoolCap.homology (lengthSpace F b) j) :
    product F hab hε hn i j k h x y =
      (PoolCap.push (outputInclusion F hab hε) k).hom
        (StrictLengthLoopProduct.product F hn hε i j k h x y) := rfl

theorem chain_apply (hn : 1 ≤ n) (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (lengthSpace F (a - L + 3 * ε)) i) (y : PoolCap.homology (lengthSpace F b) j) :
    product F hab hε hn i j k h x y = ((operation F hab hε hn).homology k).hom
      (FilteredBilinearLoopProduct.cross (lengthSpace F (a - L + 3 * ε)) (lengthSpace F b) i j (n + k) h x y) := by
  rw [product_apply, StrictLengthProductCompatibility.chain_apply, operation, DegreeLoweringHomology.Map.post_homology]
  rfl

theorem nonpos_product (hn : 1 ≤ n) (hpos : ¬ (0 < a - L + 3 * ε ∧ 0 < b))
    (i j k : ℕ) (h : i + j = n + k) : product F (L := L) hab hε hn i j k h = 0 := by
  rw [product, StrictLengthLoopProduct.product_nonpos F hn hε hpos]
  ext x y
  simp

theorem nonpos_homology (hn : 1 ≤ n) (hpos : ¬ (0 < a - L + 3 * ε ∧ 0 < b)) (k : ℕ) :
    (operation F (L := L) hab hε hn).homology k = 0 := by
  rw [operation, DegreeLoweringHomology.Map.post_homology,
    StrictLengthProductCompatibility.nonpos_homology F hn hε hpos, zero_comp]

variable (hp : 0 < a - L + 3 * ε) (hb : 0 < b)

def rawJoin := StrictLengthProductJoinComparison.rawJoin F (a - L + 3 * ε) b hp hb hε ≫
  outputInclusion F hab hε

theorem rawJoin_formula (z : StrictLengthProductJoinComparison.commonTube F (a - L + 3 * ε) b hp hb hε) :
    (rawJoin F hab hε hp hb z).val = JoinDirectionComparison.firstJoin JoinSplitHomotopy.half
      JoinSplitHomotopy.half.property.1 JoinSplitHomotopy.half.property.2 z.val.1.val z.val.2.val :=
  StrictLengthProductJoinComparison.rawJoin_formula F (a - L + 3 * ε) b hp hb hε z

def geometricOperation (hn : 1 ≤ n) :=
  (StrictLengthProductGeometricFactor.commonThom F (a - L + 3 * ε) b hp hb hε hn).post
    (push (rawJoin F hab hε hp hb))

theorem geometric_homology (hn : 1 ≤ n) (k : ℕ) :
    (operation F hab hε hn).homology k = (geometricOperation F hab hε hp hb hn).homology k := by
  rw [operation, DegreeLoweringHomology.Map.post_homology,
    StrictLengthProductGeometricFactor.operation F (a - L + 3 * ε) b hp hb hε hn k,
    StrictLengthProductGeometricFactor.geometricOperation, DegreeLoweringHomology.Map.post_homology,
    geometricOperation, DegreeLoweringHomology.Map.post_homology, rawJoin,
    push_comp, HomologicalComplex.homologyMap_comp, Category.assoc]

theorem geometric_product (hn : 1 ≤ n) (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (lengthSpace F (a - L + 3 * ε)) i) (y : PoolCap.homology (lengthSpace F b) j) :
    product F hab hε hn i j k h x y = ((geometricOperation F hab hε hp hb hn).homology k).hom
      (FilteredBilinearLoopProduct.cross (lengthSpace F (a - L + 3 * ε)) (lengthSpace F b) i j (n + k) h x y) := by
  rw [chain_apply, geometric_homology F hab hε hp hb hn k]

end
end Finsler.StrictLengthProductBudget
