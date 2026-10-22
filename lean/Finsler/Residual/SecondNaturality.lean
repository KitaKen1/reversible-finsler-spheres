module

public import Finsler.Loop.StrictLengthProductGeometricFactor
public import Finsler.Loop.LengthFilteredLoopRotation
public import Finsler.Loop.SplitPairHomologyKernel
public import Finsler.Topology.CrossProjectionZero
public import Finsler.Loop.StrictLengthProductCompatibility

/-! Enlarging the SECOND strict length cut commutes with the loop product, in the enlarged output
cut (Claude, UF prototype; the proof of `StrictLengthProductFirstNaturality` with the roles of the
two factors exchanged). -/
@[expose] public section

namespace Finsler.StrictLengthProductSecondNaturality
open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.StrictLengthEnergyBridge
open Finsler.StrictLengthLoopProduct Finsler.LengthProductNormalizationGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

variable {n : ℕ} (F : ReversibleMetric n) {p q q' ε : ℝ}
  (hp : 0 < p) (hq : 0 < q) (hq' : 0 < q') (hε : 0 < ε) (h : q ≤ q')

def pairInclusion : pairSpace F p q ⟶ pairSpace F p q' :=
  𝟙 (lengthSpace F p) ⊗ₘ LengthFilteredLoopRotation.cut F h

theorem left_square : pairInclusion F (p := p) h ≫ leftEvaluation F p q' =
    leftEvaluation F p q := by ext x : 1; rfl

theorem right_square : pairInclusion F (p := p) h ≫ rightEvaluation F p q' =
    rightEvaluation F p q := by ext x : 1; rfl

def common : Set (pairSpace F p q) :=
  StrictLengthProductJoinComparison.commonTube F p q hp hq hε ∩
    (pairInclusion F (p := p) h) ⁻¹'
      StrictLengthProductJoinComparison.commonTube F p q' hp hq' hε

theorem common_open : IsOpen (common F hp hq hq' hε h) :=
  (StrictLengthProductJoinComparison.commonTube_open F p q hp hq hε).inter
    ((StrictLengthProductJoinComparison.commonTube_open F p q' hp hq' hε).preimage
      (pairInclusion F (p := p) h).hom.continuous)

theorem diagonal_in_common (z : pairSpace F p q)
    (hz : leftEvaluation F p q z = rightEvaluation F p q z) :
    z ∈ common F hp hq hq' hε h := by
  constructor
  · exact StrictLengthProductGeometricFactor.diagonal_in_common F p q hp hq hε z hz
  · apply StrictLengthProductGeometricFactor.diagonal_in_common F p q' hp hq' hε
    exact hz

def toOld : TopCat.of (common F hp hq hq' hε h) ⟶
    TopCat.of (StrictLengthProductJoinComparison.commonTube F p q hp hq hε) :=
  restriction (𝟙 (pairSpace F p q)) _ _ (fun _ hz => hz.1)

def toNew : TopCat.of (common F hp hq hq' hε h) ⟶
    TopCat.of (StrictLengthProductJoinComparison.commonTube F p q' hp hq' hε) :=
  restriction (pairInclusion F (p := p) h) _ _ (fun _ hz => hz.2)

def thom (hn : 1 ≤ n) := DiagonalCutNaturality.operation hn
  (leftEvaluation F p q) (rightEvaluation F p q) (common F hp hq hq' hε h)
  (common_open F hp hq hq' hε h) (diagonal_in_common F hp hq hq' hε h)

theorem old_thom (hn : 1 ≤ n) (k : ℕ) :
    (StrictLengthProductGeometricFactor.commonThom F p q hp hq hε hn).homology k =
      (thom F hp hq hq' hε h hn).homology k ≫
        HomologicalComplex.homologyMap (push (toOld F hp hq hq' hε h)) k := by
  have he := DiagonalCutNaturality.homology_naturality hn (𝟙 (pairSpace F p q))
    (leftEvaluation F p q) (rightEvaluation F p q) (common F hp hq hq' hε h)
    (StrictLengthProductJoinComparison.commonTube F p q hp hq hε)
    (common_open F hp hq hq' hε h)
    (StrictLengthProductJoinComparison.commonTube_open F p q hp hq hε)
    (diagonal_in_common F hp hq hq' hε h)
    (StrictLengthProductGeometricFactor.diagonal_in_common F p q hp hq hε)
    (fun _ hz => hz.1) k
  change HomologicalComplex.homologyMap (push (𝟙 (pairSpace F p q))) (n + k) ≫ _ = _ at he
  have hid : push (𝟙 (pairSpace F p q)) = 𝟙 (chains (pairSpace F p q)) := by
    simp only [push, CategoryTheory.Functor.map_id]
  rw [hid, HomologicalComplex.homologyMap_id, Category.id_comp] at he
  exact he

theorem new_thom (hn : 1 ≤ n) (k : ℕ) :
    HomologicalComplex.homologyMap (push (pairInclusion F (p := p) h)) (n + k) ≫
      (StrictLengthProductGeometricFactor.commonThom F p q' hp hq' hε hn).homology k =
    (thom F hp hq hq' hε h hn).homology k ≫
      HomologicalComplex.homologyMap (push (toNew F hp hq hq' hε h)) k := by
  have he := DiagonalCutNaturality.homology_naturality hn (pairInclusion F (p := p) h)
    (leftEvaluation F p q') (rightEvaluation F p q') (common F hp hq hq' hε h)
    (StrictLengthProductJoinComparison.commonTube F p q' hp hq' hε)
    (common_open F hp hq hq' hε h)
    (StrictLengthProductJoinComparison.commonTube_open F p q' hp hq' hε)
    (diagonal_in_common F hp hq hq' hε h)
    (StrictLengthProductGeometricFactor.diagonal_in_common F p q' hp hq' hε)
    (fun _ hz => hz.2) k
  exact he

theorem join_square :
    toOld F hp hq hq' hε h ≫ StrictLengthProductJoinComparison.rawJoin F p q hp hq hε ≫
      LengthFilteredLoopRotation.cut F (by linarith : p + (q + ε) ≤ p + (q' + ε)) =
    toNew F hp hq hq' hε h ≫ StrictLengthProductJoinComparison.rawJoin F p q' hp hq' hε := by
  ext z : 1
  apply Subtype.ext
  change (StrictLengthProductJoinComparison.rawJoin F p q hp hq hε
    (toOld F hp hq hq' hε h z)).val =
    (StrictLengthProductJoinComparison.rawJoin F p q' hp hq' hε
      (toNew F hp hq hq' hε h z)).val
  rw [StrictLengthProductJoinComparison.rawJoin_formula,
    StrictLengthProductJoinComparison.rawJoin_formula]
  rfl

include hp hq hq'

theorem operation_naturality (hn : 1 ≤ n) (k : ℕ) :
    HomologicalComplex.homologyMap (push (pairInclusion F (p := p) h)) (n + k) ≫
      (StrictLengthLoopProduct.operation F hn (p := p) (q := q') hε).homology k =
    (StrictLengthLoopProduct.operation F hn (p := p) (q := q) hε).homology k ≫
      HomologicalComplex.homologyMap (push (LengthFilteredLoopRotation.cut F
        (by linarith : p + (q + ε) ≤ p + (q' + ε)))) k := by
  rw [StrictLengthProductGeometricFactor.operation F p q' hp hq' hε hn k,
    StrictLengthProductGeometricFactor.operation F p q hp hq hε hn k,
    StrictLengthProductGeometricFactor.geometricOperation,
    StrictLengthProductGeometricFactor.geometricOperation,
    DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology,
    ← Category.assoc, new_thom F hp hq hq' hε h hn k,
    old_thom F hp hq hq' hε h hn k]
  simp only [Category.assoc]
  congr 1
  rw [← HomologicalComplex.homologyMap_comp, ← push_comp,
    ← HomologicalComplex.homologyMap_comp, ← push_comp,
    ← HomologicalComplex.homologyMap_comp, ← push_comp, join_square]

theorem product_naturality (hn : 1 ≤ n) (i j k : ℕ) (hij : i + j = n + k)
    (x : PoolCap.homology (lengthSpace F p) i) (y : PoolCap.homology (lengthSpace F q) j) :
    StrictLengthLoopProduct.product F hn (q := q') hε i j k hij x
      ((PoolCap.push (LengthFilteredLoopRotation.cut F h) j).hom y) =
    (PoolCap.push (LengthFilteredLoopRotation.cut F
      (by linarith : p + (q + ε) ≤ p + (q' + ε))) k).hom
      (StrictLengthLoopProduct.product F hn hε i j k hij x y) := by
  rw [StrictLengthProductCompatibility.chain_apply, StrictLengthProductCompatibility.chain_apply]
  have hc := CrossProjectionZero.cross_naturality_apply (𝟙 (lengthSpace F p))
    (LengthFilteredLoopRotation.cut F h) i j (n + k) hij x y
  have hid : (PoolCap.push (𝟙 (lengthSpace F p)) i).hom x = x :=
    SplitPairHomologyKernel.push_id_apply _ _ _
  rw [hid] at hc
  rw [hc]
  exact ConcreteCategory.congr_hom (operation_naturality F hp hq hq' hε h hn k)
    (FilteredBilinearLoopProduct.cross (lengthSpace F p) (lengthSpace F q) i j (n + k) hij x y)

end
end Finsler.StrictLengthProductSecondNaturality
