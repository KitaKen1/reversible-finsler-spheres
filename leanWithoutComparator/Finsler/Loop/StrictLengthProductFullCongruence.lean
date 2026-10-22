module

public import Finsler.Loop.StrictLengthProductFullNaturality
public import Finsler.Loop.StrictLengthHomologyStabilization

/-! Equality of the FULL input homology classes, at arbitrary positive
length bounds and arbitrary positive slacks, implies equality of the FULL
images of the EXISTING filtered products. Compact stabilization supplies
actual common finite input cuts; no global product is postulated. -/
@[expose] public section
namespace Finsler.StrictLengthProductFullCongruence
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem product_full_congr {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n)
    {p q p' q' ε ε' : ℝ} (hp : 0 < p) (hq : 0 < q) (hp' : 0 < p') (hq' : 0 < q')
    (hε : 0 < ε) (hε' : 0 < ε') (i j k : ℕ) (hij : i + j = n + k)
    (x : homologyZMod2 (lengthSpace F p) i) (x' : homologyZMod2 (lengthSpace F p') i)
    (y : homologyZMod2 (lengthSpace F q) j) (y' : homologyZMod2 (lengthSpace F q') j)
    (hx : (homologyPushZMod2 (LengthFilteredLoopRotation.full F p) i).hom x =
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F p') i).hom x')
    (hy : (homologyPushZMod2 (LengthFilteredLoopRotation.full F q) j).hom y =
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F q') j).hom y') :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (p + (q + ε))) k).hom
      (StrictLengthLoopProduct.product F hn hε i j k hij x y) =
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (p' + (q' + ε'))) k).hom
      (StrictLengthLoopProduct.product F hn hε' i j k hij x' y') := by
  obtain ⟨B, hpB, hpB', hxB⟩ := StrictLengthHomologyStabilization.exists_equal F i x x' hx
  obtain ⟨C, hqC, hqC', hyC⟩ := StrictLengthHomologyStabilization.exists_equal F j y y' hy
  have hB : 0 < B := hp.trans_le hpB
  have hC : 0 < C := hq.trans_le hqC
  have ha := StrictLengthProductFullNaturality.product_naturality F hp hB hq hC hε
    (by norm_num : (0 : ℝ) < 1) hpB hqC hn i j k hij x y
  have hb := StrictLengthProductFullNaturality.product_naturality F hp' hB hq' hC hε'
    (by norm_num : (0 : ℝ) < 1) hpB' hqC' hn i j k hij x' y'
  change (PoolCap.push (LengthFilteredLoopRotation.cut F hpB) i).hom x =
    (PoolCap.push (LengthFilteredLoopRotation.cut F hpB') i).hom x' at hxB
  change (PoolCap.push (LengthFilteredLoopRotation.cut F hqC) j).hom y =
    (PoolCap.push (LengthFilteredLoopRotation.cut F hqC') j).hom y' at hyC
  rw [hxB, hyC] at ha
  exact ha.symm.trans hb

end
end Finsler.StrictLengthProductFullCongruence
