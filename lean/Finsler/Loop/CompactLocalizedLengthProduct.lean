module

public import Finsler.Loop.CompactNormalizedJoinCapComparison

/-! The genuine normalized compact-family localized join cap followed
by the actual raw join induces the specified separately strict-length
bilinear product, with an explicit strict tube margin. -/

@[expose] public section
namespace Finsler.CompactLocalizedLengthProduct

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.StrictLengthEnergyBridge Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (F : ReversibleMetric (m + 1))
  (p q : ℝ) (hα : ∀ x, SobolevLength.length F (α x) < p) (hβ : ∀ y, SobolevLength.length F (β y) < q)
  (hp : 0 < p) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε)

theorem radius_le_one : StrictLengthProductJoinComparison.radius F p q hp hq hε ≤ 1 :=
  (min_le_right _ _).trans (FilteredOriginalJoin.radius_spec F p q hp.le hq.le hε).2.1

variable {ρ : ℝ} (hρ : 0 < ρ) (R : ℝ) (hρR : 2 * ρ ≤ R)
  (hR : R < StrictLengthProductJoinComparison.radius F p q hp hq hε)

include hρR hR in
theorem rho_le_two : ρ ≤ 2 := by
  have he := radius_le_one F p q hp hq hε
  linarith

def toProductTube : TopCat.of (CompactNearJoinParameters.tube α β R) ⟶
    TopCat.of (StrictLengthProductFamilies.tube α β F p q hα hβ hp hq hε) :=
  CompactNormalizedJoinCapComparison.toNear α β R (StrictLengthProductJoinComparison.radius F p q hp hq hε) hR

def joinMap : TopCat.of (CompactNearJoinParameters.tube α β R) ⟶ lengthSpace F (p + (q + ε)) :=
  toProductTube α β F p q hα hβ hp hq hε R hR ≫ StrictLengthProductFamilies.rawJoin α β F p q hα hβ hp hq hε

theorem joinMap_formula (z : CompactNearJoinParameters.tube α β R) :
    (joinMap α β F p q hα hβ hp hq hε R hR z).val = JoinDirectionComparison.firstJoin JoinSplitHomotopy.half
      JoinSplitHomotopy.half.property.1 JoinSplitHomotopy.half.property.2 (α z.val.1) (β z.val.2) :=
  StrictLengthProductFamilies.rawJoin_formula α β F p q hα hβ hp hq hε _

def operation := (CompactJoinCapLocalization.unrefined α β (dim_pos m) hρ hρR).post
  (push (joinMap α β F p q hα hβ hp hq hε R hR))

theorem cap_homology (hm : 1 ≤ m) (k : ℕ) :
    (CompactJoinCapLocalization.unrefined α β (dim_pos m) hρ hρR).homology k ≫
      HomologicalComplex.homologyMap (push (toProductTube α β F p q hα hβ hp hq hε R hR)) k =
    (StrictLengthProductFamilies.thomOperation α β F p q hα hβ hp hq hε (dim_pos m)).homology k := by
  rw [← DegreeLoweringHomology.Map.post_homology]
  have he := (CompactNormalizedJoinCapComparison.existing_unrefined α β hρ R
    (StrictLengthProductJoinComparison.radius F p q hp hq hε) hρR hR k).trans
      (CompactNormalizedJoinCapComparison.specified_homology α β hρ R
        (StrictLengthProductJoinComparison.radius F p q hp hq hε) hρR hR hm
        (rho_le_two F p q hp hq hε R hρR hR) k)
  exact he

theorem operation_homology (hm : 1 ≤ m) (k : ℕ) :
    (operation α β F p q hα hβ hp hq hε hρ R hρR hR).homology k =
    ((StrictLengthLoopProduct.operation F (dim_pos m) hε).pre
      (push (StrictLengthProductFamilies.pairInput α β F p q hα hβ))).homology k := by
  rw [operation, DegreeLoweringHomology.Map.post_homology, joinMap, push_comp,
    HomologicalComplex.homologyMap_comp, ← Category.assoc, cap_homology α β F p q hα hβ hp hq hε hρ R hρR hR hm k,
    StrictLengthProductFamilies.operation_factor α β F p q hα hβ hp hq hε (dim_pos m) k,
    StrictLengthProductFamilies.geometricOperation, DegreeLoweringHomology.Map.post_homology]

theorem product_factor (hm : 1 ≤ m) (i j k : ℕ) (h : i + j = (m + 1) + k)
    (x : PoolCap.homology (TopCat.of P) i) (y : PoolCap.homology (TopCat.of Q) j) :
    StrictLengthLoopProduct.product F (dim_pos m) hε i j k h
      ((PoolCap.push (StrictLengthProductFamilies.leftInput α F p hα) i).hom x)
      ((PoolCap.push (StrictLengthProductFamilies.rightInput β F q hβ) j).hom y) =
    ((operation α β F p q hα hβ hp hq hε hρ R hρR hR).homology k).hom
      (FilteredBilinearLoopProduct.cross (TopCat.of P) (TopCat.of Q) i j ((m + 1) + k) h x y) := by
  rw [operation_homology α β F p q hα hβ hp hq hε hρ R hρR hR hm k,
    StrictLengthProductFamilies.operation_factor α β F p q hα hβ hp hq hε (dim_pos m) k]
  exact StrictLengthProductFamilies.product_factor α β F p q hα hβ hp hq hε (dim_pos m) i j k h x y

end
end Finsler.CompactLocalizedLengthProduct
