module

public import Finsler.Loop.CompactLocalizedLengthProduct
public import Finsler.Loop.CompactJoinCapNaturality
public import Finsler.Loop.FirstInputSelfCutBoundedSpace

/-! Use the actual individually bounded kept-output carrier for the first
input of the genuine length product. Its normalized localized join cap
is the real pullback of the existing proper-cut join cap, with strict
chain naturality before passing through the actual retractions. -/

@[expose] public section
namespace Finsler.BoundedKeptProductInputs

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.StrictLengthEnergyBridge Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (B : ℝ)

def kept : C(FirstInputSelfCutBoundedSpace.bounded α r hr F B, SphereLoop (m + 1)) :=
  (OriginalFirstHalfCutOutputJoinData.kept α r hr).comp (FirstInputSelfCutBoundedSpace.toCut α r hr F B).hom

theorem length_lt (z : FirstInputSelfCutBoundedSpace.bounded α r hr F B) :
    SobolevLength.length F (kept α r hr F B z) < B := z.property.choose_spec

theorem short_input : StrictLengthProductFamilies.leftInput (kept α r hr F B) F B (length_lt α r hr F B) =
    FirstInputSelfCutBoundedSpace.retained α r hr F B := rfl

def properPair := CompactJoinCapNaturality.input (FirstInputSelfCutBoundedSpace.toCut α r hr F B).hom (ContinuousMap.id Q)

def properTube (R : ℝ) := CompactJoinCapNaturality.nearMap (OriginalFirstHalfCutOutputJoinData.kept α r hr) β
  (FirstInputSelfCutBoundedSpace.toCut α r hr F B).hom (ContinuousMap.id Q) R

def properSmall (ρ : ℝ) := CompactJoinCapNaturality.smallMap (OriginalFirstHalfCutOutputJoinData.kept α r hr) β
  (FirstInputSelfCutBoundedSpace.toCut α r hr F B).hom (ContinuousMap.id Q) ρ

theorem cocycle (hn : 1 ≤ m + 1) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (properPair α r hr F B (Q := Q)) (m + 1)
      (CompactJoinCocycle.cocycle (OriginalFirstHalfCutOutputJoinData.kept α r hr) β hn hρ) =
    CompactJoinCocycle.cocycle (kept α r hr F B) β hn hρ :=
  CompactJoinCapNaturality.cocycle_pullback (OriginalFirstHalfCutOutputJoinData.kept α r hr) β
    (FirstInputSelfCutBoundedSpace.toCut α r hr F B).hom (ContinuousMap.id Q) hn hρ

theorem cap_component (hn : 1 ≤ m + 1) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : 2 * ρ ≤ R) (k : ℕ) :
    (properSmall α β r hr F B ρ).f ((m + 1) + k) ≫
      (CompactJoinCapLocalization.localized (OriginalFirstHalfCutOutputJoinData.kept α r hr) β hn hρ hρR).component k =
    (CompactJoinCapLocalization.localized (kept α r hr F B) β hn hρ hρR).component k ≫
      (push (properTube α β r hr F B R)).f k :=
  CompactJoinCapNaturality.component (OriginalFirstHalfCutOutputJoinData.kept α r hr) β
    (FirstInputSelfCutBoundedSpace.toCut α r hr F B).hom (ContinuousMap.id Q) hn hρ hρR k

theorem cap_homology (hn : 1 ≤ m + 1) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : 2 * ρ ≤ R) (k : ℕ) :
    HomologicalComplex.homologyMap (push (properPair α r hr F B (Q := Q))) ((m + 1) + k) ≫
      (CompactJoinCapLocalization.unrefined (OriginalFirstHalfCutOutputJoinData.kept α r hr) β hn hρ hρR).homology k =
    (CompactJoinCapLocalization.unrefined (kept α r hr F B) β hn hρ hρR).homology k ≫
      HomologicalComplex.homologyMap (push (properTube α β r hr F B R)) k :=
  CompactJoinCapNaturality.unrefined_homology (OriginalFirstHalfCutOutputJoinData.kept α r hr) β
    (FirstInputSelfCutBoundedSpace.toCut α r hr F B).hom (ContinuousMap.id Q) hn hρ hρR k

variable (b : ℝ) (hβ : ∀ y, SobolevLength.length F (β y) < b) (hB : 0 < B) (hb : 0 < b)
  {ε : ℝ} (hε : 0 < ε) {ρ : ℝ} (hρ : 0 < ρ) (R : ℝ) (hρR : 2 * ρ ≤ R)
  (hR : R < StrictLengthProductJoinComparison.radius F B b hB hb hε)

theorem product_factor (hm : 1 ≤ m) (i j k : ℕ) (h : i + j = (m + 1) + k)
    (x : PoolCap.homology (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) i)
    (y : PoolCap.homology (TopCat.of Q) j) :
    StrictLengthLoopProduct.product F (dim_pos m) hε i j k h
      ((PoolCap.push (FirstInputSelfCutBoundedSpace.retained α r hr F B) i).hom x)
      ((PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j).hom y) =
    ((CompactLocalizedLengthProduct.operation (kept α r hr F B) β F B b
      (length_lt α r hr F B) hβ hB hb hε hρ R hρR hR).homology k).hom
      (FilteredBilinearLoopProduct.cross (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B))
        (TopCat.of Q) i j ((m + 1) + k) h x y) := by
  rw [← short_input α r hr F B]
  exact CompactLocalizedLengthProduct.product_factor (kept α r hr F B) β F B b
    (length_lt α r hr F B) hβ hB hb hε hρ R hρR hR hm i j k h x y

end
end Finsler.BoundedKeptProductInputs
