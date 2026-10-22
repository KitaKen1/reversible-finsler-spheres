module

public import Finsler.Loop.NativeGHOuterTimeComparison
public import Finsler.Loop.SupportedCapCochainCongruence

/-! The sequential side really uses the ORIGINAL NormalizedSelfCut
operation and ORIGINAL first time prism, with the canonical second
interval and the actual interleaved raw GH test. Identity-pullback
and every source-degree cast are removed by proved equalities.
This still does not identify the complete nested PrismSelfCut composite
or the two-interval chain with the canonical square shuffle. -/
@[expose] public section
namespace Finsler.NativeGHOriginalTimeStages
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

theorem identity_thom (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    NativeOrderedDoubleCutSupported.thom (𝟙 (SelfCutThomCocycle.parameters n)) hn hρ =
      NormalizedSelfCut.cocycle n hn hρ :=
  congrArg (fun f => (f.f n).hom (NormalizedSelfCut.cocycle n hn hρ))
    (singularCochainComplexZMod2.map_id (Opposite.op (SelfCutThomCocycle.parameters n)))

theorem identity_operation (n : ℕ) (hn : 1 ≤ n) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ) :
    (NativeOrderedDoubleCutSupported.operation (𝟙 (SelfCutThomCocycle.parameters n)) hn hρ hρr).component q =
      (NormalizedSelfCut.operation n hn hρ hρr).component q :=
  SupportedCapCochainCongruence.cut_eq (SelfCutThomCocycle.parameters n)
    (SupportedSelfCut.exterior n ρ) (SupportedSelfCut.neighborhood n r)
    (SupportedSelfCut.exterior_open n ρ) (SupportedSelfCut.neighborhood_open n r)
    (SupportedSelfCut.cover n hρr) n q (n + q) rfl
    (NativeOrderedDoubleCutSupported.thom (𝟙 (SelfCutThomCocycle.parameters n)) hn hρ)
    (NormalizedSelfCut.cocycle n hn hρ)
    (NativeOrderedDoubleCutSupported.thom_supported (𝟙 (SelfCutThomCocycle.parameters n)) hn hρ)
    (NormalizedSelfCut.cocycle_supported n hn hρ) (identity_thom n hn hρ)

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k) (side : Bool)

theorem before_normalized : CochainDegreeTransport.pre (base m)
    (show m + index m a b k side + 1 = (m + 1) + index m a b k side by omega)
      ((NormalizedSelfCut.operation (m + 1) (by omega)
        (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
        (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)).component (index m a b k side) ≫
        TimeTriangleSplit.interval (TopCat.of (near m hm F)) (index m a b k side) ≫ test m hm F a b k E side) =
      NativeGHIntervalOrder.before m hm F a b k E side := by
  have h := NativeGHIntervalOrder.before_original m hm F a b k E side
  rw [identity_operation] at h
  exact h

include hm in
theorem original_degree : NativeGHOuterTimeComparison.squareDegree m a b k + 2 =
    (m + 1) + index m a b k side := by
  have h := NativeGHOuterTimeComparison.input_degree m hm a b k side
  omega

def originalSequential : singularCochainGroup (ZMod 2) (Loops (m + 1))
    (NativeGHOuterTimeComparison.squareDegree m a b k + 1) :=
  SelfCutTimePrism.prism (m + 1) (NativeGHOuterTimeComparison.squareDegree m a b k + 1) ≫
    CochainDegreeTransport.pre (base m) (original_degree m hm a b k side)
      ((NormalizedSelfCut.operation (m + 1) (by omega)
        (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
        (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)).component (index m a b k side) ≫
        TimeTriangleSplit.interval (TopCat.of (near m hm F)) (index m a b k side) ≫ test m hm F a b k E side)

theorem sequential_original : originalSequential m hm F a b k E side =
    NativeGHOuterTimeComparison.sequential m hm F a b k E side := by
  unfold NativeGHOuterTimeComparison.sequential NativeGHOuterTimeComparison.parameterBefore
  rw [← before_normalized m hm F a b k E side, NativeRawClockSupportedAlignment.pre_trans]
  rfl

theorem full_comparison (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (NativeGHOuterTimeComparison.squareDegree m a b k)
      (NativeGHOuterTimeComparison.primitive m hm F a b k E side) =
      originalSequential m hm F a b k E side - NativeGHOuterTimeComparison.moved m hm F a b k E side := by
  rw [sequential_original]
  exact NativeGHOuterTimeComparison.full_comparison m hm F a b k E side hE

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (NativeGHOuterTimeComparison.squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (NativeGHOuterTimeComparison.squareDegree m a b k + 1)
      (NativeGHOuterTimeComparison.squareDegree m a b k) = 0) :
    c ≫ originalSequential m hm F a b k E side = c ≫ NativeGHOuterTimeComparison.moved m hm F a b k E side := by
  rw [sequential_original]
  exact NativeGHOuterTimeComparison.cycle_values_eq m hm F a b k E side hE c hc

end
end Finsler.NativeGHOriginalTimeStages
