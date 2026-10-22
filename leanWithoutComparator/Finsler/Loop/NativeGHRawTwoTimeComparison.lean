module

public import Finsler.Loop.NativeGHRawIntervalComparison
public import Finsler.Loop.NativeGHProductRawAlignment
public import Finsler.Loop.NativeGHOriginalTimeStages

/-! Full explicit source coboundary from the ORIGINAL normalized
self-cut/near-interval expression to TWO genuine time insertions tested
against the SAME Stage108 raw interleaved cochain. Both branches and all
source terms are retained. Two-time insertion versus canonical square
shuffle, and complete nested PrismSelfCut identification, remain open. -/
@[expose] public section
namespace Finsler.NativeGHRawTwoTimeComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests
open Finsler.NativeGHOuterTimeComparison (squareDegree primitive_degree input_degree)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

theorem interval_pre (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (T : singularCochainGroup (ZMod 2) (RightIntervalCochain.space X) (j + 1)) :
    CochainDegreeTransport.pre X h (TimeTriangleSplit.interval X j ≫ T) =
      TimeTriangleSplit.interval X i ≫ CochainDegreeTransport.pre (RightIntervalCochain.space X)
        (congrArg (fun n => n + 1) h) T := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k) (side : Bool)

def parameterPrimitive := CochainDegreeTransport.pre (base m) (primitive_degree m hm a b k side)
  (NativeGHRawIntervalComparison.primitive m hm F a b k E side)
def parameterAfter := CochainDegreeTransport.pre (base m) (input_degree m hm a b k side)
  (NativeGHRawIntervalComparison.rawInterval m hm F a b k E side)

theorem parameter_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (base m) (squareDegree m a b k + 1)
      (parameterPrimitive m hm F a b k E side) =
      NativeGHOuterTimeComparison.parameterBefore m hm F a b k E side - parameterAfter m hm F a b k E side := by
  unfold parameterPrimitive
  rw [NativeRawOriginalScalarReduction.pre_boundary, NativeGHRawIntervalComparison.boundary m hm F a b k E side hE,
    NativeRawOriginalScalarReduction.pre_sub]
  rfl

theorem parameter_endpoint (t : IntervalSobolev.ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SelfCutThomCocycle.atTime (m + 1) t) (squareDegree m a b k + 1)
      (parameterPrimitive m hm F a b k E side) = 0 :=
  NativeSequentialGHGlobalComparison.pullback_pre_zero _ _ _
    (NativeGHRawIntervalComparison.primitive_endpoint m hm F a b k E side t ht)

def primitive := SelfCutPrismCoboundary.primitive (m + 1) (squareDegree m a b k)
  (parameterPrimitive m hm F a b k E side)

def twoTimeRaw : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) := SelfCutTimePrism.prism (m + 1) (squareDegree m a b k + 1) ≫
  parameterAfter m hm F a b k E side

def twoTimeStage108 : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) := SelfCutTimePrism.prism (m + 1) (squareDegree m a b k + 1) ≫
  TimeTriangleSplit.interval (base m) (squareDegree m a b k + 2) ≫
  cochainPullback (rawSource m) (squareDegree m a b k + 3)
    (NativeGHProductRawAlignment.stage108 m hm F a b k E side)

theorem twoTime_original : twoTimeRaw m hm F a b k E side = twoTimeStage108 m hm F a b k E side := by
  unfold twoTimeRaw parameterAfter NativeGHRawIntervalComparison.rawInterval
  rw [interval_pre, NativeGHProductRawAlignment.original_stage108]
  rfl

theorem full_comparison (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E side) =
      NativeGHOriginalTimeStages.originalSequential m hm F a b k E side - twoTimeStage108 m hm F a b k E side := by
  rw [NativeGHOriginalTimeStages.sequential_original, ← twoTime_original]
  exact SelfCutPrismCoboundary.comparison (m + 1) (squareDegree m a b k)
    (parameterPrimitive m hm F a b k E side) (NativeGHOuterTimeComparison.parameterBefore m hm F a b k E side)
    (parameterAfter m hm F a b k E side) (parameter_boundary m hm F a b k E side hE)
    (parameter_endpoint m hm F a b k E side 0 (Or.inl rfl))
    (parameter_endpoint m hm F a b k E side 1 (Or.inr rfl))

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ NativeGHOriginalTimeStages.originalSequential m hm F a b k E side =
      c ≫ twoTimeStage108 m hm F a b k E side := by
  have h := congrArg (fun f => c ≫ f) (full_comparison m hm F a b k E side hE)
  change c ≫ ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
    primitive m hm F a b k E side) = _ at h
  rw [← Category.assoc c, hc, zero_comp, Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h.symm

end
end Finsler.NativeGHRawTwoTimeComparison
