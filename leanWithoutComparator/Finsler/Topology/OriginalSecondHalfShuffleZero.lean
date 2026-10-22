module

public import Finsler.Topology.OriginalSecondHalfBoundedFactors
public import Finsler.Topology.ThreeCapBlockVanishing

/-! The original first-corrected second-half family, the specified
normalized annular Thom cochain and the actual tested-loop pullback.
Any genuine bounded product lift with the prescribed source identity
has zero normalized three-cap output under the original degree bound.
The remaining original small-chain/refinement and local zero-extension
comparison is not asserted by this component-level theorem. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfShuffleZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.OriginalSecondHalfBoundedFactors
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
  (K : Set (P × (ClosedInterval × Q)))
  (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
  (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ)

theorem annular_pullback (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (domainProjection α β K hK r hr F A ≫ OriginalSecondHalfFamily.cutMap α β K hK r) n
      (cochainPullback (SupportedCap.subspaceMap (parameters n) (neighborhood n r)) n
        (AnnularSelfCut.cocycle n hn h)) =
      cochainPullback (evaluation α β K hK r hr F A) n (AnnularThomCocycle.ambient n hn h) := by
  simp only [AnnularSelfCut.cocycle, ← SupportedCapNaturality.pullback_comp,
    OriginalSecondHalfBoundedFactors.evaluation, Category.assoc]

def normalizedComponent (a p q : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    (chains (TopCat.of (bounded α β K hK r hr F A))).X (a + n + p + q) ⟶
      (chains (TopCat.of ({γ | SobolevLength.length F γ < A} : Set (SphereLoop n)))).X q :=
  ThreeCapBlockVanishing.threeCap (TopCat.of (bounded α β K hK r hr F A)) a n p q
    (cochainPullback (source α β K hK r hr F A) a J)
    (cochainPullback (domainProjection α β K hK r hr F A ≫ OriginalSecondHalfFamily.cutMap α β K hK r) n
      (cochainPullback (SupportedCap.subspaceMap (parameters n) (neighborhood n r)) n
        (AnnularSelfCut.cocycle n hn h)))
    (cochainPullback (domainProjection α β K hK r hr F A ≫ OriginalSecondHalfFamily.cutMap α β K hK r) p
      (NormalizedSelfCut.testedCocycle n p hr T)) ≫
    (push (OriginalSecondHalfBoundedFactors.retained α β K hK r hr F A)).f q ≫
    (SingularNormalization.projector
      (TopCat.of ({γ | SobolevLength.length F γ < A} : Set (SphereLoop n)))).f q

variable (j k : ℕ)
  (σ : TopCat.toSSet.obj (TopCat.of P) _⦋j⦌)
  (τ : TopCat.toSSet.obj (TopCat.of (ClosedInterval × Q)) _⦋k⦌)
  (G : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ TopCat.toSSet.obj (TopCat.of (bounded α β K hK r hr F A)))
  (hG : G ≫ TopCat.toSSet.map (source α β K hK r hr F A) =
    ProductSimplexCarrier.model (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ)

include hG

theorem component_zero (a p q : ℕ) (htotal : j + k = a + n + p + q) (hdegree : a + p < j)
    (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    (SSet.chainComplexMap G coeff).f (a + n + p + q) ≫
      normalizedComponent α β K hK r hr F A a p q hn h J T = 0 := by
  unfold normalizedComponent
  rw [annular_pullback]
  let g := BoundedSecondFactorDescent.zeroSection j k ≫ G ≫
    TopCat.toSSet.map (nativeProjection α β K hK r hr F A) ≫
    TopCat.toSSet.map (OriginalSecondHalfFamily.nativeCut β r ≫
      SupportedCap.subspaceMap (parameters n) (neighborhood n r) ≫ selfEvaluation n)
  let f := BoundedSecondFactorDescent.zeroSection j k ≫ G ≫
    TopCat.toSSet.map (OriginalSecondHalfBoundedFactors.retained α β K hK r hr F A)
  exact ProductThreeCapVanishing.component_zero
    (TopCat.of (bounded α β K hK r hr F A)) (DiagonalCohomology.product n)
    (TopCat.of ({γ | SobolevLength.length F γ < A} : Set (SphereLoop n)))
    (evaluation α β K hK r hr F A) (OriginalSecondHalfBoundedFactors.retained α β K hK r hr F A)
    j k a n p q htotal hdegree _ (AnnularThomCocycle.raw n hn h) _ G g f
    (evaluation_second α β K hK r hr F A j k σ τ G hG)
    (retained_second α β K hK r hr F A j k σ τ G hG)

theorem shuffle_zero (a p q : ℕ) (htotal : j + k = a + n + p + q) (hdegree : a + p < j)
    (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    SSet.shuffleChain coeff j k (a + n + p + q) htotal ≫
      (SSet.chainComplexMap G coeff).f (a + n + p + q) ≫
        normalizedComponent α β K hK r hr F A a p q hn h J T = 0 := by
  rw [component_zero α β K hK r hr F A j k σ τ G hG a p q htotal hdegree hn h J T, comp_zero]

end
end Finsler.OriginalSecondHalfShuffleZero
