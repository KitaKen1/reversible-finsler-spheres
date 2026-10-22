module

public import Finsler.Topology.OriginalSecondHalfFamily
public import Finsler.Topology.ProductSimplexProjection
public import Finsler.Topology.BoundedSecondFactorDescent
public import Finsler.Topology.PartialDoubleCapDomainFiltered

/-! Actual second-factor diagrams for a genuine bounded product map into
the original first-corrected second-half cut domain. The native cut and
retained-loop factors are constructed in their actual subspaces by the
zero-vertex section. No bounded second-factor map is assumed. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfBoundedFactors

open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.Geometry
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.CochainComparison
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

def retainedCut (r : ℝ) (hr : r ≤ 1) :
    TopCat.of (OriginalSecondHalfFamily.domain α β K hK r) ⟶ TopCat.of (SphereLoop n) :=
  OriginalSecondHalfFamily.cutMap α β K hK r ≫ TopCat.ofHom (SupportedSelfCut.retained n hr)

def bounded (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    Set (TopCat.of (OriginalSecondHalfFamily.domain α β K hK r)) :=
  PartialDoubleCapDomainFiltered.boundedDomain (TopCat.of (P × (ClosedInterval × Q)))
    (TopCat.of (SphereLoop n)) (OriginalSecondHalfFamily.domain α β K hK r)
    (retainedCut α β K hK r hr) {γ | SobolevLength.length F γ < A}

def domainProjection (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    TopCat.of (bounded α β K hK r hr F A) ⟶ TopCat.of (OriginalSecondHalfFamily.domain α β K hK r) :=
  SupportedCap.subspaceMap _ _

def source (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    TopCat.of (bounded α β K hK r hr F A) ⟶ TopCat.of (P × (ClosedInterval × Q)) :=
  domainProjection α β K hK r hr F A ≫
    SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
      (OriginalSecondHalfFamily.domain α β K hK r)

def retained (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    TopCat.of (bounded α β K hK r hr F A) ⟶
      TopCat.of ({γ | SobolevLength.length F γ < A} : Set (SphereLoop n)) :=
  PartialDoubleCapDomainFiltered.retained (TopCat.of (P × (ClosedInterval × Q)))
    (TopCat.of (SphereLoop n)) (OriginalSecondHalfFamily.domain α β K hK r)
    (retainedCut α β K hK r hr) {γ | SobolevLength.length F γ < A}

def nativeProjection (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    TopCat.of (bounded α β K hK r hr F A) ⟶
      TopCat.of (OriginalSecondHalfFamily.nativeDomain β r) :=
  domainProjection α β K hK r hr F A ≫
    TopCat.ofHom (OriginalSecondHalfFamily.nativeProjection α β K hK (r := r))

def evaluation (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    TopCat.of (bounded α β K hK r hr F A) ⟶ DiagonalCohomology.product n :=
  domainProjection α β K hK r hr F A ≫ OriginalSecondHalfFamily.cutMap α β K hK r ≫
    SupportedCap.subspaceMap (parameters n) (neighborhood n r) ≫ selfEvaluation n

theorem native_source (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    nativeProjection α β K hK r hr F A ≫
      SupportedCap.subspaceMap (TopCat.of (ClosedInterval × Q))
        (OriginalSecondHalfFamily.nativeDomain β r) =
      source α β K hK r hr F A ≫
        CartesianMonoidalCategory.snd (TopCat.of P) (TopCat.of (ClosedInterval × Q)) := by
  unfold nativeProjection source
  rw [Category.assoc, OriginalSecondHalfFamily.native_projection_source]
  rfl

theorem retained_inclusion (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    retained α β K hK r hr F A ≫ SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
      {γ | SobolevLength.length F γ < A} =
      nativeProjection α β K hK r hr F A ≫ OriginalSecondHalfFamily.nativeCut β r ≫
        TopCat.ofHom (SupportedSelfCut.retained n hr) := by
  have he : retained α β K hK r hr F A ≫ SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
      {γ | SobolevLength.length F γ < A} =
      domainProjection α β K hK r hr F A ≫ retainedCut α β K hK r hr := by
    ext z : 1
    rfl
  rw [he]
  unfold retainedCut nativeProjection
  simp only [Category.assoc, OriginalSecondHalfFamily.retained_factor]

theorem evaluation_native (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    evaluation α β K hK r hr F A = nativeProjection α β K hK r hr F A ≫
      OriginalSecondHalfFamily.nativeCut β r ≫
        SupportedCap.subspaceMap (parameters n) (neighborhood n r) ≫ selfEvaluation n := by
  unfold evaluation nativeProjection
  simp only [Category.assoc, OriginalSecondHalfFamily.cut_evaluation_factor]

variable (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) (j k : ℕ)
  (σ : TopCat.toSSet.obj (TopCat.of P) _⦋j⦌)
  (τ : TopCat.toSSet.obj (TopCat.of (ClosedInterval × Q)) _⦋k⦌)
  (G : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ TopCat.toSSet.obj (TopCat.of (bounded α β K hK r hr F A)))
  (hG : G ≫ TopCat.toSSet.map (source α β K hK r hr F A) =
    ProductSimplexCarrier.model (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ)

include hG

theorem native_source_on_product : G ≫ TopCat.toSSet.map (nativeProjection α β K hK r hr F A) ≫
    TopCat.toSSet.map (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × Q))
      (OriginalSecondHalfFamily.nativeDomain β r)) =
      CartesianMonoidalCategory.snd (Δ[j] : SSet.{0}) Δ[k] ≫ SSet.yonedaEquiv.symm τ := by
  rw [← Functor.map_comp, native_source, Functor.map_comp, ← Category.assoc, hG,
    ProductSimplexProjection.model_snd]

theorem native_second : G ≫ TopCat.toSSet.map (nativeProjection α β K hK r hr F A) =
    CartesianMonoidalCategory.snd (Δ[j] : SSet.{0}) Δ[k] ≫
      (BoundedSecondFactorDescent.zeroSection j k ≫ G ≫
        TopCat.toSSet.map (nativeProjection α β K hK r hr F A)) := by
  haveI : Mono (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × Q))
      (OriginalSecondHalfFamily.nativeDomain β r)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  apply BoundedSecondFactorDescent.factor j k _
    (TopCat.toSSet.map (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × Q))
      (OriginalSecondHalfFamily.nativeDomain β r))) (SSet.yonedaEquiv.symm τ)
  simpa only [Category.assoc] using native_source_on_product α β K hK r hr F A j k σ τ G hG

theorem evaluation_second : G ≫ TopCat.toSSet.map (evaluation α β K hK r hr F A) =
    CartesianMonoidalCategory.snd (Δ[j] : SSet.{0}) Δ[k] ≫
      (BoundedSecondFactorDescent.zeroSection j k ≫ G ≫
        TopCat.toSSet.map (nativeProjection α β K hK r hr F A) ≫
        TopCat.toSSet.map (OriginalSecondHalfFamily.nativeCut β r ≫
          SupportedCap.subspaceMap (parameters n) (neighborhood n r) ≫ selfEvaluation n)) := by
  have he := congrArg (fun H => H ≫ TopCat.toSSet.map (OriginalSecondHalfFamily.nativeCut β r ≫
    SupportedCap.subspaceMap (parameters n) (neighborhood n r) ≫ selfEvaluation n))
    (native_second α β K hK r hr F A j k σ τ G hG)
  simpa only [evaluation_native, Functor.map_comp, Category.assoc] using he

theorem retained_second : G ≫ TopCat.toSSet.map (retained α β K hK r hr F A) =
    CartesianMonoidalCategory.snd (Δ[j] : SSet.{0}) Δ[k] ≫
      (BoundedSecondFactorDescent.zeroSection j k ≫ G ≫
        TopCat.toSSet.map (retained α β K hK r hr F A)) := by
  let g := BoundedSecondFactorDescent.zeroSection j k ≫ G ≫
    TopCat.toSSet.map (nativeProjection α β K hK r hr F A) ≫
    TopCat.toSSet.map (OriginalSecondHalfFamily.nativeCut β r ≫
      TopCat.ofHom (SupportedSelfCut.retained n hr))
  apply BoundedSecondFactorDescent.bounded_factor (TopCat.of (SphereLoop n))
    {γ | SobolevLength.length F γ < A} j k _ g
  have he := congrArg (fun H => H ≫ TopCat.toSSet.map (OriginalSecondHalfFamily.nativeCut β r ≫
    TopCat.ofHom (SupportedSelfCut.retained n hr)))
    (native_second α β K hK r hr F A j k σ τ G hG)
  dsimp only [g]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [congrArg (fun H => TopCat.toSSet.map H) (retained_inclusion α β K hK r hr F A)]
  simpa only [Category.assoc, ← Functor.map_comp] using he

end
end Finsler.OriginalSecondHalfBoundedFactors
