module

public import Finsler.Topology.OriginalSecondHalfShuffleZero
public import Finsler.Topology.OriginalSecondHalfExtensions
public import Finsler.Topology.ThreeCapFunctoriality

/-! Any actual bounded lift of the original zero-extended three-cap is
the canonical cap on the genuine bounded product map, by chain monicity.
Its actual retained output is zero after normalization under the degree
bound, in that same retained-length target. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfCapUniqueness

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.ThreeCapBlockVanishing Finsler.OriginalSecondHalfBoundedFactors
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

theorem source_mono (q : ℕ) : Mono ((push (source α β K hK r hr F A)).f q) := by
  haveI : Mono ((push (domainProjection α β K hK r hr F A)).f q) :=
    SupportedCap.subspacePush_mono (TopCat.of (OriginalSecondHalfFamily.domain α β K hK r))
      (bounded α β K hK r hr F A) q
  haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
      (OriginalSecondHalfFamily.domain α β K hK r))).f q) :=
    SupportedCap.subspacePush_mono (TopCat.of (P × (ClosedInterval × Q)))
      (OriginalSecondHalfFamily.domain α β K hK r) q
  rw [OriginalSecondHalfBoundedFactors.source, push_comp, HomologicalComplex.comp_f]
  infer_instance

variable (j k : ℕ)
  (σ : TopCat.toSSet.obj (TopCat.of P) _⦋j⦌)
  (τ : TopCat.toSSet.obj (TopCat.of (ClosedInterval × Q)) _⦋k⦌)
  (G : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ TopCat.toSSet.obj (TopCat.of (bounded α β K hK r hr F A)))
  (hG : G ≫ TopCat.toSSet.map (source α β K hK r hr F A) =
    ProductSimplexCarrier.model (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ)

include hG

theorem lift_eq (a b c d : ℕ)
    (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
    (φ : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) b)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) c)
    (W : (((Δ[j] : SSet.{0}) ⊗ Δ[k]).chainComplex coeff).X (a + b + c + d) ⟶
      (chains (TopCat.of (bounded α β K hK r hr F A))).X d)
    (hW : W ≫ (push (source α β K hK r hr F A)).f d =
      (SSet.chainComplexMap
        (ProductSimplexCarrier.model (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ) coeff).f
        (a + b + c + d) ≫ threeCap (TopCat.of (P × (ClosedInterval × Q))) a b c d J φ ψ) :
    W = (SSet.chainComplexMap G coeff).f (a + b + c + d) ≫
      threeCap (TopCat.of (bounded α β K hK r hr F A)) a b c d
        (cochainPullback (source α β K hK r hr F A) a J)
        (cochainPullback (source α β K hK r hr F A) b φ)
        (cochainPullback (source α β K hK r hr F A) c ψ) := by
  haveI := source_mono α β K hK r hr F A d
  apply (cancel_mono ((push (source α β K hK r hr F A)).f d)).mp
  have hg : SSet.chainComplexMap G coeff ≫ push (source α β K hK r hr F A) =
      SSet.chainComplexMap
        (ProductSimplexCarrier.model (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ) coeff := by
    rw [push, ← Functor.map_comp, hG]
  rw [hW, Category.assoc, ThreeCapFunctoriality.natural, ← Category.assoc,
    ← HomologicalComplex.comp_f, hg]

theorem normalized_output_zero (a p q : ℕ) (htotal : j + k = a + n + p + q) (hdegree : a + p < j)
    (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (W : (((Δ[j] : SSet.{0}) ⊗ Δ[k]).chainComplex coeff).X (a + n + p + q) ⟶
      (chains (TopCat.of (bounded α β K hK r hr F A))).X q)
    (hW : W ≫ (push (source α β K hK r hr F A)).f q =
      (SSet.chainComplexMap
        (ProductSimplexCarrier.model (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ) coeff).f
        (a + n + p + q) ≫ threeCap (TopCat.of (P × (ClosedInterval × Q))) a n p q J
        (SupportedSelfCutAdequacy.extension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
          (AnnularSelfCut.cocycle n hn h))
        (SelfCutParameterFamily.testedExtension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
          (fun _ => r) (fun _ => hr) PUnit.unit p T)) :
    W ≫ (push (OriginalSecondHalfBoundedFactors.retained α β K hK r hr F A)).f q ≫
      (SingularNormalization.projector
        (TopCat.of ({γ | SobolevLength.length F γ < A} : Set (SphereLoop n)))).f q = 0 := by
  rw [lift_eq α β K hK r hr F A j k σ τ G hG a n p q J _ _ W hW,
    OriginalSecondHalfExtensions.thom_extension_pullback,
    OriginalSecondHalfExtensions.tested_extension_pullback]
  have hz := OriginalSecondHalfShuffleZero.component_zero α β K hK r hr F A
    j k σ τ G hG a p q htotal hdegree hn h J T
  unfold OriginalSecondHalfShuffleZero.normalizedComponent at hz
  rw [OriginalSecondHalfShuffleZero.annular_pullback] at hz
  simpa only [Category.assoc] using hz

end
end Finsler.OriginalSecondHalfCapUniqueness
