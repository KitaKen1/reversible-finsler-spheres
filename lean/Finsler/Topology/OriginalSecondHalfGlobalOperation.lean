module

public import Finsler.Topology.ThreeCapDomainFiltered
public import Finsler.Topology.PartialFamilyThreeCapBoundary
public import Finsler.Topology.OriginalSecondHalfUniformVanishing

/-! A global closed three-cap lift for the original first-corrected
second-half family. A common positive factor scale and the actual join
support supply its bounded carrier condition, including source pieces
outside the outer tube. The actual local boundary equation supplies
closedness. Global source/time comparison remains separate. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfGlobalOperation

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.ThreeCapBlockVanishing
open Finsler.OriginalSecondHalfBoundedFactors
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
  (K : Set (P × (ClosedInterval × Q)))
  (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
  (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n)
  (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)

def adequate {ι : Type*} (W : ι → Set (P × (ClosedInterval × Q))) (a p : ℕ)
    (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) (A : ℝ) : Prop :=
  ∀ q (σ : ((TopCat.of (P × (ClosedInterval × Q))).smallSingularSubcomplex W : SSet)
      _⦋a + n + p + q⦌),
    (TopCat.toSSet.obj (TopCat.of (P × (ClosedInterval × Q)))).ιChainComplex σ.val ≫
      threeCap (TopCat.of (P × (ClosedInterval × Q))) a n p q J
        (SupportedSelfCutAdequacy.extension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
          (AnnularSelfCut.cocycle n hn h))
        (SelfCutParameterFamily.testedExtension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
          (fun _ => r) (fun _ => hr) PUnit.unit p T) ≠ 0 →
    ∀ z ∈ Set.range ((TopCat.of (P × (ClosedInterval × Q))).toSSetObjEquiv _ σ.val),
      ∃ hz : z ∈ OriginalSecondHalfFamily.domain α β K hK r,
        SobolevLength.length F (retainedCut α β K hK r hr ⟨z, hz⟩) < A

theorem exists_scale (hcompact : IsCompact K) {ε b : ℝ} (hρr : 4 * ρ < r)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
    ∀ {ι : Type*} (W : ι → Set (P × (ClosedInterval × Q)))
      (cx : ι → P) (cy : ι → ClosedInterval × Q),
      (∀ v, W v ⊆ PairDistanceCover.cover id η (cx v) ×ˢ PairDistanceCover.cover id η (cy v)) →
    ∀ (ρJ : ℝ),
      (∀ v, W v ⊆ PairDistanceCover.cover (fun x => basepoint (α x)) (ρJ / 4) (cx v) ×ˢ
        PairDistanceCover.cover (fun y : ClosedInterval × Q => basepoint (β y.2)) (ρJ / 4) (cy v)) →
      (∀ z : P × (ClosedInterval × Q),
        dist (basepoint (α z.1)) (basepoint (β z.2.2)) < 2 * ρJ → z ∈ K) →
    ∀ (a p : ℕ) (L A : ℝ)
      (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
        (NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2)) ρJ)) a J = 0 →
    ∀ (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : K, SobolevLength.length F (OriginalSecondHalfFamily.family α β K hK z).2 < A) →
      adequate α β K hK r hr F hn h W a p J T (A - L + 3 * ε) := by
  obtain ⟨η, hη, hηb, hall⟩ := ThreeCapWholeRectangle.exists_filtered_scale F K hcompact
    (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
    (fun _ => r) (fun _ => ρ) (fun _ => hr) (fun _ => h.1.trans h.2.2) (fun _ => hρr)
    hε hb (fun _ => hradius)
  refine ⟨η, hη, hηb, ?_⟩
  intro ι W cx cy hrect ρJ hrectJ hTube a p L A J hJ T hT hA q σ hnz z hz
  obtain ⟨v, hv⟩ := (TopCat.mem_smallSingularSubcomplex_iff
    (TopCat.of (P × (ClosedInterval × Q))) W σ.val).mp σ.property
  have hWK : W v ⊆ K :=
    ThreeCapJoinTube.rectangle_in_tube (P := TopCat.of P) (Q := TopCat.of (ClosedInterval × Q))
      (E := Ambient n)
      (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2))
      ρJ (cx v) (cy v) (W v) K (hrectJ v) hTube a n p q J hJ _ _ σ.val hv hnz
  exact hall (cx v) (cy v) (W v) (hrect v) hWK PUnit.unit a n p q L A J
    (AnnularSelfCut.cocycle n hn h) (AnnularSupportedCut.cocycle_supported n hn h) T hT
    (fun w _ => hA w) σ.val hv hnz z (hv hz)

variable {ι : Type*} (W : ι → Set (P × (ClosedInterval × Q))) (A : ℝ)
  (a p : ℕ) (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
  (hgood : adequate α β K hK r hr F hn h W a p J T A)
  (hJ : cochainCoboundary (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a J = 0)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
  (U : Set (P × (ClosedInterval × Q)))
  (hU : cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q))) U) a J = 0)
  (hW : ∀ v, W v ⊆ U ∨
    W v ⊆ {z | ρ < SelfCutParameterFamily.distanceValue K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit z} ∨
    W v ⊆ OriginalSecondHalfFamily.domain α β K hK r)

def operation : DegreeLoweringHomology.Map (small (TopCat.of (P × (ClosedInterval × Q))) W)
    (chains (TopCat.of (bounded α β K hK r hr F A))) (a + n + p) :=
  ThreeCapDomainFiltered.operation (TopCat.of (P × (ClosedInterval × Q))) (TopCat.of (SphereLoop n))
    (OriginalSecondHalfFamily.domain α β K hK r) (retainedCut α β K hK r hr)
    {γ | SobolevLength.length F γ < A} W a n p J
    (SupportedSelfCutAdequacy.extension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
      (AnnularSelfCut.cocycle n hn h))
    (SelfCutParameterFamily.testedExtension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
      (fun _ => r) (fun _ => hr) PUnit.unit p T) hgood
    (fun q => PartialFamilyThreeCapBoundary.boundary K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
      (fun _ => r) (fun _ => hr) W U ρ PUnit.unit hW a n p J hJ hU
      (AnnularSelfCut.cocycle n hn h) (AnnularSelfCut.cocycle_closed n hn h)
      (AnnularSupportedCut.cocycle_supported n hn h) T hT q)

theorem source_inclusion (q : ℕ) :
    (operation α β K hK r hr F hn h W A a p J T hgood hJ hT U hU hW).component q ≫
      (push (source α β K hK r hr F A)).f q =
    (inclusion (TopCat.of (P × (ClosedInterval × Q))) W).f (a + n + p + q) ≫
      threeCap (TopCat.of (P × (ClosedInterval × Q))) a n p q J
        (SupportedSelfCutAdequacy.extension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
          (AnnularSelfCut.cocycle n hn h))
        (SelfCutParameterFamily.testedExtension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
          (fun _ => r) (fun _ => hr) PUnit.unit p T) :=
  ThreeCapDomainFiltered.source_inclusion (TopCat.of (P × (ClosedInterval × Q)))
    (TopCat.of (SphereLoop n)) (OriginalSecondHalfFamily.domain α β K hK r)
    (retainedCut α β K hK r hr) {γ | SobolevLength.length F γ < A} W a n p J
    (SupportedSelfCutAdequacy.extension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
      (AnnularSelfCut.cocycle n hn h))
    (SelfCutParameterFamily.testedExtension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
      (fun _ => r) (fun _ => hr) PUnit.unit p T) hgood q

end
end Finsler.OriginalSecondHalfGlobalOperation
