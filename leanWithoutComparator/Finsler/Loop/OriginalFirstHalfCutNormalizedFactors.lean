module

public import Finsler.Loop.OriginalFirstHalfCutProductCochains
public import Finsler.Topology.NormalizationCarrier
public import Finsler.Loop.TestedCupOneSupport

/-! Normalize the actual closed proper cut cochain, retaining strict
first-factor dependence and tested-short support. The homotopy uses the
actual normalization homotopy, with the original degree convention. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCutNormalizedFactors

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

private theorem homotopy_primitive_boundary (X : TopCat.{0}) (a d : ℕ) (hd : a + 1 = d)
    (φ : singularCochainGroup (ZMod 2) X d)
    (hφ : cochainCoboundary (ZMod 2) X d φ = 0) :
    cochainCoboundary (ZMod 2) X a
      ((SingularNormalization.projectorHomotopy X).hom a d ≫ φ) =
      eqToHom (congrArg (chains X).X hd) ≫ (SingularNormalization.normalize X d φ - φ) := by
  subst d
  simpa only [SingularNormalization.primitive, eqToHom_refl, Category.id_comp] using
    SingularNormalization.primitive_boundary X a φ hφ

private theorem homotopy_primitive_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (a d : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y d) :
    cochainPullback f a ((SingularNormalization.projectorHomotopy Y).hom a d ≫ φ) =
      (SingularNormalization.projectorHomotopy X).hom a d ≫ cochainPullback f d φ := by
  have he : (SupportedCapNaturality.push f).f a ≫
      (SingularNormalization.projectorHomotopy Y).hom a d =
    (SingularNormalization.projectorHomotopy X).hom a d ≫
      (SupportedCapNaturality.push f).f d :=
    NormalizationCarrier.homotopy_natural (TopCat.toSSet.map f) a d
  change (SupportedCapNaturality.push f).f a ≫
      ((SingularNormalization.projectorHomotopy Y).hom a d ≫ φ) = _
  rw [← Category.assoc, he, Category.assoc]
  rfl

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

abbrev cutSpace : TopCat.{0} := TopCat.of (CompactRotatedCutData.source α r)

def cutGamma : singularCochainGroup (ZMod 2) (cutSpace α r) ((m + 1) + p) :=
  cochainCup (m + 1) p
    (cochainPullback (FirstInputRotationOriginalFactors.originalEvaluation α r) (m + 1)
      (AnnularSelfCut.cocycle (m + 1) (by omega) h))
    (cochainPullback (FirstInputRotationOriginalFactors.originalTester α r hr) p T)

def normalized : singularCochainGroup (ZMod 2) (cutSpace α r) ((m + 1) + p) :=
  SingularNormalization.normalize (cutSpace α r) ((m + 1) + p) (cutGamma α r hr h p T)

def primitive : singularCochainGroup (ZMod 2) (cutSpace α r) (m + p) :=
  (SingularNormalization.projectorHomotopy (cutSpace α r)).hom (m + p) ((m + 1) + p) ≫
    cutGamma α r hr h p T

theorem gamma_projection :
    OriginalFirstHalfCutProductCochains.gamma α r hr h p T (Q := Q) =
      cochainPullback (OriginalFirstHalfCutProductCochains.projection α r (Q := Q)) ((m + 1) + p)
        (cutGamma α r hr h p T) := by
  rw [cutGamma, cochainCup_naturality, OriginalFirstHalfCutProductCochains.gamma,
    OriginalFirstHalfCutProductCochains.thom, OriginalFirstHalfCutProductCochains.tested,
    pullback_comp, pullback_comp]

theorem normalized_projection :
    SingularNormalization.normalize (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
      ((m + 1) + p) (OriginalFirstHalfCutProductCochains.gamma α r hr h p T (Q := Q)) =
      cochainPullback (OriginalFirstHalfCutProductCochains.projection α r (Q := Q)) ((m + 1) + p)
        (normalized α r hr h p T) := by
  rw [gamma_projection, ← SingularNormalization.normalize_natural]
  rfl

theorem primitive_projection :
    (SingularNormalization.projectorHomotopy (OriginalFirstHalfCutProductCochains.space α r (Q := Q))).hom
      (m + p) ((m + 1) + p) ≫ OriginalFirstHalfCutProductCochains.gamma α r hr h p T (Q := Q) =
      cochainPullback (OriginalFirstHalfCutProductCochains.projection α r (Q := Q)) (m + p)
        (primitive α r hr h p T) := by
  rw [gamma_projection]
  exact (homotopy_primitive_natural _ _ _ _).symm

theorem normalized_degeneracies :
    DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (cutSpace α r))
      (normalized α r hr h p T) :=
  SingularNormalization.normalize_degeneracies _ _ _

variable (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

include hT in
theorem cutGamma_closed :
    cochainCoboundary (ZMod 2) (cutSpace α r) ((m + 1) + p) (cutGamma α r hr h p T) = 0 :=
  cochainCupZMod2_respects_cocycles (m + 1) p _ _
    (pullback_closed _ _ _ (AnnularSelfCut.cocycle_closed (m + 1) (by omega) h))
    (pullback_closed _ _ _ hT)

include hT in
theorem normalized_closed :
    cochainCoboundary (ZMod 2) (cutSpace α r) ((m + 1) + p) (normalized α r hr h p T) = 0 :=
  SingularNormalization.normalize_closed _ _ _ (cutGamma_closed α r hr h p T hT)

include hT in
theorem primitive_boundary :
    cochainCoboundary (ZMod 2) (cutSpace α r) (m + p) (primitive α r hr h p T) =
      eqToHom (congrArg (chains (cutSpace α r)).X (show (m + p) + 1 = (m + 1) + p by omega)) ≫
        (normalized α r hr h p T - cutGamma α r hr h p T) :=
  homotopy_primitive_boundary _ _ _ (by omega) _ (cutGamma_closed α r hr h p T hT)

variable (F : ReversibleMetric (m + 1)) (L : ℝ)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)

include hshort in
theorem cutGamma_short_zero :
    cochainPullback (SupportedCap.subspaceMap (cutSpace α r)
      (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L))
      ((m + 1) + p) (cutGamma α r hr h p T) = 0 :=
  TestedCupOneSupport.gamma_zero F (FirstInputRotationOriginalFactors.originalTester α r hr) L
    (m + 1) p _ T hshort

include hshort in
theorem normalized_short_zero :
    cochainPullback (SupportedCap.subspaceMap (cutSpace α r)
      (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L))
      ((m + 1) + p) (normalized α r hr h p T) = 0 :=
  SingularNormalization.normalize_supported _ _ _ (cutGamma_short_zero α r hr h p T F L hshort)

include hshort in
theorem primitive_short_zero :
    cochainPullback (SupportedCap.subspaceMap (cutSpace α r)
      (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L))
      (m + p) (primitive α r hr h p T) = 0 := by
  rw [primitive, homotopy_primitive_natural, cutGamma_short_zero α r hr h p T F L hshort, comp_zero]

end
end Finsler.OriginalFirstHalfCutNormalizedFactors
