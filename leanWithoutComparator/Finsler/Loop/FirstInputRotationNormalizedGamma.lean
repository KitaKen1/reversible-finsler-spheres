module

public import Finsler.Loop.OriginalFirstHalfCutNormalizedFactors
public import Finsler.Loop.FirstInputRotationCupOne
public import Finsler.Loop.FirstInputRotationSupportedCap

/-! Actual normalization of the rotating proper cut gamma. Both the
normalized cochain and its actual primitive retain the tested-short
support and the same uniform whole-parent length bound. At rotation
zero they strictly factor through the original self-cut parameter. -/

@[expose] public section
namespace Finsler.FirstInputRotationNormalizedGamma

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem primitive_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (a d : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y d) :
    cochainPullback f a ((SingularNormalization.projectorHomotopy Y).hom a d ≫ φ) =
      (SingularNormalization.projectorHomotopy X).hom a d ≫ cochainPullback f d φ := by
  have he : (push f).f a ≫ (SingularNormalization.projectorHomotopy Y).hom a d =
      (SingularNormalization.projectorHomotopy X).hom a d ≫ (push f).f d :=
    NormalizationCarrier.homotopy_natural (TopCat.toSSet.map f) a d
  change (push f).f a ≫ ((SingularNormalization.projectorHomotopy Y).hom a d ≫ φ) = _
  rw [← Category.assoc, he, Category.assoc]
  rfl

private theorem primitive_boundary_regrade (X : TopCat.{0}) (a d : ℕ) (hd : a + 1 = d)
    (φ : singularCochainGroup (ZMod 2) X d)
    (hφ : cochainCoboundary (ZMod 2) X d φ = 0) :
    cochainCoboundary (ZMod 2) X a ((SingularNormalization.projectorHomotopy X).hom a d ≫ φ) =
      eqToHom (congrArg (chains X).X hd) ≫ (SingularNormalization.normalize X d φ - φ) := by
  subst d
  simpa only [SingularNormalization.primitive, eqToHom_refl, Category.id_comp] using
    SingularNormalization.primitive_boundary X a φ hφ

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def normalized : singularCochainGroup (ZMod 2) (space α β R r) ((m + 1) + p) :=
  SingularNormalization.normalize (space α β R r) ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T)

def primitive : singularCochainGroup (ZMod 2) (space α β R r) (m + p) :=
  (SingularNormalization.projectorHomotopy (space α β R r)).hom (m + p) ((m + 1) + p) ≫
    FirstInputRotationCupOne.gamma α β R r hR hr h p T

theorem gamma_zero :
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) ((m + 1) + p)
      (FirstInputRotationCupOne.gamma α β R r hR hr h p T) =
    cochainPullback (FirstInputRotationOriginalFactors.projection α β R r) ((m + 1) + p)
      (OriginalFirstHalfCutNormalizedFactors.cutGamma α r hr h p T) := by
  rw [FirstInputRotationCupOne.gamma, cochainCup_naturality,
    FirstInputRotationOriginalFactors.thom_zero, FirstInputRotationOriginalFactors.tested_zero,
    OriginalFirstHalfCutNormalizedFactors.cutGamma, cochainCup_naturality]

theorem normalized_zero :
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) ((m + 1) + p)
      (normalized α β R r hR hr h p T) =
    cochainPullback (FirstInputRotationOriginalFactors.projection α β R r) ((m + 1) + p)
      (OriginalFirstHalfCutNormalizedFactors.normalized α r hr h p T) := by
  rw [normalized, SingularNormalization.normalize_natural, gamma_zero,
    ← SingularNormalization.normalize_natural]
  rfl

theorem primitive_zero :
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) (m + p)
      (primitive α β R r hR hr h p T) =
    cochainPullback (FirstInputRotationOriginalFactors.projection α β R r) (m + p)
      (OriginalFirstHalfCutNormalizedFactors.primitive α r hr h p T) := by
  rw [primitive, primitive_pullback, gamma_zero]
  exact (primitive_pullback _ _ _ _).symm

theorem normalized_closed
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainCoboundary (ZMod 2) (space α β R r) ((m + 1) + p) (normalized α β R r hR hr h p T) = 0 :=
  SingularNormalization.normalize_closed _ _ _ (FirstInputRotationCupOne.gamma_closed α β R r hR hr h p T hT)

theorem primitive_boundary
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainCoboundary (ZMod 2) (space α β R r) (m + p) (primitive α β R r hR hr h p T) =
      eqToHom (congrArg (chains (space α β R r)).X (show (m + p) + 1 = (m + 1) + p by omega)) ≫
        (normalized α β R r hR hr h p T - FirstInputRotationCupOne.gamma α β R r hR hr h p T) :=
  primitive_boundary_regrade _ _ _ (by omega) _
    (FirstInputRotationCupOne.gamma_closed α β R r hR hr h p T hT)

theorem gamma_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (space α β R r) (collar α β R r δ)) ((m + 1) + p)
      (FirstInputRotationCupOne.gamma α β R r hR hr h p T) = 0 := by
  rw [FirstInputRotationCupOne.gamma, cochainCup_naturality,
    thom_inner_zero α β R r hR hr (by omega) h, cochainCup_zero_left]

theorem normalized_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (space α β R r) (collar α β R r δ)) ((m + 1) + p)
      (normalized α β R r hR hr h p T) = 0 :=
  SingularNormalization.normalize_supported _ _ _ (gamma_inner_zero α β R r hR hr h p T)

theorem primitive_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (space α β R r) (collar α β R r δ)) (m + p)
      (primitive α β R r hR hr h p T) = 0 := by
  rw [primitive, primitive_pullback, gamma_inner_zero, comp_zero]

variable (F : ReversibleMetric (m + 1)) (L : ℝ)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)

include hshort in
theorem gamma_short_zero :
    cochainPullback (SupportedCap.subspaceMap (space α β R r)
      (TestedCupOneSupport.short F (testedMap α β R r hR hr) L)) ((m + 1) + p)
      (FirstInputRotationCupOne.gamma α β R r hR hr h p T) = 0 :=
  TestedCupOneSupport.gamma_zero F (testedMap α β R r hR hr) L (m + 1) p _ T hshort

include hshort in
theorem normalized_short_zero :
    cochainPullback (SupportedCap.subspaceMap (space α β R r)
      (TestedCupOneSupport.short F (testedMap α β R r hR hr) L)) ((m + 1) + p)
      (normalized α β R r hR hr h p T) = 0 :=
  SingularNormalization.normalize_supported _ _ _ (gamma_short_zero α β R r hR hr h p T F L hshort)

include hshort in
theorem primitive_short_zero :
    cochainPullback (SupportedCap.subspaceMap (space α β R r)
      (TestedCupOneSupport.short F (testedMap α β R r hR hr) L)) (m + p)
      (primitive α β R r hR hr h p T) = 0 := by
  rw [primitive, primitive_pullback, gamma_short_zero α β R r hR hr h p T F L hshort, comp_zero]

theorem exists_uniform [CompactSpace P] [CompactSpace Q] {ε b : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ u > 0, u ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < u →
      ∃ η > 0, η ≤ b ∧ ∀ (p : ℕ) (L A : ℝ)
        (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p),
        cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
          (SelfCutOscillation.short F L)) p T = 0 →
        (∀ z : CompactNearJoinParameters.tube α β R,
          SobolevLength.length F (α z.val.1) + SobolevLength.length F (β z.val.2) < A) →
        FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η ((m + 1) + p)
          (FirstInputRotationCupOne.gamma α β R r hR hr h p T) ∧
        FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η ((m + 1) + p)
          (normalized α β R r hR hr h p T) ∧
        FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η (m + p)
          (primitive α β R r hR hr h p T) := by
  obtain ⟨u, hu, hu1, had⟩ := FirstInputRotationSupportedCap.exists_uniform α β r hr F hε hb hradius
  refine ⟨u, hu, hu1, ?_⟩
  intro R hR hRu
  obtain ⟨η, hη, hηb, hbnd⟩ := had R hR hRu
  refine ⟨η, hη, hηb, ?_⟩
  intro p L A T hshort hA
  exact ⟨hbnd _ L A _ (gamma_short_zero α β R r hR hr h p T F L hshort) hA,
    hbnd _ L A _ (normalized_short_zero α β R r hR hr h p T F L hshort) hA,
    hbnd _ L A _ (primitive_short_zero α β R r hR hr h p T F L hshort) hA⟩

end
end Finsler.FirstInputRotationNormalizedGamma
