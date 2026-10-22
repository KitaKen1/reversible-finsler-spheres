module

public import Finsler.Loop.SupportedCapIntervalOrder
public import Finsler.Loop.NativeSupportedStageCarrier
public import Finsler.Loop.NativePrefixPostponedAlignment

/-! Specialize the actual cap/interval comparison to the ORIGINAL
normalized self-cut Thom and near/far operation. The original operation
is identified after its real source-degree transport. Endpoint-relative
tests remain explicit hypotheses; the full repeated time/square
identification is not asserted here. -/
@[expose] public section
namespace Finsler.NativeSupportedIntervalOrder
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RightIntervalCochain Finsler.NativeOrderedDoubleCutSupported
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1))
  {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
  (T : singularCochainGroup (ZMod 2) (space (TopCat.of (near f r))) (q + 1))

theorem thom_normalized : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X)
    (thom f (by omega) hρ) :=
  SupportedCapIntervalLocal.normalized_pullback f (m + 1) _
    (NormalizedSelfCut.cocycle_normalized (m + 1) (by omega) hρ)

def before : singularCochainGroup (ZMod 2) X (m + q + 1) :=
  SupportedCapIntervalLocal.before X (far f ρ) (near f r) (far_open f ρ) (near_open f r)
    (cover f hρr) m q (thom f (by omega) hρ) (thom_supported f (by omega) hρ) T

def after : singularCochainGroup (ZMod 2) X (m + q + 1) :=
  SupportedCapIntervalLocal.after X (far f ρ) (near f r) (far_open f ρ) (near_open f r)
    (cover f hρr) m q (thom f (by omega) hρ) (thom_supported f (by omega) hρ) T

def primitive : singularCochainGroup (ZMod 2) X (m + q) :=
  SupportedCapIntervalOrder.primitive X (far f ρ) (near f r) (far_open f ρ) (near_open f r)
    (cover f hρr) m q (thom f (by omega) hρ) (thom_supported f (by omega) hρ) T

theorem before_original : CochainDegreeTransport.pre X (show m + q + 1 = (m + 1) + q by omega)
    ((operation f (by omega) hρ hρr).component q ≫ TimeTriangleSplit.interval (TopCat.of (near f r)) q ≫ T) =
      before m f hρ hρr q T := by
  have h := NativePrefixPostponedAlignment.pre_cut_output X (far f ρ) (near f r)
    (far_open f ρ) (near_open f r) (cover f hρr) (m + 1) q q (m + q + 1) ((m + 1) + q)
    (by omega) rfl rfl (by omega) (thom f (by omega) hρ) (thom_supported f (by omega) hρ)
    (TimeTriangleSplit.interval (TopCat.of (near f r)) q ≫ T)
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] at h
  exact h

theorem after_original : TimeTriangleSplit.interval X (m + q + 1) ≫
    CochainDegreeTransport.pre (space X) (show m + q + 1 + 1 = (m + 1) + (q + 1) by omega)
      ((operation (SupportedIntervalProduct.project X ≫ f) (by omega) hρ hρr).component (q + 1) ≫
        cochainPullback (SupportedIntervalProduct.nearOut X (near f r)) (q + 1) T) =
      after m f hρ hρr q T := by
  have h := NativePrefixPostponedAlignment.pre_cut_output (space X)
    (far (SupportedIntervalProduct.project X ≫ f) ρ) (near (SupportedIntervalProduct.project X ≫ f) r)
    (far_open _ ρ) (near_open _ r) (cover _ hρr) (m + 1) (q + 1) (q + 1)
    (m + q + 1 + 1) ((m + 1) + (q + 1)) (by omega) rfl rfl (by omega)
    (thom (SupportedIntervalProduct.project X ≫ f) (by omega) hρ)
    (thom_supported _ (by omega) hρ)
    (cochainPullback (SupportedIntervalProduct.nearOut X (near f r)) (q + 1) T)
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] at h
  have ht : SupportedCap.cut (space X)
      (far (SupportedIntervalProduct.project X ≫ f) ρ) (near (SupportedIntervalProduct.project X ≫ f) r)
      (far_open _ ρ) (near_open _ r) (cover _ hρr) (m + 1) (q + 1) (m + q + 1 + 1) (by omega)
      (thom (SupportedIntervalProduct.project X ≫ f) (by omega) hρ) (thom_supported _ (by omega) hρ) ≫
        cochainPullback (SupportedIntervalProduct.nearOut X (near f r)) (q + 1) T =
      SupportedIntervalProduct.tested X (far f ρ) (near f r) (far_open f ρ) (near_open f r)
        (cover f hρr) (m + 1) (q + 1) (m + q + 1 + 1) (by omega)
        (thom f (by omega) hρ) (thom_supported f (by omega) hρ) T := by
    simp only [SupportedIntervalProduct.tested, thom, pullback_comp]
    rfl
  exact congrArg (fun z => TimeTriangleSplit.interval X (m + q + 1) ≫ z) (h.trans ht)

variable (hT : cochainCoboundary (ZMod 2) (space (TopCat.of (near f r))) (q + 1) T = 0)
  (h₀ : cochainPullback (endpoint (TopCat.of (near f r)) 0) (q + 1) T = 0)
  (h₁ : cochainPullback (endpoint (TopCat.of (near f r)) 1) (q + 1) T = 0)

include hT h₀ h₁ in
theorem boundary : cochainCoboundary (ZMod 2) X (m + q) (primitive m f hρ hρr q T) =
    before m f hρ hρr q T - after m f hρ hρr q T :=
  SupportedCapIntervalOrder.boundary X (far f ρ) (near f r) (far_open f ρ) (near_open f r)
    (cover f hρr) m q (thom f (by omega) hρ) (thom_supported f (by omega) hρ) T
    (thom_closed f (by omega) hρ) hT h₀ h₁ (thom_normalized m f hρ)

include hT h₀ h₁ in
theorem cycle_values_eq (c : coeff ⟶ (chains X).X (m + q + 1))
    (hc : c ≫ (chains X).d (m + q + 1) (m + q) = 0) :
    c ≫ before m f hρ hρr q T = c ≫ after m f hρ hρr q T :=
  SupportedCapIntervalOrder.cycle_values_eq X (far f ρ) (near f r) (far_open f ρ) (near_open f r)
    (cover f hρr) m q (thom f (by omega) hρ) (thom_supported f (by omega) hρ) T
    (thom_closed f (by omega) hρ) hT h₀ h₁ (thom_normalized m f hρ) c hc

theorem primitive_parameter_time_zero (S : Set X) (t : IntervalSobolev.ClosedInterval)
    (hS : ∀ z ∈ S, (f z).1 = t)
    (ht : cochainPullback (SelfCutThomCocycle.atTime (m + 1) t) (m + 1)
      (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) (m + q) (primitive m f hρ hρr q T) = 0 :=
  SupportedCapIntervalOrder.primitive_thom_zero X (far f ρ) (near f r) (far_open f ρ) (near_open f r)
    (cover f hρr) m q (thom f (by omega) hρ) (thom_supported f (by omega) hρ) T S
    (NativeSupportedStageCarrier.parameter_time_zero f (by omega) hρ S t hS ht)

theorem primitive_parameter_zero (S : Set X) (hS : ∀ z ∈ S, (f z).1 = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) (m + q) (primitive m f hρ hρr q T) = 0 :=
  primitive_parameter_time_zero m f hρ hρr q T S 0 hS (NormalizedSelfCut.time_zero _ (by omega) hρ)

theorem primitive_parameter_one (S : Set X) (hS : ∀ z ∈ S, (f z).1 = 1) :
    cochainPullback (SupportedCap.subspaceMap X S) (m + q) (primitive m f hρ hρr q T) = 0 :=
  primitive_parameter_time_zero m f hρ hρr q T S 1 hS (NormalizedSelfCut.time_one _ (by omega) hρ)

end
end Finsler.NativeSupportedIntervalOrder
