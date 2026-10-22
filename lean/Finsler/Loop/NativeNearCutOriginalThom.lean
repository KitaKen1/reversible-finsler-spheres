module

public import Finsler.Loop.NativeNearCutPrimitiveGH
public import Finsler.Loop.NativeBVThomBoundary

/-! The ORIGINAL Thom radius already lies inside the fixed rejoining
tube. Pull back the SAME near primitive without changing either radius,
then pass it through the ORIGINAL Thom/time operation. That operation
supplies time-end, diagonal, far, and source-constant support. -/
@[expose] public section
namespace Finsler.NativeNearCutOriginalThom
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SupportedSelfCut Finsler.NativeInnerCutPullback
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

abbrev space := TopCat.of (neighborhood (m + 1) (NativeClosingArcPowerVanishing.radius m hm F))

theorem original_radius_le_eighth : NativeClosingArcPowerVanishing.radius m hm F ≤ 1 / 8 :=
  NativeClosingArcUniformTube.radius_le_eighth F _

def intoNear : space m hm F ⟶ NativeNearCutRejoining.domain (m + 1) :=
  TopCat.ofHom ⟨fun z => ⟨z.val, z.property.trans_le (original_radius_le_eighth m hm F)⟩,
    continuous_subtype_val.subtype_mk _⟩

def underlying : space m hm F ⟶ Loops (m + 1) :=
  TopCat.ofHom ⟨fun z => z.val.2, by fun_prop⟩

theorem source_factor : intoNear m hm F ≫ NativeNearCutPrimitiveGH.source (m + 1) =
    underlying m hm F := rfl

theorem tested_factor : intoNear m hm F ≫ NativeNearCutPrimitiveGH.tested (m + 1) =
    TopCat.ofHom (tested (m + 1) (radiusLe m hm F)) := rfl

theorem retained_factor : intoNear m hm F ≫ NativeNearCutPrimitiveGH.retained (m + 1) =
    TopCat.ofHom (retained (m + 1) (radiusLe m hm F)) := rfl

def primitive : singularCochainGroup (ZMod 2) (space m hm F) (m - 1) :=
  cochainPullback (intoNear m hm F) (m - 1) (NativeNearCutPrimitiveGH.primitive m hm F)

def before : singularCochainGroup (ZMod 2) (space m hm F) m :=
  cochainPullback (underlying m hm F) m (NativeNearCutPrimitiveGH.original m hm F)

def after : singularCochainGroup (ZMod 2) (space m hm F) m :=
  cochainPullback (TopCat.ofHom (tested (m + 1) (radiusLe m hm F))) m
      (NativeNearCutPrimitiveGH.original m hm F) +
    cochainPullback (TopCat.ofHom (retained (m + 1) (radiusLe m hm F))) m
      (NativeNearCutPrimitiveGH.original m hm F)

theorem before_pullback : cochainPullback (intoNear m hm F) m
    (NativeNearCutPrimitiveGH.before m hm F) = before m hm F := by
  unfold NativeNearCutPrimitiveGH.before before
  rw [← pullback_comp, source_factor]

theorem after_pullback : cochainPullback (intoNear m hm F) m
    (NativeNearCutPrimitiveGH.after m hm F) = after m hm F := by
  unfold NativeNearCutPrimitiveGH.after after
  change (push (intoNear m hm F)).f m ≫ (_ + _) = _
  rw [Preadditive.comp_add]
  change cochainPullback (intoNear m hm F) m (cochainPullback _ m _) +
    cochainPullback (intoNear m hm F) m (cochainPullback _ m _) = _
  rw [← pullback_comp, ← pullback_comp, tested_factor, retained_factor]

theorem primitive_boundary : (chains (space m hm F)).d m (m - 1) ≫ primitive m hm F =
    before m hm F - after m hm F := by
  change (chains (space m hm F)).d m (m - 1) ≫
    ((push (intoNear m hm F)).f (m - 1) ≫ _) = _
  rw [← Category.assoc, ← (push (intoNear m hm F)).comm, Category.assoc,
    NativeNearCutPrimitiveGH.primitive_boundary, Preadditive.comp_sub]
  exact congrArg₂ (· - ·) (before_pullback m hm F) (after_pullback m hm F)

def parameterPrimitive : singularCochainGroup (ZMod 2) (SelfCutThomCocycle.parameters (m + 1))
    ((m + 1) + (m - 1)) :=
  NativeBVThomBoundary.parameter m (rhoPos m hm F) (rhoLt m hm F) (m - 1) (primitive m hm F)

theorem parameter_endpoints (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SelfCutThomCocycle.atTime (m + 1) t) ((m + 1) + (m - 1))
      (parameterPrimitive m hm F) = 0 :=
  NativeBVThomBoundary.parameter_endpoint _ _ _ _ _ t ht

theorem parameter_diagonal {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1))
    (hf : ∀ x, f x ∈ FilteredGlobalThomTime.endpointCarrier (m + 1)) :
    cochainPullback f ((m + 1) + (m - 1)) (parameterPrimitive m hm F) = 0 :=
  NativeBVThomBoundary.parameter_diagonal _ _ _ _ _ f hf

theorem parameter_far {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1))
    (hf : ∀ x, f x ∈ exterior (m + 1) (NativeOrderedDoubleCutSupported.thomRadius m hm F)) :
    cochainPullback f ((m + 1) + (m - 1)) (parameterPrimitive m hm F) = 0 :=
  NativeBVThomBoundary.parameter_far _ _ _ _ _ f hf

def sourcePrimitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + (m - 1)) :=
  NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F) (m - 1) (primitive m hm F)

def sourceBefore : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + m) :=
  NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F) m (before m hm F)

def sourceAfter : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + m) :=
  NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F) m (after m hm F)

theorem source_boundary : (chains (Loops (m + 1))).d (m + m) (m + (m - 1)) ≫
    sourcePrimitive m hm F = sourceBefore m hm F - sourceAfter m hm F := by
  unfold sourcePrimitive sourceBefore sourceAfter NativeBVThomBoundary.source
  rw [NativeBVThomBoundary.lowering_boundary_at _ _ _ (by omega), primitive_boundary,
    Preadditive.comp_sub]

theorem source_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (m + (m - 1)) (sourcePrimitive m hm F) = 0 :=
  NativeBVThomBoundary.source_constants_zero _ _ _ _ _

theorem relative_cycle_values {M : ModuleCat.{0} (ZMod 2)}
    (u : M ⟶ (chains (Loops (m + 1))).X (m + m))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f (m + m)) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d
        (m + m) (m + (m - 1)) = 0) :
    u ≫ sourceBefore m hm F = u ≫ sourceAfter m hm F := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← source_boundary m hm F]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1)))
    _ _ u hu _ (source_constants_zero m hm F)

end
end Finsler.NativeNearCutOriginalThom
