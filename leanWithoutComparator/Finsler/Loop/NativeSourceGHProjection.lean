module

public import Finsler.Loop.NativeSourceTimeProjection
public import Finsler.Loop.NativeNearCutPowerSubstitution

/-! Apply actual source projection to the SAME normalized supported GH_0
and retained GH_r, then compose with actual near rejoining. Thus the
ordinary source cup evaluates to one plus the retained ordinary-cup
remainder on the SAME raised inputs. Neither remainder zero nor a BV
derivation/comparison is assumed. -/
@[expose] public section
namespace Finsler.NativeSourceGHProjection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.NativeInnerCutPullback
open Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def bareSource : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + NativeGHPowers.degree m r) :=
  NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F) (NativeGHPowers.degree m r)
    (NativeNearCutPowerSubstitution.retainedPower m hm F r)

theorem bareSource_closed : cochainCoboundary (ZMod 2) _ (m + NativeGHPowers.degree m r) (bareSource m hm F r) = 0 :=
  DegreeLoweringCochainPullback.closed (GlobalThomTime.operation m (rhoPos m hm F) (rhoLt m hm F)) _ _
    (NativeNearCutPowerSubstitution.retainedPower_closed m hm F r)

theorem bareSource_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (m + NativeGHPowers.degree m r) (bareSource m hm F r) = 0 :=
  NativeBVThomBoundary.source_constants_zero _ _ _ _ _

def ordinaryCup : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  CupOne.cup _ m (m + NativeGHPowers.degree m r) (NativeGHPowers.degree m (r + 1))
    (NativeNearCutPowerSubstitution.degree_match m r).symm
    (NativeNearCutPrimitiveGH.original m hm F) (bareSource m hm F r)

theorem ordinaryCup_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1)) (ordinaryCup m hm F r) = 0 :=
  CupCapOrder.closed _ _ _ _ _ _ _ (NativeNearCutPrimitiveGH.original_closed m hm F) (bareSource_closed m hm F r)

theorem ordinaryCup_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1)) (ordinaryCup m hm F r) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ _ _ _ (Or.inr (bareSource_constants_zero m hm F r))

theorem near_source : NativeSourceThomProjection.near m m (NativeGHPowers.degree m r)
    (NativeNearCutPrimitiveGH.original m hm F) (NativeNearCutPowerSubstitution.retainedPower m hm F r) =
      NativeNearCutPowerSubstitution.nearSource m hm F r := by
  unfold NativeSourceThomProjection.near NativeSourceThomProjection.alpha
  rw [← pullback_comp]
  rfl

theorem projection_exists : ∃ K : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) - 1),
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1) - 1) K = 0 ∧
    (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1)) (NativeGHPowers.degree m (r + 1) - 1) ≫ K =
      ordinaryCup m hm F r - NativeNearCutPowerSubstitution.sourceTest m hm F r := by
  have h := NativeSourceTimeProjection.exists_boundary_at_degree m (rhoPos m hm F) (rhoLt m hm F)
    m (NativeGHPowers.degree m r) (NativeGHPowers.degree m (r + 1)) (by omega)
    (NativeNearCutPowerSubstitution.degree_match m r) (NativeNearCutPrimitiveGH.original m hm F)
    (NativeNearCutPowerSubstitution.retainedPower m hm F r)
    (NativeClosingArcPowerVanishing.powerCocycle_normalized m hm F 0)
    (NativeNearCutPrimitiveGH.original_closed m hm F) (NativeNearCutPowerSubstitution.retainedPower_closed m hm F r)
  rw [near_source] at h
  exact h

def projectionPrimitive := Classical.choose (projection_exists m hm F r)

theorem projection_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1) - 1) (projectionPrimitive m hm F r) = 0 :=
  (Classical.choose_spec (projection_exists m hm F r)).1

theorem projection_boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1))
    (NativeGHPowers.degree m (r + 1) - 1) ≫ projectionPrimitive m hm F r =
      ordinaryCup m hm F r - NativeNearCutPowerSubstitution.sourceTest m hm F r :=
  (Classical.choose_spec (projection_exists m hm F r)).2

def primitive := projectionPrimitive m hm F r + NativeNearCutPowerSubstitution.primitive m hm F r

theorem boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1))
    (NativeGHPowers.degree m (r + 1) - 1) ≫ primitive m hm F r =
      ordinaryCup m hm F r - (NativeBVTestedTransgression.after m hm F r + NativeNearCutPowerSubstitution.remainder m hm F r) := by
  rw [primitive, Preadditive.comp_add, projection_boundary, NativeNearCutPowerSubstitution.boundary]
  abel

theorem primitive_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1) - 1) (primitive m hm F r) = 0 := by
  change (push (GlobalTimeCupConstantsVanish.inclusion (m + 1))).f _ ≫ (_ + _) = 0
  rw [Preadditive.comp_add]
  exact (congrArg₂ (· + ·) (projection_constants_zero m hm F r)
    (NativeNearCutPowerSubstitution.primitive_constants_zero m hm F r)).trans (zero_add _)

theorem relative_cycle_values {M : ModuleCat.{0} (ZMod 2)}
    (u : M ⟶ (chains (Loops (m + 1))).X (NativeGHPowers.degree m (r + 1)))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f
      (NativeGHPowers.degree m (r + 1))) ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d
        (NativeGHPowers.degree m (r + 1)) (NativeGHPowers.degree m (r + 1) - 1) = 0) :
    u ≫ ordinaryCup m hm F r = u ≫ NativeBVTestedTransgression.after m hm F r +
      u ≫ NativeNearCutPowerSubstitution.remainder m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_add, ← Preadditive.comp_sub, ← boundary m hm F r]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1)))
    _ _ u hu _ (primitive_constants_zero m hm F r)

theorem projection_cycle_values : (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ ordinaryCup m hm F r =
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ NativeNearCutPowerSubstitution.sourceTest m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← projection_boundary m hm F r, ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]

theorem value_one_plus_remainder (P : Sphere (m + 1)) (v₀ : equator P)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ ordinaryCup m hm F r).hom c =
      1 + ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ NativeNearCutPowerSubstitution.remainder m hm F r).hom c := by
  rw [projection_cycle_values]
  exact NativeNearCutPowerSubstitution.value_one_plus_remainder m hm F r P v₀ c hc

theorem value_one_iff_remainder_zero (P : Sphere (m + 1)) (v₀ : equator P)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ ordinaryCup m hm F r).hom c = 1 ↔
      ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ NativeNearCutPowerSubstitution.remainder m hm F r).hom c = 0 := by
  rw [value_one_plus_remainder m hm F r P v₀ c hc]
  exact add_eq_left

end
end Finsler.NativeSourceGHProjection
