module

public import Finsler.Loop.NativeBVRelativeCochain
public import Finsler.Topology.CupOne

/-! The actual Alexander--Whitney cup-order error on the near-cut space
has an explicit cup-one primitive. The ORIGINAL supported Thom/time map
and full-period H1 rotation carry this primitive to a constant-relative
boundary. No support condition on either near-space cochain is needed.
This exchanges the order of multiplication, not the two cut outputs. -/
@[expose] public section
namespace Finsler.NativeBVThomCupOne
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedSelfCut Finsler.NativeBVThomBoundary
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
  (p q k : ℕ) (h : p + q = k + 1)
  (A : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) p)
  (B : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)

def primitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + k) :=
  source m hρ hρr k (CupOne.cupOne _ p q k h A B)

def ordered : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + (k + 1)) :=
  source m hρ hρr (k + 1) (CupOne.cup _ p q (k + 1) h A B)

def reordered : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + (k + 1)) :=
  source m hρ hρr (k + 1) (CupOne.cup _ q p (k + 1) (by omega) B A)

theorem boundary
    (hA : cochainCoboundary (ZMod 2) _ p A = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0) :
    (chains (Loops (m + 1))).d (m + (k + 1)) (m + k) ≫ primitive m hρ hρr p q k h A B =
      ordered m hρ hρr p q k h A B - reordered m hρ hρr p q k h A B := by
  unfold primitive source ordered reordered
  rw [lowering_boundary_at (GlobalThomTime.operation m hρ hρr) k (k + 1) rfl]
  change _ ≫ cochainCoboundary (ZMod 2) _ k (CupOne.cupOne _ p q k h A B) = _
  rw [CupOne.boundary_cocycles _ p q k h A B hA hB, Preadditive.comp_sub]
  rfl

theorem primitive_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (m + k)
      (primitive m hρ hρr p q k h A B) = 0 := source_constants_zero _ _ _ _ _

def rotatedPrimitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + k - 1) :=
  (H1LoopRotation.chainHomotopy (m + 1)).hom (m + k - 1) (m + k) ≫ primitive m hρ hρr p q k h A B

theorem rotated_boundary (hm : 1 ≤ m)
    (hA : cochainCoboundary (ZMod 2) _ p A = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0) :
    (chains (Loops (m + 1))).d (m + k) (m + k - 1) ≫ rotatedPrimitive m hρ hρr p q k h A B =
      (H1LoopRotation.chainHomotopy (m + 1)).hom (m + k) (m + (k + 1)) ≫ ordered m hρ hρr p q k h A B -
      (H1LoopRotation.chainHomotopy (m + 1)).hom (m + k) (m + (k + 1)) ≫ reordered m hρ hρr p q k h A B := by
  unfold rotatedPrimitive
  rw [NativeBVRelativeCochain.boundary_at (m + 1) _ _ (m + (k + 1)) (by omega) (by omega),
    boundary m hρ hρr p q k h A B hA hB, Preadditive.comp_sub]

theorem rotatedPrimitive_constants_zero (hm : 1 ≤ m) :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (m + k - 1)
      (rotatedPrimitive m hρ hρr p q k h A B) = 0 :=
  NativeBVRelativeCochain.rotation_constants_zero_at (m + 1) _ _ (by omega) _
    (primitive_constants_zero m hρ hρr p q k h A B)

theorem relative_values (hm : 1 ≤ m)
    (hA : cochainCoboundary (ZMod 2) _ p A = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0)
    {M : ModuleCat.{0} (ZMod 2)} (u : M ⟶ (chains (Loops (m + 1))).X (m + k))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f (m + k)) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d (m + k) (m + k - 1) = 0) :
    u ≫ (H1LoopRotation.chainHomotopy (m + 1)).hom (m + k) (m + (k + 1)) ≫ ordered m hρ hρr p q k h A B =
      u ≫ (H1LoopRotation.chainHomotopy (m + 1)).hom (m + k) (m + (k + 1)) ≫ reordered m hρ hρr p q k h A B := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← rotated_boundary m hρ hρr p q k h A B hm hA hB]
  exact relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1))) _ _ u hu _
    (rotatedPrimitive_constants_zero m hρ hρr p q k h A B hm)

theorem cycle_values (hm : 1 ≤ m)
    (hA : cochainCoboundary (ZMod 2) _ p A = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0) :
    (chains (Loops (m + 1))).iCycles (m + k) ≫
      (H1LoopRotation.chainHomotopy (m + 1)).hom (m + k) (m + (k + 1)) ≫ ordered m hρ hρr p q k h A B =
    (chains (Loops (m + 1))).iCycles (m + k) ≫
      (H1LoopRotation.chainHomotopy (m + 1)).hom (m + k) (m + (k + 1)) ≫ reordered m hρ hρr p q k h A B := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← rotated_boundary m hρ hρr p q k h A B hm hA hB,
    ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]

end
end Finsler.NativeBVThomCupOne
