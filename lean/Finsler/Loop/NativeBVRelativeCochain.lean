module

public import Finsler.Loop.NativeBVThomBoundary
public import Finsler.Loop.SelfSweepCochain
public import Finsler.Loop.H1LoopRotation
public import Finsler.Loop.DoublePrismCochainBoundary

/-! The ORIGINAL full-period H1 rotation preserves constant-relative
cochains and their actual boundary comparisons. No cut compatibility is
assumed; both rotation endpoints are the same identity map. -/
@[expose] public section
namespace Finsler.NativeBVRelativeCochain
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SobolevShift Finsler.SobolevCircleRepresentative Finsler.SobolevCircleAction
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem shift_constant (n : ℕ) (x : Sphere n) (a : ℝ) :
    shiftSphere (constantSphereLoop x) a = constantSphereLoop x := by
  apply sphereCircleMap_injective n
  ext t
  rw [circleMap_shiftSphere, shiftedSphereMap_apply, sphereCircleMap_constant, sphereCircleMap_constant]

theorem rotation_mem_constants (n : ℕ) (t : _root_.unitInterval) (u : Loops n)
    (hu : u ∈ consts n) : (H1LoopRotation.homotopy n) (t, u) ∈ consts n := by
  obtain ⟨x, rfl⟩ := hu
  exact ⟨x, (shift_constant n x (t : ℝ)).symm⟩

theorem rotation_constants_zero (n q : ℕ)
    (K : singularCochainGroup (ZMod 2) (Loops n) (q + 1))
    (hK : cochainPullback (GlobalTimeCupConstantsVanish.inclusion n) (q + 1) K = 0) :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion n) q
      (SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy n) q K) = 0 := by
  apply DoublePrismCochainBoundary.prism_pre_zero (H1LoopRotation.homotopy n)
    (GlobalTimeCupConstantsVanish.inclusion n) q K
  apply CochainCarrierPullbackZero.family_zero (consts n) (q + 1) K hK
  intro z
  exact rotation_mem_constants n z.2.down z.1.val z.1.property

theorem rotation_constants_zero_at (n i j : ℕ) (h : i + 1 = j)
    (K : singularCochainGroup (ZMod 2) (Loops n) j)
    (hK : cochainPullback (GlobalTimeCupConstantsVanish.inclusion n) j K = 0) :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion n) i
      ((H1LoopRotation.chainHomotopy n).hom i j ≫ K) = 0 := by
  subst j
  exact rotation_constants_zero n i K hK

theorem boundary_at (n i j k : ℕ) (hi : i + 1 = j) (hj : j + 1 = k)
    (K : singularCochainGroup (ZMod 2) (Loops n) j) :
    (chains (Loops n)).d j i ≫ ((H1LoopRotation.chainHomotopy n).hom i j ≫ K) =
      (H1LoopRotation.chainHomotopy n).hom j k ≫ ((chains (Loops n)).d k j ≫ K) := by
  subst j k
  exact SelfSweepCochain.coboundary (H1LoopRotation.chainHomotopy n) i K

theorem boundary_relative_zero (n i j k : ℕ) (hi : i + 1 = j) (hj : j + 1 = k)
    (K : singularCochainGroup (ZMod 2) (Loops n) j)
    (hK : cochainPullback (GlobalTimeCupConstantsVanish.inclusion n) j K = 0)
    {M : ModuleCat.{0} (ZMod 2)} (u : M ⟶ (chains (Loops n)).X j)
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts n)).singularChainComplexπ coeff).f j) ≫
      ((RelativePrismSweep.targetPair (consts n)).singularChainComplex coeff).d j i = 0) :
    u ≫ (H1LoopRotation.chainHomotopy n).hom j k ≫ ((chains (Loops n)).d k j ≫ K) = 0 := by
  rw [← boundary_at n i j k hi hj]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts n))
    i j u hu _ (rotation_constants_zero_at n i j hi K hK)

theorem comparison_relative_values (n i j k : ℕ) (hi : i + 1 = j) (hj : j + 1 = k)
    (K : singularCochainGroup (ZMod 2) (Loops n) j)
    (hK : cochainPullback (GlobalTimeCupConstantsVanish.inclusion n) j K = 0)
    (T U : singularCochainGroup (ZMod 2) (Loops n) k)
    (hδ : (chains (Loops n)).d k j ≫ K = T - U)
    {M : ModuleCat.{0} (ZMod 2)} (u : M ⟶ (chains (Loops n)).X j)
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts n)).singularChainComplexπ coeff).f j) ≫
      ((RelativePrismSweep.targetPair (consts n)).singularChainComplex coeff).d j i = 0) :
    u ≫ (H1LoopRotation.chainHomotopy n).hom j k ≫ T =
      u ≫ (H1LoopRotation.chainHomotopy n).hom j k ≫ U := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← Preadditive.comp_sub, ← hδ]
  exact boundary_relative_zero n i j k hi hj K hK u hu

end
end Finsler.NativeBVRelativeCochain
