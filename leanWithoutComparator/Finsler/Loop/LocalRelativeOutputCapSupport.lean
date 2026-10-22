module

public import Finsler.Loop.LocalOriginalRelativeOutputClass
public import Finsler.Topology.SelfCutEndpoints

/-! Literal exterior support for the original UNIT parameter cochain
and its actual source-local primitive candidate. The vanishing comes
from the same normalized Thom cocycle, so no support condition is
imposed on the chosen split-cup primitive. -/
@[expose] public section
namespace Finsler.LocalRelativeOutputCapSupport
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem local_exterior_zero (n : ℕ) (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) q) :
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀)
      (LocalNativeSupportedCap.exterior P v₀ b ρ)) (n + q)
      (LocalNativeSupportedCap.cochain n hn P v₀ b hρ hρr q ψ) = 0 := by
  let X := LocalNativeBallCut.space P v₀
  let A := LocalNativeSupportedCap.exterior P v₀ b ρ
  let B := LocalNativeBallCut.near P v₀ b r
  have hz := SelfCutEndpoints.cut_map_zero A B A
    (LocalNativeSupportedCap.exterior_open P v₀ b ρ) (LocalNativeSupportedCap.near_open P v₀ b r)
    (LocalNativeSupportedCap.cover P v₀ b hρr) n q
    (LocalNativeSupportedCap.cocycle n hn P v₀ b hρ)
    (LocalNativeSupportedCap.cocycle_supported n hn P v₀ b hρ)
    (LocalNativeSupportedCap.cocycle_supported n hn P v₀ b hρ)
    (SupportedCap.subspaceMap X A) (fun z => z.property)
  have hz' : (push (SupportedCap.subspaceMap X A)).f (n + q) ≫
      (LocalNativeSupportedCap.operation n hn P v₀ b hρ hρr).component q = 0 := hz
  change (push (SupportedCap.subspaceMap X A)).f (n + q) ≫
    ((LocalNativeSupportedCap.operation n hn P v₀ b hρ hρr).component q ≫ _) = 0
  rw [← Category.assoc, hz', zero_comp]

theorem parameter_exterior_zero (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1)) :
    cochainPullback (SupportedCap.subspaceMap (SelfCutThomCocycle.parameters (m + 1))
      (SupportedSelfCut.exterior (m + 1) ρ)) ((m + 1) + (m + (m + 1)))
      (NativeUnitParameterCochain.cochain m hρ hρr hr a) = 0 := by
  let X := SelfCutThomCocycle.parameters (m + 1)
  let A := SupportedSelfCut.exterior (m + 1) ρ
  have hz := SelfCutEndpoints.cut_map_zero A (SupportedSelfCut.neighborhood (m + 1) r) A
    (SupportedSelfCut.exterior_open (m + 1) ρ) (SupportedSelfCut.neighborhood_open (m + 1) r)
    (SupportedSelfCut.cover (m + 1) hρr) (m + 1) (m + (m + 1))
    (NormalizedSelfCut.cocycle (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hρ)
    (SupportedCap.subspaceMap X A) (fun z => z.property)
  have hz' : (push (SupportedCap.subspaceMap X A)).f ((m + 1) + (m + (m + 1))) ≫
      (NormalizedSelfCut.operation (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hρ hρr).component (m + (m + 1)) = 0 := hz
  change (push (SupportedCap.subspaceMap X A)).f _ ≫
    ((NormalizedSelfCut.operation (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hρ hρr).component (m + (m + 1)) ≫ _) = 0
  rw [← Category.assoc, hz', zero_comp]

theorem original_exterior_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1)) :
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀)
      (LocalNativeSupportedCap.exterior P v₀ b ρ)) ((m + 1) + (m + (m + 1)))
      (LocalOriginalRelativeOutputClass.original m P v₀ b hρ hρr hr a) = 0 :=
  pullback_support (LocalNativeBallCut.cutParameters P v₀ b) _ _ (fun _ h => h) _ _
    (parameter_exterior_zero m hρ hρr hr a)

theorem correction_exterior_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1)) :
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀)
      (LocalNativeSupportedCap.exterior P v₀ b ρ)) ((m + 1) + (m + m))
      (LocalRelativeOutputCapBoundary.correction m hm P v₀ b hρ hρr a) = 0 :=
  local_exterior_zero (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) P v₀ b hρ hρr (m + m) _

end
end Finsler.LocalRelativeOutputCapSupport
