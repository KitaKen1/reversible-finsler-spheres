module

public import Finsler.Loop.LocalRelativeOutputCapSupport
public import Finsler.Loop.SmallChainPrimitiveCorrection

/-! An actual exterior-supported primitive for the ORIGINAL ambient
complete first cap on each whole-ball chart. Source-small cap
naturality is corrected by the actual subdivision prism. This is
local to the chart, with no assertion about gluing different charts. -/
@[expose] public section
namespace Finsler.LocalOriginalRelativeOutputPrimitive
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

def sourceCover {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (ρ r : ℝ) :=
  SupportedCap.cover (LocalNativeBallCut.space P v₀)
    (LocalNativeSupportedCap.exterior P v₀ b ρ) (LocalNativeBallCut.near P v₀ b r)

theorem sourceCover_open {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (ρ r : ℝ) :
    ∀ i, IsOpen (sourceCover P v₀ b ρ r i) :=
  SupportedCap.cover_open _ _ _ (LocalNativeSupportedCap.exterior_open P v₀ b ρ)
    (LocalNativeSupportedCap.near_open P v₀ b r)

theorem sourceCover_univ {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ} (hρr : ρ < r) :
    ⋃ i, sourceCover P v₀ b ρ r i = Set.univ :=
  SupportedCap.cover_univ _ _ _ (LocalNativeSupportedCap.cover P v₀ b hρr)

variable (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
  (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1))

theorem small_boundary :
    (SmallChainCarrier.inclusion (LocalNativeBallCut.space P v₀) (sourceCover P v₀ b ρ r)).f
      ((m + 1) + (m + (m + 1))) ≫ LocalOriginalRelativeOutputClass.original m P v₀ b hρ hρr hr a =
    (SmallChainCarrier.inclusion (LocalNativeBallCut.space P v₀) (sourceCover P v₀ b ρ r)).f
      ((m + 1) + (m + (m + 1))) ≫
      cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) ((m + 1) + (m + m))
        (LocalRelativeOutputCapBoundary.correction m hm P v₀ b hρ hρr a) := by
  let f := LocalNativeBallCut.cutParameters P v₀ b
  let A := LocalNativeSupportedCap.exterior P v₀ b ρ
  let B := LocalNativeBallCut.near P v₀ b r
  let C := SupportedSelfCut.exterior (m + 1) ρ
  let D := SupportedSelfCut.neighborhood (m + 1) r
  let hA := LocalNativeSupportedCap.exterior_open P v₀ b ρ
  let hB := LocalNativeSupportedCap.near_open P v₀ b r
  let hC := SupportedSelfCut.exterior_open (m + 1) ρ
  let hD := SupportedSelfCut.neighborhood_open (m + 1) r
  let hcX := LocalNativeSupportedCap.cover P v₀ b hρr
  let hcY := SupportedSelfCut.cover (m + 1) hρr
  let τ := NormalizedSelfCut.cocycle (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hρ
  let hsτ := NormalizedSelfCut.cocycle_supported (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hρ
  let ψ := NativeUnitParameterCochain.output m hr a
  have he := SupportedCapPullbackClass.small_equality f A B C D hA hB hcX hC hD hcY
    (fun _ h => h) (fun _ h => h) (m + 1) (m + (m + 1)) τ hsτ ψ
  have hf : restriction f B D (fun _ h => h) = LocalNativeBallCut.toNeighborhood P v₀ b r := by ext z : 1; rfl
  have hψnear : cochainPullback (restriction f B D (fun _ h => h)) (m + (m + 1)) ψ =
      cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) (m + (m + 1))
        (LocalRelativeOutputSplitCup.split m P v₀ b a) := by
    rw [hf]
    exact LocalRelativeOutputSplitCup.original_near_equality m P v₀ b a hr
  have hc : SupportedCapPullbackClass.localCochain f A B C D hA hB hcX (fun _ h => h) (fun _ h => h)
      (m + 1) (m + (m + 1)) τ hsτ ψ = LocalRelativeOutputCapBoundary.cochain m P v₀ b hρ hρr a := by
    unfold SupportedCapPullbackClass.localCochain
    rw [hψnear]
    rfl
  rw [hc] at he
  change _ = _ ≫ LocalRelativeOutputCapBoundary.cochain m P v₀ b hρ hρr a at he
  rw [LocalRelativeOutputCapBoundary.boundary m hm P v₀ b hρ hρr a]
  exact he

def primitive : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) ((m + 1) + (m + m)) :=
  SmallChainPrimitiveCorrection.primitive (sourceCover P v₀ b ρ r) ((m + 1) + (m + m))
    (LocalOriginalRelativeOutputClass.original m P v₀ b hρ hρr hr a)
    (LocalRelativeOutputCapBoundary.correction m hm P v₀ b hρ hρr a)

theorem primitive_boundary :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) ((m + 1) + (m + m))
      (primitive m hm P v₀ b hρ hρr hr a) = LocalOriginalRelativeOutputClass.original m P v₀ b hρ hρr hr a :=
  SmallChainPrimitiveCorrection.primitive_boundary (sourceCover P v₀ b ρ r) ((m + 1) + (m + m)) _ _
    (sourceCover_open P v₀ b ρ r) (sourceCover_univ P v₀ b hρr)
    (LocalOriginalRelativeOutputClass.closed m P v₀ b hρ hρr hr a)
    (small_boundary m hm P v₀ b hρ hρr hr a)

theorem primitive_exterior_zero :
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀)
      (LocalNativeSupportedCap.exterior P v₀ b ρ)) ((m + 1) + (m + m))
      (primitive m hm P v₀ b hρ hρr hr a) = 0 :=
  SmallChainPrimitiveCorrection.primitive_support_zero (sourceCover P v₀ b ρ r) ((m + 1) + (m + m)) _ _
    (LocalNativeSupportedCap.exterior P v₀ b ρ)
    (LocalRelativeOutputCapSupport.original_exterior_zero m P v₀ b hρ hρr hr a)
    (LocalRelativeOutputCapSupport.correction_exterior_zero m hm P v₀ b hρ hρr a)

end
end Finsler.LocalOriginalRelativeOutputPrimitive
