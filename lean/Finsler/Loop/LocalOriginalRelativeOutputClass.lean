module

public import Finsler.Loop.LocalRelativeOutputCapBoundary
public import Finsler.Loop.NativeUnitParameterCochain
public import Finsler.Loop.SupportedCapPullbackClass

/-! Return to the ORIGINAL ambient first-Thom cap on actual native
whole-ball charts, for EVERY genuine relative output. Actual source-
small naturality and subdivision compare it to the explicit exact
local cap. Only ABSOLUTE local class zero is proved here; the global
relative cut is the remaining UNIT obligation. -/
@[expose] public section
namespace Finsler.LocalOriginalRelativeOutputClass
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
  (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1))

def original : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) ((m + 1) + (m + (m + 1))) :=
  cochainPullback (LocalNativeBallCut.cutParameters P v₀ b) ((m + 1) + (m + (m + 1))) (NativeUnitParameterCochain.cochain m hρ hρr hr a)

theorem closed : cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) ((m + 1) + (m + (m + 1))) (original m P v₀ b hρ hρr hr a) = 0 :=
  pullback_closed _ _ _ (NativeUnitParameterCochain.closed m hρ hρr hr a)

theorem original_class_zero (hm : 1 ≤ m) :
    CochainClass.classOf (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) ((m + 1) + (m + (m + 1)))
      (original m P v₀ b hρ hρr hr a) (closed m P v₀ b hρ hρr hr a) = 0 := by
  let X := LocalNativeBallCut.space P v₀
  let Y := SelfCutThomCocycle.parameters (m + 1)
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
  let hτ := NormalizedSelfCut.cocycle_closed (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hρ
  let ψ := NativeUnitParameterCochain.output m hr a
  let hψ := NativeUnitParameterCochain.output_closed m hr a
  have he := SupportedCapPullbackClass.class_equality f A B C D hA hB hcX hC hD hcY
    (fun _ h => h) (fun _ h => h) (m + 1) (m + (m + 1)) τ hsτ hτ ψ hψ (by omega)
  have hf : restriction f B D (fun _ h => h) = LocalNativeBallCut.toNeighborhood P v₀ b r := by ext z : 1; rfl
  have hψnear : cochainPullback (restriction f B D (fun _ h => h)) (m + (m + 1)) ψ =
      cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) (m + (m + 1)) (LocalRelativeOutputSplitCup.split m P v₀ b a) := by
    rw [hf]
    exact LocalRelativeOutputSplitCup.original_near_equality m P v₀ b a hr
  have hc : SupportedCapPullbackClass.localCochain f A B C D hA hB hcX (fun _ h => h) (fun _ h => h)
      (m + 1) (m + (m + 1)) τ hsτ ψ = LocalRelativeOutputCapBoundary.cochain m P v₀ b hρ hρr a := by
    unfold SupportedCapPullbackClass.localCochain
    rw [hψnear]
    rfl
  have hclass := CochainClass.classOf_congr (cochainCxZMod2 X) ((m + 1) + (m + (m + 1))) hc
    (SupportedCapPullbackClass.local_closed f A B C D hA hB hcX (fun _ h => h) (fun _ h => h)
      (m + 1) (m + (m + 1)) τ hsτ hτ ψ hψ)
    (LocalRelativeOutputCapBoundary.closed m hm P v₀ b hρ hρr a)
  exact he.trans (hclass.trans (LocalRelativeOutputCapBoundary.class_zero m hm P v₀ b hρ hρr a))

end
end Finsler.LocalOriginalRelativeOutputClass
