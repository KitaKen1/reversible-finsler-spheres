module

public import Finsler.Loop.LocalRelativeOutputSplitCup
public import Finsler.Loop.LocalNativeSupportedCap

/-! Carry the new arbitrary-relative-output split primitive through
the REAL source-local first normalized Thom cap. Its complete original
tested/retained scalar cochain is an actual coboundary. Global support
and boundary-face comparison are deliberately separate obligations. -/
@[expose] public section
namespace Finsler.LocalRelativeOutputCapBoundary
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

def cochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1)) :=
  LocalNativeSupportedCap.cochain (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) P v₀ b hρ hρr (m + (m + 1))
    (LocalRelativeOutputSplitCup.split m P v₀ b a)

def correction (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1)) :=
  LocalNativeSupportedCap.cochain (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) P v₀ b hρ hρr (m + m)
    (LocalRelativeOutputSplitCup.primitive m P v₀ b a hm)

variable (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
  (hρ : 0 < ρ) (hρr : ρ < r) (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1))

theorem boundary : cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) ((m + 1) + (m + m))
    (correction m hm P v₀ b hρ hρr a) = cochain m P v₀ b hρ hρr a := by
  have hd : cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) (m + m)
      (LocalRelativeOutputSplitCup.primitive m P v₀ b a hm) = LocalRelativeOutputSplitCup.split m P v₀ b a :=
    LocalRelativeOutputSplitCup.primitive_d m P v₀ b a hm
  rw [correction, LocalNativeSupportedCap.cochain_boundary, hd]
  rfl

include hm in
theorem closed : cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) ((m + 1) + (m + (m + 1)))
    (cochain m P v₀ b hρ hρr a) = 0 := by
  rw [← boundary m hm P v₀ b hρ hρr a]
  exact CochainClass.closed_boundary (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) ((m + 1) + (m + m)) ((m + 1) + (m + (m + 1))) _

theorem class_zero : CochainClass.classOf (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) ((m + 1) + (m + (m + 1)))
    (cochain m P v₀ b hρ hρr a) (closed m hm P v₀ b hρ hρr a) = 0 := by
  have he := boundary m hm P v₀ b hρ hρr a
  have hc := CochainClass.closed_boundary (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) ((m + 1) + (m + m)) ((m + 1) + (m + (m + 1)))
    (correction m hm P v₀ b hρ hρr a)
  exact (CochainClass.classOf_congr _ _ he.symm _ hc).trans
    (CochainClass.classOf_boundary _ ((m + 1) + (m + m)) ((m + 1) + (m + (m + 1))) _ hc)

end
end Finsler.LocalRelativeOutputCapBoundary
