module

public import Finsler.Loop.WholeSelfCutComplement
public import Finsler.Loop.NativeComplementMatchingPairings

/-! The actual wrapped matching branch is the ORIGINAL native cut
followed by the genuine strong-H1 complement. Its cut is 1 minus the
original difference and its loop is rotated to the LATER meridian time.
This gives exact native wrapped coordinates without constructing a
second redundant source-space family or comparing expanded H1 graphs. -/
@[expose] public section
namespace Finsler.NativeWrappedMatchingLoci
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.NativeMeridianMatchingLoci
open Finsler.SobolevShift Finsler.SobolevCircleAction
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 700000

def laterTime (b : Fin 3) (s : ClosedInterval) : ClosedInterval :=
  ⟨legClock (pairRight b) s, legClock_mem _ _⟩

def wrappedCut {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    parameters P ⟶ SelfCutThomCocycle.parameters n :=
  NativeMeridianMatchingLoci.intoCut P v₀ b ≫ WholeSelfCutComplement.complement n

theorem wrapped_time_interior {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : parameters P) :
    0 < ((wrappedCut P v₀ b z).1 : ℝ) ∧ ((wrappedCut P v₀ b z).1 : ℝ) < 1 := by
  have ht := cutTime_interior b z.1
  change 0 < 1 - (cutTime b z.1 : ℝ) ∧ 1 - (cutTime b z.1 : ℝ) < 1
  exact ⟨sub_pos.mpr ht.2, sub_lt_self 1 ht.1⟩

theorem wrapped_loop {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : parameters P) :
    (wrappedCut P v₀ b z).2 =
      shiftSphere (NativeH1TripleMeridian.native P v₀ (repeated b z.2.1 z.2.2)) (laterTime b z.1 : ℝ) := by
  let U : SphereLoop n := NativeH1TripleMeridian.native P v₀ (repeated b z.2.1 z.2.2)
  have h := shiftSphere_add U (legClock (pairRight b) z.1 - legClock (pairLeft b) z.1)
    (legClock (pairLeft b) z.1)
  have hs := h.trans (congrArg (shiftSphere U)
    (sub_add_cancel (legClock (pairRight b) z.1) (legClock (pairLeft b) z.1)))
  exact hs

theorem wrapped_selfEvaluation (n : ℕ) (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : parameters P) :
    SelfCutThomCocycle.selfEvaluation n (wrappedCut P v₀ b z) =
      (meridian P z.2.1 z.1, meridian P z.2.1 z.1) := by
  have hs := ConcreteCategory.congr_hom (WholeSelfCutComplement.selfEvaluation_exchange n)
    (NativeMeridianMatchingLoci.intoCut P v₀ b z)
  exact hs.trans (congrArg Prod.swap (selfEvaluation n P v₀ b z))

theorem reverse_diagonal_parameter {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    NativeComplementMatchingPairings.reverseDiagonal P v₀ b ≫ WholeSelfCutComplement.diagonalInclusion n =
      wrappedCut P v₀ b := by
  ext z : 1
  rfl

end
end Finsler.NativeWrappedMatchingLoci
