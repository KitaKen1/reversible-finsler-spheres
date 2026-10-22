module

public import Finsler.Loop.LocalNativeBallPrimitive
public import Finsler.Loop.NormalizedCupBoundary
public import Finsler.Loop.LocalizedSphereTopCocycle

/-! Cup the ACTUAL tested cochain primitive with the ORIGINAL
localized evaluation cocycle. This gives an EXPLICIT boundary for
the local split cup, and literal correction-zero on all real near
families whose first OR second point is far from Q. No correction
support after the original Thom cap is assumed. -/
@[expose] public section
namespace Finsler.LocalNativeBallCupCorrection
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.IntervalSobolev
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def firstPoint {n : ℕ} (P : Sphere n) (v₀ : equator P) : LocalNativeBallCut.space P v₀ ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun z => z.1.val, continuous_subtype_val.comp continuous_fst⟩

def evaluationCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η) :=
  cochainPullback (firstPoint P v₀) (m + 1)
    (LocalizedSphereTopCocycle.cocycle (m + 1) (by omega) (LocalNativeBallCut.center P v₀) hη)

theorem evaluation_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) (m + 1) (evaluationCocycle m P v₀ hη) = 0 :=
  cochainPullback_cocycle (firstPoint P v₀) (m + 1) _ (LocalizedSphereTopCocycle.closed (m + 1) (by omega) _ hη)

theorem evaluation_far_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η)
    {X : TopCat.{0}} (f : X ⟶ LocalNativeBallCut.space P v₀)
    (hf : ∀ x, η ≤ ‖((f x).1.val : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1))‖) :
    cochainPullback f (m + 1) (evaluationCocycle m P v₀ hη) = 0 := by
  rw [evaluationCocycle, ← Finsler.SupportedCapNaturality.pullback_comp]
  exact LocalizedSphereTopCocycle.pullback_far_zero (by omega) (LocalNativeBallCut.center P v₀) hη (f ≫ firstPoint P v₀) hf

def correction (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {η : ℝ} (hη : 0 < η) :=
  CupOne.cup (LocalNativeBallCut.space P v₀) (m - 1) (m + 1) ((m - 1) + (m + 1)) rfl
    (LocalNativeBallPrimitive.primitive m hm P v₀ b) (evaluationCocycle m P v₀ hη)

theorem correction_boundary (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {η : ℝ} (hη : 0 < η) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) ((m - 1) + (m + 1)) (correction m hm P v₀ b hη) =
      CupOne.cup (LocalNativeBallCut.space P v₀) m (m + 1) (((m - 1) + (m + 1)) + 1) (by omega)
        (LocalNativeBallPrimitive.testedCocycle m P v₀ b) (evaluationCocycle m P v₀ hη) -
      CupOne.cup (LocalNativeBallCut.space P v₀) m (m + 1) (((m - 1) + (m + 1)) + 1) (by omega)
        (LocalNativeBallPrimitive.reducedCocycle m P v₀ b) (evaluationCocycle m P v₀ hη) := by
  cases m with
  | zero => omega
  | succ k =>
    have hp := LocalNativeBallPrimitive.primitive_d (k + 1) hm P v₀ b
    change cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) k (LocalNativeBallPrimitive.primitive (k + 1) hm P v₀ b) = _ at hp
    have hb := NormalizedCupBoundary.boundary_right_closed (LocalNativeBallCut.space P v₀) k (k + 2) (k + (k + 2)) rfl
      (LocalNativeBallPrimitive.primitive (k + 1) hm P v₀ b) (evaluationCocycle (k + 1) P v₀ hη) (evaluation_closed (k + 1) P v₀ hη)
    rw [hp, NormalizedCupBoundary.cup_sub_left] at hb
    exact hb

theorem correction_far_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {η : ℝ} (hη : 0 < η)
    {X : TopCat.{0}} (f : X ⟶ LocalNativeBallCut.space P v₀)
    (hf : ∀ x, η ≤ ‖((f x).1.val : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1))‖) :
    cochainPullback f ((m - 1) + (m + 1)) (correction m hm P v₀ b hη) = 0 :=
  CupCapOrder.restriction_zero f (m - 1) (m + 1) _ rfl _ _ (Or.inr (evaluation_far_zero m P v₀ hη f hf))

theorem near_distance {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {r : ℝ}
    (z : LocalNativeBallCut.near P v₀ b r) : ‖(z.val.2.1.val : Ambient n) - z.val.1.val‖ < r := by
  have he := LocalNativeBallCut.self_evaluation P v₀ b z.val
  have hl := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  change H1FiberBase.point (LocalNativeBallCut.cutParameters P v₀ b z.val).2 = z.val.1.val at hl
  change H1SelfCutNeighborhood.endpoint (LocalNativeBallCut.cutParameters P v₀ b z.val) = z.val.2.1.val at hr
  have hz := z.property
  change ‖(H1SelfCutNeighborhood.endpoint (LocalNativeBallCut.cutParameters P v₀ b z.val) : Ambient n) -
    (H1FiberBase.point (LocalNativeBallCut.cutParameters P v₀ b z.val).2 : Ambient n)‖ < r at hz
  rw [hl, hr] at hz
  exact hz

theorem near_either_far_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3)
    {η r D : ℝ} (hη : 0 < η) (hηr : η + r ≤ D) {X : TopCat.{0}}
    (f : X ⟶ TopCat.of (LocalNativeBallCut.near P v₀ b r))
    (hf : ∀ x, D ≤ ‖((f x).val.1.val : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1))‖ ∨
      D ≤ ‖((f x).val.2.1.val : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1))‖) :
    cochainPullback (f ≫ SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (LocalNativeBallCut.near P v₀ b r))
      ((m - 1) + (m + 1)) (correction m hm P v₀ b hη) = 0 := by
  apply correction_far_zero m hm P v₀ b hη
  intro x
  have hrx := near_distance P v₀ b (f x)
  rcases hf x with h | h
  · have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg _) hrx
    change η ≤ ‖((f x).val.1.val : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1))‖
    linarith
  · have he := norm_sub_le ((f x).val.2.1.val : Ambient (m + 1)) ((f x).val.1.val : Ambient (m + 1))
    have ht := norm_add_le (((f x).val.2.1.val : Ambient (m + 1)) - (f x).val.1.val)
      (((f x).val.1.val : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1)))
    have hh : (((f x).val.2.1.val : Ambient (m + 1)) - (f x).val.1.val) +
      (((f x).val.1.val : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1))) =
        ((f x).val.2.1.val : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1)) := by abel
    rw [hh] at ht
    change η ≤ ‖((f x).val.1.val : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1))‖
    linarith

end
end Finsler.LocalNativeBallCupCorrection
