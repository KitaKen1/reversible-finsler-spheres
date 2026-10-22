module

public import Finsler.Loop.StraightenedWrappedBallSplit

/-! Pull the ACTUAL wrapped tested primitive through the actual
ball-point exchange. Remaining cocycles are literally unchanged.
The result is a real primitive for the actual straightened tested
cochain and the explicit remaining/zero/remaining reduced cocycle. -/
@[expose] public section
namespace Finsler.StraightenedWrappedBallPrimitive
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.BorelLoop Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def testedCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :=
  cochainPullback (StraightenedWrappedBallSplit.testedH1 P v₀ b) m
    (classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m))

abbrev reducedCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :=
  LocalNativeWrappedBallPrimitive.reducedCocycle m P v₀ b

theorem tested_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    cochainPullback (NativeCutPointSwap.ballSwap P v₀) m (LocalNativeWrappedBallPrimitive.testedCocycle m P v₀ b) =
      testedCocycle m P v₀ b :=
  (pullback_comp (NativeCutPointSwap.ballSwap P v₀) (LocalNativeWrappedBallCut.testedH1 P v₀ b) m
    (classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m))).symm

theorem remaining_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    cochainPullback (NativeCutPointSwap.ballSwap P v₀) m (LocalNativeBallPrimitive.remainingCocycle m P v₀) =
      LocalNativeBallPrimitive.remainingCocycle m P v₀ := by
  have hs : NativeCutPointSwap.ballSwap P v₀ ≫
      SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P)) =
      SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P)) := rfl
  unfold LocalNativeBallPrimitive.remainingCocycle
  rw [← pullback_comp, hs]

theorem reduced_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    cochainPullback (NativeCutPointSwap.ballSwap P v₀) m (LocalNativeWrappedBallPrimitive.reducedCocycle m P v₀ b) =
      reducedCocycle m P v₀ b := by
  by_cases hb : b = 1
  · simp only [LocalNativeWrappedBallPrimitive.reducedCocycle, reducedCocycle, ite_eq_left hb]
    exact map_zero _
  · simpa only [LocalNativeWrappedBallPrimitive.reducedCocycle, reducedCocycle, ite_eq_right hb] using remaining_pullback m P v₀

theorem tested_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) m (testedCocycle m P v₀ b) = 0 :=
  cochainPullback_cocycle (StraightenedWrappedBallSplit.testedH1 P v₀ b) m _ (classRepr_isCocycle _ m _)

theorem reduced_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) m (reducedCocycle m P v₀ b) = 0 :=
  LocalNativeWrappedBallPrimitive.reduced_closed m P v₀ b

def primitive (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :=
  cochainPullback (NativeCutPointSwap.ballSwap P v₀) (m - 1) (LocalNativeWrappedBallPrimitive.primitive m hm P v₀ b)

theorem primitive_d (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    ((cochainCxZMod2 (LocalNativeBallCut.space P v₀)).d (m - 1) m).hom (primitive m hm P v₀ b) =
      testedCocycle m P v₀ b - reducedCocycle m P v₀ b := by
  have hc := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (NativeCutPointSwap.ballSwap P v₀).op).comm (m - 1) m)
    (LocalNativeWrappedBallPrimitive.primitive m hm P v₀ b)
  change ((cochainCxZMod2 (LocalNativeBallCut.space P v₀)).d (m - 1) m).hom (primitive m hm P v₀ b) =
    cochainPullback (NativeCutPointSwap.ballSwap P v₀) m
      (((cochainCxZMod2 (LocalNativeBallCut.space P v₀)).d (m - 1) m).hom
        (LocalNativeWrappedBallPrimitive.primitive m hm P v₀ b)) at hc
  rw [LocalNativeWrappedBallPrimitive.primitive_d] at hc
  have hs := map_sub ((singularCochainComplexZMod2.map (NativeCutPointSwap.ballSwap P v₀).op).f m).hom
    (LocalNativeWrappedBallPrimitive.testedCocycle m P v₀ b) (LocalNativeWrappedBallPrimitive.reducedCocycle m P v₀ b)
  exact hc.trans (hs.trans (congrArg₂ (fun a b => a - b) (tested_pullback m P v₀ b) (reduced_pullback m P v₀ b)))

end
end Finsler.StraightenedWrappedBallPrimitive
