module

public import Finsler.Loop.LocalNativeWrappedBallCut
public import Finsler.Loop.LocalNativeBallPrimitive

/-! The actual wrapped tested cocycle on the WHOLE ball product has
remaining class on adjacent branches and zero on the nonadjacent one.
Construct a genuine coboundary primitive to these explicit cocycles.
This is the tested correction needed for a later supported full cap;
no support property of this primitive is silently asserted. -/
@[expose] public section
namespace Finsler.LocalNativeWrappedBallPrimitive
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def reducedClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    cohomologyZMod2 (LocalNativeBallCut.space P v₀) m :=
  if b = 1 then 0 else
    (cohPullback (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))) m).hom
      (LocalNativeBallPrimitive.remainingClass m P v₀)

theorem ordinary_tested_class (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    (cohPullback (LocalNativeWrappedBallCut.tested P v₀ b) m).hom (MeridianLoopClass.ordinaryTransgression m) =
      reducedClass m P v₀ b := by
  have he := LocalNativeWrappedBallCut.paired_transgression P v₀ b m (SphereTopClass.topClass (m + 1) (by omega))
  change (cohPullback (LocalNativeBallCut.tested P v₀ b) m).hom (MeridianLoopClass.ordinaryTransgression m) +
    (cohPullback (LocalNativeWrappedBallCut.tested P v₀ b) m).hom (MeridianLoopClass.ordinaryTransgression m) =
    (cohPullback (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))) m).hom
      (LocalNativeBallPrimitive.remainingClass m P v₀) at he
  let F : Fin 3 → cohomologyZMod2 (LocalNativeBallCut.space P v₀) m := fun c =>
    (cohPullback (LocalNativeBallCut.tested P v₀ c) m).hom (MeridianLoopClass.ordinaryTransgression m)
  let W : Fin 3 → cohomologyZMod2 (LocalNativeBallCut.space P v₀) m := fun c =>
    (cohPullback (LocalNativeWrappedBallCut.tested P v₀ c) m).hom (MeridianLoopClass.ordinaryTransgression m)
  let R := (cohPullback (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))) m).hom
    (LocalNativeBallPrimitive.remainingClass m P v₀)
  fin_cases b
  · change F 0 + W 0 = R at he
    change W 0 = R
    have hf : F 0 = 0 := LocalNativeBallSlice.adjacent01_zero P v₀ m (by omega) _
    rw [hf, zero_add] at he
    exact he
  · change F 1 + W 1 = R at he
    change W 1 = 0
    have hf : F 1 = R := LocalNativeBallSlice.nonadjacent_reduced m hm P v₀
    rw [hf] at he
    exact add_left_cancel (he.trans (add_zero _).symm)
  · change F 2 + W 2 = R at he
    change W 2 = R
    have hf : F 2 = 0 := LocalNativeBallSlice.adjacent12_zero P v₀ m (by omega) _
    rw [hf, zero_add] at he
    exact he

def testedCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :=
  cochainPullback (LocalNativeWrappedBallCut.testedH1 P v₀ b) m
    (classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m))

theorem tested_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) m (testedCocycle m P v₀ b) = 0 :=
  cochainPullback_cocycle (LocalNativeWrappedBallCut.testedH1 P v₀ b) m _ (classRepr_isCocycle _ m _)

def reducedCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) m :=
  if b = 1 then 0 else LocalNativeBallPrimitive.remainingCocycle m P v₀

theorem reduced_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) m (reducedCocycle m P v₀ b) = 0 := by
  by_cases hb : b = 1
  · simp only [reducedCocycle, ite_eq_left hb]
    exact map_zero _
  · simpa only [reducedCocycle, ite_eq_right hb] using LocalNativeBallPrimitive.remaining_closed m P v₀

theorem reduced_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    CochainClass.classOf (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) m
      (reducedCocycle m P v₀ b) (reduced_closed m P v₀ b) = reducedClass m P v₀ b := by
  by_cases hb : b = 1
  · rw [reducedClass, ite_eq_left hb]
    have he : reducedCocycle m P v₀ b = 0 := ite_eq_left hb
    have hz : cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) m 0 = 0 := map_zero _
    exact (CochainClass.classOf_congr _ m he _ hz).trans (CochainClass.classOf_zero _ m hz)
  · rw [reducedClass, ite_eq_right hb]
    have he : reducedCocycle m P v₀ b = LocalNativeBallPrimitive.remainingCocycle m P v₀ := ite_eq_right hb
    exact (CochainClass.classOf_congr _ m he _ _).trans (LocalNativeBallPrimitive.remaining_class m P v₀)

theorem tested_class (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    CochainClass.classOf (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) m
      (testedCocycle m P v₀ b) (tested_closed m P v₀ b) = reducedClass m P v₀ b := by
  have he := CochainClass.classOf_map (cochainCxZMod2 (Loops (m + 1)))
    (singularCochainComplexZMod2.map (LocalNativeWrappedBallCut.testedH1 P v₀ b).op) m
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) (classRepr_isCocycle _ m _) (tested_closed m P v₀ b)
  change (cohPullback (LocalNativeWrappedBallCut.testedH1 P v₀ b) m).hom
    (CochainClass.classOf (cochainCxZMod2 (Loops (m + 1))) m (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) _) = _ at he
  rw [LocalNativeBallPrimitive.classOf_classRepr] at he
  have hg := congrArg (cohPullback (LocalNativeWrappedBallCut.testedH1 P v₀ b) m).hom (LocalNativeBallPrimitive.H1_class m)
  have hc := NativeMatchingTransgression.pullback_comp (LocalNativeWrappedBallCut.testedH1 P v₀ b)
    (ContinuousLoopModel.inclusion (m + 1)) m (MeridianLoopClass.ordinaryTransgression m)
  exact he.symm.trans (hg.trans (hc.symm.trans (ordinary_tested_class m hm P v₀ b)))

def primitive (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :=
  CochainClassExact.primitive (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) m hm
    (testedCocycle m P v₀ b) (reducedCocycle m P v₀ b) (tested_closed m P v₀ b) (reduced_closed m P v₀ b)
      ((tested_class m hm P v₀ b).trans (reduced_class m P v₀ b).symm)

theorem primitive_d (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    ((cochainCxZMod2 (LocalNativeBallCut.space P v₀)).d (m - 1) m).hom (primitive m hm P v₀ b) =
      testedCocycle m P v₀ b - reducedCocycle m P v₀ b :=
  CochainClassExact.primitive_d (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) m hm
    (testedCocycle m P v₀ b) (reducedCocycle m P v₀ b) (tested_closed m P v₀ b) (reduced_closed m P v₀ b)
      ((tested_class m hm P v₀ b).trans (reduced_class m P v₀ b).symm)

end
end Finsler.LocalNativeWrappedBallPrimitive
