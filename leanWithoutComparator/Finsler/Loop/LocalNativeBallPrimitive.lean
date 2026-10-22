module

public import Finsler.Loop.LocalNativeBallSlice
public import Finsler.Topology.CochainClassExact

/-! An ACTUAL local cochain primitive compares the SAME original
tested classRepr with zero on adjacent branches, and with a genuine
remaining-factor pulled-back primitive cocycle on the nonadjacent
branch. This supplies a real coboundary for the next supported
Thom/split-cup comparison; support of that correction is not assumed. -/
@[expose] public section
namespace Finsler.LocalNativeBallPrimitive
open CategoryTheory CategoryTheory.Limits SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem classOf_classRepr (X : TopCat.{0}) (q : ℕ) (a : cohomologyZMod2 X q) :
    CochainClass.classOf (cochainCxZMod2 X) q (classRepr X q a) (classRepr_isCocycle X q a) = a :=
  (CochainClass.classOf_iCycles (cochainCxZMod2 X) q (classCycleRepr X q a)).trans
    (homologyπ_classCycleRepr X q a)

theorem H1_class (m : ℕ) : MeridianLoopClass.H1TransgressionClass m =
    (cohPullback (ContinuousLoopModel.inclusion (m + 1)) m).hom (MeridianLoopClass.ordinaryTransgression m) := rfl

def remainingClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (cohPullback (ordinary P v₀) m).hom (MeridianLoopClass.ordinaryTransgression m)

def testedCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :=
  cochainPullback (LocalNativeBallCut.testedH1 P v₀ b) m (classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m))

theorem tested_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) m (testedCocycle m P v₀ b) = 0 :=
  cochainPullback_cocycle (LocalNativeBallCut.testedH1 P v₀ b) m _ (classRepr_isCocycle _ m _)

def remainingCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :=
  cochainPullback (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))) m
    (classRepr (TopCat.of (equator P)) m (remainingClass m P v₀))

theorem remaining_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) m (remainingCocycle m P v₀) = 0 :=
  cochainPullback_cocycle (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))) m _
    (classRepr_isCocycle _ m _)

def reducedClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    cohomologyZMod2 (LocalNativeBallCut.space P v₀) m :=
  if b = 1 then (cohPullback (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))) m).hom
    (remainingClass m P v₀) else 0

def reducedCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) m :=
  if b = 1 then remainingCocycle m P v₀ else 0

theorem reduced_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) m (reducedCocycle m P v₀ b) = 0 := by
  by_cases h : b = 1
  · simpa only [reducedCocycle, ite_eq_left h] using remaining_closed m P v₀
  · simp only [reducedCocycle, ite_eq_right h]
    exact map_zero _

theorem remaining_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    CochainClass.classOf (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) m
      (remainingCocycle m P v₀) (remaining_closed m P v₀) =
      (cohPullback (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))) m).hom
        (remainingClass m P v₀) := by
  have he := CochainClass.classOf_map (cochainCxZMod2 (TopCat.of (equator P)))
    (singularCochainComplexZMod2.map (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))).op)
    m (classRepr _ m (remainingClass m P v₀)) (classRepr_isCocycle _ m _) (remaining_closed m P v₀)
  change (cohPullback (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))) m).hom
    (CochainClass.classOf (cochainCxZMod2 (TopCat.of (equator P))) m (classRepr _ m (remainingClass m P v₀)) _) = _ at he
  rw [classOf_classRepr] at he
  exact he.symm

theorem reduced_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    CochainClass.classOf (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) m
      (reducedCocycle m P v₀ b) (reduced_closed m P v₀ b) = reducedClass m P v₀ b := by
  by_cases h : b = 1
  · rw [reducedClass, ite_eq_left h]
    have he : reducedCocycle m P v₀ b = remainingCocycle m P v₀ := ite_eq_left h
    exact (CochainClass.classOf_congr _ m he _ _).trans (remaining_class m P v₀)
  · rw [reducedClass, ite_eq_right h]
    have he : reducedCocycle m P v₀ b = 0 := ite_eq_right h
    have hz : cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) m 0 = 0 := map_zero _
    exact (CochainClass.classOf_congr _ m he _ hz).trans (CochainClass.classOf_zero _ m hz)

theorem tested_class (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) :
    CochainClass.classOf (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) m
      (testedCocycle m P v₀ b) (tested_closed m P v₀ b) = reducedClass m P v₀ b := by
  have he := CochainClass.classOf_map (cochainCxZMod2 (Loops (m + 1)))
    (singularCochainComplexZMod2.map (LocalNativeBallCut.testedH1 P v₀ b).op) m
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) (classRepr_isCocycle _ m _) (tested_closed m P v₀ b)
  change (cohPullback (LocalNativeBallCut.testedH1 P v₀ b) m).hom
    (CochainClass.classOf (cochainCxZMod2 (Loops (m + 1))) m (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) _) = _ at he
  rw [classOf_classRepr] at he
  have hg := congrArg (cohPullback (LocalNativeBallCut.testedH1 P v₀ b) m).hom (H1_class m)
  have hc := NativeMatchingTransgression.pullback_comp (LocalNativeBallCut.testedH1 P v₀ b)
    (ContinuousLoopModel.inclusion (m + 1)) m (MeridianLoopClass.ordinaryTransgression m)
  have hv : (cohPullback (LocalNativeBallCut.tested P v₀ b) m).hom (MeridianLoopClass.ordinaryTransgression m) =
      reducedClass m P v₀ b := by
    fin_cases b
    · exact LocalNativeBallSlice.adjacent01_zero P v₀ m (by omega) (MeridianLoopClass.ordinaryTransgression m)
    · exact LocalNativeBallSlice.nonadjacent_reduced m hm P v₀
    · exact LocalNativeBallSlice.adjacent12_zero P v₀ m (by omega) (MeridianLoopClass.ordinaryTransgression m)
  exact he.symm.trans (hg.trans (hc.symm.trans hv))

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
end Finsler.LocalNativeBallPrimitive
