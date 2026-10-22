module

public import Finsler.Loop.LocalRetainedOutputPrimitive
public import Finsler.Loop.LocalNativeBallPrimitive
public import Finsler.Loop.GeometricTimeCupCochain

/-! The ORIGINAL tested factor and a TRUE arbitrary relative output
give an exact split cup on every actual whole-ball native cut chart.
Adjacent branches use their tested primitive; the nonadjacent branch
uses its retained-output primitive. This local statement does not
assert global relative boundary/support compatibility or UNIT. -/
@[expose] public section
namespace Finsler.LocalRelativeOutputSplitCup
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

variable (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3)
  (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1))

def output : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) (m + 1) :=
  cochainPullback (LocalNativeBallCut.retainedH1 P v₀ b) (m + 1) (ConstantRelativeOutputCochain.cochain (m + 1) (m + 1) a)

theorem output_closed : cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) (m + 1) (output m P v₀ b a) = 0 :=
  pullback_closed _ _ _ (ConstantRelativeOutputCochain.closed (m + 1) (m + 1) a)

def split : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) (m + (m + 1)) :=
  cochainCup m (m + 1) (LocalNativeBallPrimitive.testedCocycle m P v₀ b) (output m P v₀ b a)

theorem closed : cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) (m + (m + 1)) (split m P v₀ b a) = 0 :=
  cochainCupZMod2_respects_cocycles m (m + 1) _ _ (LocalNativeBallPrimitive.tested_closed m P v₀ b) (output_closed m P v₀ b a)

theorem class_zero (hm : 1 ≤ m) :
    CochainClass.classOf (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) (m + (m + 1)) (split m P v₀ b a) (closed m P v₀ b a) = 0 := by
  have he := (cupZMod2_mk (LocalNativeBallPrimitive.testedCocycle m P v₀ b)
    (LocalNativeBallPrimitive.tested_closed m P v₀ b) (output m P v₀ b a) (output_closed m P v₀ b a)).symm
  have ht := LocalNativeBallPrimitive.tested_class m hm P v₀ b
  change cocycleClass _ m (LocalNativeBallPrimitive.testedCocycle m P v₀ b) (LocalNativeBallPrimitive.tested_closed m P v₀ b) =
    LocalNativeBallPrimitive.reducedClass m P v₀ b at ht
  rw [ht] at he
  by_cases hb : b = 1
  · subst b
    have hz := LocalRetainedOutputPrimitive.class_zero P v₀ (m + 1)
      (ConstantRelativeOutputCochain.cochain (m + 1) (m + 1) a) (ConstantRelativeOutputCochain.closed (m + 1) (m + 1) a) (by omega)
    change cocycleClass _ (m + 1) (output m P v₀ 1 a) (output_closed m P v₀ 1 a) = 0 at hz
    rw [hz, Finsler.Cup.cup_zero] at he
    exact he
  · have hz : LocalNativeBallPrimitive.reducedClass m P v₀ b = 0 := by
      simp only [LocalNativeBallPrimitive.reducedClass, hb, ite_false]
    rw [hz, Finsler.Cup.zero_cup] at he
    exact he

def primitive (hm : 1 ≤ m) : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) (m + (m + 1) - 1) :=
  CochainClassExact.primitive (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) (m + (m + 1)) (by omega)
    (split m P v₀ b a) 0 (closed m P v₀ b a) (map_zero _)
    ((class_zero m P v₀ b a hm).trans (CochainClass.classOf_zero _ _ (map_zero _)).symm)

theorem primitive_d (hm : 1 ≤ m) :
    ((cochainCxZMod2 (LocalNativeBallCut.space P v₀)).d (m + (m + 1) - 1) (m + (m + 1))).hom (primitive m P v₀ b a hm) =
      split m P v₀ b a := by
  have he := CochainClassExact.primitive_d (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) (m + (m + 1)) (by omega)
    (split m P v₀ b a) 0 (closed m P v₀ b a) (map_zero _)
    ((class_zero m P v₀ b a hm).trans (CochainClass.classOf_zero _ _ (map_zero _)).symm)
  exact he.trans (sub_zero _)

theorem original_near_equality {r : ℝ} (hr : r ≤ 1) :
    cochainPullback (LocalNativeBallCut.toNeighborhood P v₀ b r) (m + (m + 1))
      (GeometricTimeCupCochain.splitCup m m hr (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) (m + 1)
        (ConstantRelativeOutputCochain.cochain (m + 1) (m + 1) a)) =
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (LocalNativeBallCut.near P v₀ b r)) (m + (m + 1))
      (split m P v₀ b a) := by
  rw [GeometricTimeCupCochain.splitCup, NormalizedSelfCut.testedCocycle, split, output, LocalNativeBallPrimitive.testedCocycle,
    cochainCup_naturality, cochainCup_naturality, ← pullback_comp, ← pullback_comp, ← pullback_comp, ← pullback_comp,
    ← LocalNativeBallCut.tested_restrict P v₀ b hr, ← LocalNativeBallCut.retained_restrict P v₀ b hr]

end
end Finsler.LocalRelativeOutputSplitCup
