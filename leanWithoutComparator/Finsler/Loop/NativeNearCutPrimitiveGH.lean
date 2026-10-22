module

public import Finsler.Loop.NativeNearCutTransgression
public import Finsler.Loop.NativeBVEvaluationTransgression

/-! An actual primitive for the difference between the source pullback
and the two ORIGINAL cut-output pullbacks of the SAME supported GH_0
cochain. This holds on the genuine fixed near tube. No time-face or
Thom-support property of this primitive is inferred from absolute exactness. -/
@[expose] public section
namespace Finsler.NativeNearCutPrimitiveGH
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.H1SelfCutNeighborhood Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.NativeNearCutRejoining
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def source (n : ℕ) : domain n ⟶ Loops n :=
  TopCat.ofHom ⟨fun z => z.val.2, by fun_prop⟩

def tested (n : ℕ) : domain n ⟶ Loops n :=
  TopCat.ofHom ⟨fun z => left (input z), continuous_left.comp (continuous_input n)⟩

def retained (n : ℕ) : domain n ⟶ Loops n :=
  TopCat.ofHom ⟨fun z => right (input z), continuous_right.comp (continuous_input n)⟩

theorem source_factor (n : ℕ) : source n ≫ ContinuousLoopModel.inclusion n =
    NativeNearCutTransgression.source n := rfl

theorem tested_factor (n : ℕ) : tested n ≫ ContinuousLoopModel.inclusion n =
    NativeNearCutTransgression.tested n := rfl

theorem retained_factor (n : ℕ) : retained n ≫ ContinuousLoopModel.inclusion n =
    NativeNearCutTransgression.retained n := rfl

theorem H1_transgression_split (n q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (source n) q).hom (ContinuousLoopSweep.H1Transgression n q a) =
      (cohPullback (tested n) q).hom (ContinuousLoopSweep.H1Transgression n q a) +
      (cohPullback (retained n) q).hom (ContinuousLoopSweep.H1Transgression n q a) := by
  change (cohPullback (source n) q).hom
      ((cohPullback (ContinuousLoopModel.inclusion n) q).hom (ContinuousLoopSweep.transgression n q a)) =
    (cohPullback (tested n) q).hom
      ((cohPullback (ContinuousLoopModel.inclusion n) q).hom (ContinuousLoopSweep.transgression n q a)) +
    (cohPullback (retained n) q).hom
      ((cohPullback (ContinuousLoopModel.inclusion n) q).hom (ContinuousLoopSweep.transgression n q a))
  rw [← Cup.pullback_comp, ← Cup.pullback_comp, ← Cup.pullback_comp,
    source_factor, tested_factor, retained_factor]
  exact NativeNearCutTransgression.original_transgression_split n q a

theorem primitive_class_split (m : ℕ) :
    (cohPullback (source (m + 1)) m).hom (NativeGHPowers.power m 0) =
      (cohPullback (tested (m + 1)) m).hom (NativeGHPowers.power m 0) +
      (cohPullback (retained (m + 1)) m).hom (NativeGHPowers.power m 0) :=
  H1_transgression_split (m + 1) m (SphereTopClass.topClass (m + 1) (by omega))

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

def original : singularCochainGroup (ZMod 2) (Loops (m + 1)) m :=
  NativeClosingArcPowerVanishing.powerCocycle m hm F 0

theorem original_closed : cochainCoboundary (ZMod 2) _ m (original m hm F) = 0 :=
  NativeClosingArcPowerVanishing.powerCocycle_closed m hm F 0

theorem original_class : cocycleClass _ m (original m hm F) (original_closed m hm F) =
    NativeGHPowers.power m 0 := NativeClosingArcPowerVanishing.powerCocycle_class m hm F 0

def before : singularCochainGroup (ZMod 2) (domain (m + 1)) m :=
  cochainPullback (source (m + 1)) m (original m hm F)

def after : singularCochainGroup (ZMod 2) (domain (m + 1)) m :=
  cochainPullback (tested (m + 1)) m (original m hm F) +
    cochainPullback (retained (m + 1)) m (original m hm F)

theorem before_closed : cochainCoboundary (ZMod 2) _ m (before m hm F) = 0 :=
  cochainPullback_cocycle _ _ _ (original_closed m hm F)

theorem after_closed : cochainCoboundary (ZMod 2) _ m (after m hm F) = 0 := by
  change ((cochainCxZMod2 (domain (m + 1))).d m (m + 1)).hom (_ + _) = 0
  rw [map_add]
  exact (congrArg₂ (· + ·) (cochainPullback_cocycle _ _ _ (original_closed m hm F))
    (cochainPullback_cocycle _ _ _ (original_closed m hm F))).trans (zero_add _)

private theorem class_add (X : TopCat.{0}) (q : ℕ)
    (A B : singularCochainGroup (ZMod 2) X q)
    (hA : cochainCoboundary (ZMod 2) X q A = 0)
    (hB : cochainCoboundary (ZMod 2) X q B = 0)
    (hAB : cochainCoboundary (ZMod 2) X q (A + B) = 0) :
    cocycleClass X q (A + B) hAB = cocycleClass X q A hA + cocycleClass X q B hB := by
  unfold cocycleClass
  rw [← map_add]
  congr 1
  apply (ModuleCat.mono_iff_injective ((cochainCxZMod2 X).iCycles q)).mp inferInstance
  rw [map_add]
  exact ((cochainCxZMod2 X).i_cyclesMk _ _ _ _).trans (congrArg₂ (· + ·)
    ((cochainCxZMod2 X).i_cyclesMk _ _ _ _).symm ((cochainCxZMod2 X).i_cyclesMk _ _ _ _).symm)

theorem class_eq : cocycleClass _ m (before m hm F) (before_closed m hm F) =
    cocycleClass _ m (after m hm F) (after_closed m hm F) := by
  have hT := original_closed m hm F
  have hclass := original_class m hm F
  change cocycleClass _ m (cochainPullback (source (m + 1)) m _) _ = _
  rw [← cohPullback_cocycleClass _ _ _ hT]
  unfold after
  rw [class_add _ _ _ _ (cochainPullback_cocycle _ _ _ hT) (cochainPullback_cocycle _ _ _ hT),
    ← cohPullback_cocycleClass _ _ _ hT, ← cohPullback_cocycleClass _ _ _ hT, hclass]
  exact primitive_class_split m

def primitive : singularCochainGroup (ZMod 2) (domain (m + 1)) (m - 1) :=
  CochainClassExact.primitive (cochainCxZMod2 (domain (m + 1))) m (by omega)
    (before m hm F) (after m hm F) (before_closed m hm F) (after_closed m hm F) (class_eq m hm F)

private theorem differential (X : TopCat.{0}) (i j : ℕ) (h : i + 1 = j)
    (η : singularCochainGroup (ZMod 2) X i) :
    ((cochainCxZMod2 X).d i j).hom η = (chains X).d j i ≫ η := by
  subst j
  rfl

theorem primitive_boundary : (chains (domain (m + 1))).d m (m - 1) ≫ primitive m hm F =
    before m hm F - after m hm F := by
  have h := CochainClassExact.primitive_d (cochainCxZMod2 (domain (m + 1))) m (by omega)
    (before m hm F) (after m hm F) (before_closed m hm F) (after_closed m hm F) (class_eq m hm F)
  rw [differential _ _ _ (by omega)] at h
  exact h

theorem cycle_values : (chains (domain (m + 1))).iCycles m ≫ before m hm F =
    (chains (domain (m + 1))).iCycles m ≫ after m hm F := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← primitive_boundary m hm F, ← Category.assoc,
    HomologicalComplex.iCycles_d, zero_comp]

end
end Finsler.NativeNearCutPrimitiveGH
