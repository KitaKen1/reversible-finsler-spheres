module

public import Finsler.Loop.DiagonalCutRejoining
public import Finsler.Loop.NativeTripleSelfEvaluation

/-! Three EXPLICIT native matching-meridian families, for pairs01,
02,12. North and south are joined into the original full meridian,
including both poles. Their actual cut times lie strictly inside(0,1).
The ORIGINAL tested/retained transgression identity is pulled back
along these genuine families. No Thom multiplicity is assigned here. -/
@[expose] public section
namespace Finsler.NativeMeridianMatchingLoci
open CategoryTheory MonoidalCategory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.SobolevCircleRepresentative
open Finsler.CochainComparison Finsler.MeridianLoopFamily Finsler.MeridianTripleQuarterClocks
open Finsler.NativeTripleSelfEvaluation
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

local notation "I" => ClosedInterval

def legClock (k : Fin 3) (t : I) : ℝ :=
  match k with
  | 0 => (t : ℝ) / 8
  | 1 => (2 + (t : ℝ)) / 8
  | 2 => (2 + (t : ℝ)) / 4

theorem legClock_mem (k : Fin 3) (t : I) : legClock k t ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases k <;> constructor <;> dsimp [legClock] <;> linarith [t.property.1, t.property.2]

theorem loop_meridian {n : ℕ} (P : Sphere n) (v₀ v : equator P) (t : I) :
    (loop P v₀ v).extend ((t : ℝ) / 2) = meridian P v t := by
  rw [loop, Path.extend_trans_of_le_half _ _ (by linarith [t.property.2]),
    show 2 * ((t : ℝ) / 2) = (t : ℝ) by ring]
  exact Path.extend_apply _ t.property

theorem triple_meridian {n : ℕ} (P : Sphere n) (v₀ : equator P) (v : Fin 3 → equator P)
    (k : Fin 3) (t : I) :
    (triple P v₀ v).extend (legClock k t) = meridian P (v k) t := by
  have ht : (t : ℝ) / 2 ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [t.property.1, t.property.2]
  fin_cases k
  · change (triple P v₀ v).extend ((t : ℝ) / 8) = _
    rw [show (t : ℝ) / 8 = ((t : ℝ) / 2) / 4 by ring, triple_first P v₀ v _ ht]
    exact loop_meridian P v₀ (v 0) t
  · change (triple P v₀ v).extend ((2 + (t : ℝ)) / 8) = _
    rw [show (2 + (t : ℝ)) / 8 = (1 + (t : ℝ) / 2) / 4 by ring, triple_second P v₀ v _ ht]
    exact loop_meridian P v₀ (v 1) t
  · change (triple P v₀ v).extend ((2 + (t : ℝ)) / 4) = _
    rw [show (2 + (t : ℝ)) / 4 = (1 + (t : ℝ) / 2) / 2 by ring, triple_third P v₀ v _ ht]
    exact loop_meridian P v₀ (v 2) t

theorem circle_meridian {n : ℕ} (P : Sphere n) (v₀ : equator P)
    (z : NativeH1TripleMeridian.parameters P) (k : Fin 3) (t : I) :
    sphereCircleMap (NativeH1TripleMeridian.native P v₀ z)
      ((legClock k t : ℝ) : SobolevCircleRepresentative.Circle) = meridian P (directions z k) t := by
  rw [NativeH1TripleMeridian.circle_value]
  have ht := legClock_mem k t
  calc
    _ = NativeH1TripleMeridian.triplePath P v₀ z ⟨legClock k t, ht⟩ :=
      ClosedPathCircle.circle_coe _ ⟨legClock k t, ht⟩
    _ = (triple P v₀ (directions z)).extend (legClock k t) := (Path.extend_apply _ ht).symm
    _ = _ := triple_meridian P v₀ (directions z) k t

def pairLeft (b : Fin 3) : Fin 3 := if b = 2 then 1 else 0
def pairRight (b : Fin 3) : Fin 3 := if b = 0 then 1 else 2

def repeated {n : ℕ} {P : Sphere n} (b : Fin 3) (v w : equator P) : NativeH1TripleMeridian.parameters P :=
  match b with
  | 0 => ((v, v), w)
  | 1 => ((v, w), v)
  | 2 => ((w, v), v)

theorem repeated_left {n : ℕ} {P : Sphere n} (b : Fin 3) (v w : equator P) :
    directions (repeated b v w) (pairLeft b) = v := by fin_cases b <;> rfl
theorem repeated_right {n : ℕ} {P : Sphere n} (b : Fin 3) (v w : equator P) :
    directions (repeated b v w) (pairRight b) = v := by fin_cases b <;> rfl

def cutTime (b : Fin 3) (t : I) : I :=
  ⟨legClock (pairRight b) t - legClock (pairLeft b) t, by
    fin_cases b <;> constructor <;> dsimp [pairLeft, pairRight, legClock] <;>
      linarith [t.property.1, t.property.2]⟩

theorem cutTime_interior (b : Fin 3) (t : I) : 0 < (cutTime b t : ℝ) ∧ (cutTime b t : ℝ) < 1 := by
  fin_cases b <;> constructor <;> dsimp [cutTime, pairLeft, pairRight, legClock] <;>
    linarith [t.property.1, t.property.2]

def rotationTime (b : Fin 3) (t : I) : I :=
  ⟨legClock (pairLeft b) t, legClock_mem _ _⟩

abbrev parameters {n : ℕ} (P : Sphere n) : TopCat.{0} := TopCat.of (I × (equator P × equator P))

def intoSource {n : ℕ} (P : Sphere n) (b : Fin 3) : parameters P ⟶ sourceSpace P :=
  TopCat.ofHom ⟨fun z => (cutTime b z.1, (rotationTime b z.1, repeated b z.2.1 z.2.2)), by
    fin_cases b <;> dsimp [cutTime, rotationTime, pairLeft, pairRight, legClock, repeated] <;> fun_prop⟩

def intoCut {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    parameters P ⟶ SelfCutThomCocycle.parameters n := intoSource P b ≫ NativeTripleSelfEvaluation.intoCut P v₀

theorem selfEvaluation (n : ℕ) (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : parameters P) :
    SelfCutThomCocycle.selfEvaluation n (intoCut P v₀ b z) =
      (meridian P z.2.1 z.1, meridian P z.2.1 z.1) := by
  have ha : ((rotationTime b z.1 : ℝ) : SobolevCircleRepresentative.Circle) +
      ((cutTime b z.1 : ℝ) : SobolevCircleRepresentative.Circle) =
      ((legClock (pairRight b) z.1 : ℝ) : SobolevCircleRepresentative.Circle) := by
    rw [← AddCircle.coe_add]
    apply congrArg (fun x : ℝ => (x : SobolevCircleRepresentative.Circle))
    change legClock (pairLeft b) z.1 +
      (legClock (pairRight b) z.1 - legClock (pairLeft b) z.1) = _
    ring
  change SelfCutThomCocycle.selfEvaluation n (NativeTripleSelfEvaluation.intoCut P v₀ (intoSource P b z)) = _
  rw [selfEvaluation_apply]
  apply Prod.ext
  · change sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated b z.2.1 z.2.2))
      ((legClock (pairLeft b) z.1 : ℝ) : SobolevCircleRepresentative.Circle) = _
    rw [circle_meridian, repeated_left]
  · change sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated b z.2.1 z.2.2))
      (((rotationTime b z.1 : ℝ) : SobolevCircleRepresentative.Circle) +
        ((cutTime b z.1 : ℝ) : SobolevCircleRepresentative.Circle)) = _
    rw [ha, circle_meridian, repeated_right]

def intoDiagonal {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    parameters P ⟶ DiagonalSelfCutRepresentatives.domain n :=
  TopCat.ofHom ⟨fun z => ⟨intoCut P v₀ b z, by
    have hp := congrArg Prod.fst (selfEvaluation n P v₀ b z)
    have he := congrArg Prod.snd (selfEvaluation n P v₀ b z)
    exact he.trans hp.symm⟩,
    (intoCut P v₀ b).hom.continuous.subtype_mk _⟩

theorem original_transgression_split (n q : ℕ) (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (intoDiagonal P v₀ b ≫ DiagonalCutRejoining.source n) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (intoDiagonal P v₀ b ≫ DiagonalSelfCutRepresentatives.tested n) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (intoDiagonal P v₀ b ≫ DiagonalSelfCutRepresentatives.retained n) q).hom (ContinuousLoopSweep.transgression n q a) := by
  have hc (k : DiagonalSelfCutRepresentatives.domain n ⟶ ContinuousLoopModel.space n) :
      (cohPullback (intoDiagonal P v₀ b ≫ k) q).hom (ContinuousLoopSweep.transgression n q a) =
        (cohPullback (intoDiagonal P v₀ b) q).hom
          ((cohPullback k q).hom (ContinuousLoopSweep.transgression n q a)) :=
    ConcreteCategory.congr_hom ((singularCohomologyZMod2 q).map_comp k.op (intoDiagonal P v₀ b).op) _
  rw [hc, hc, hc]
  simpa only [map_add] using congrArg ((cohPullback (intoDiagonal P v₀ b) q).hom)
    (DiagonalCutRejoining.original_transgression_split n q a)

end
end Finsler.NativeMeridianMatchingLoci
