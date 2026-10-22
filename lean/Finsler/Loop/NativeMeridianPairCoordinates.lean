module

public import Finsler.Loop.NativeWrappedMatchingLoci
public import Finsler.Loop.NormalizedSphereGraphCap

/-! Independent times and directions for each of the THREE native
variable-meridian pairs. The ORIGINAL self-evaluation factors EXACTLY
through two actual sphere meridian evaluations and the remaining
parameter. The original normalized cochain and radius are retained. -/
@[expose] public section
namespace Finsler.NativeMeridianPairCoordinates
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.NativeMeridianMatchingLoci Finsler.NativeTripleSelfEvaluation
open Finsler.SobolevCircleRepresentative Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
local notation "I" => ClosedInterval

abbrev parameters {n : ℕ} (P : Sphere n) : TopCat.{0} :=
  TopCat.of ((I × equator P) × ((I × equator P) × equator P))

def assembly {n : ℕ} {P : Sphere n} (b : Fin 3) (v w r : equator P) : NativeH1TripleMeridian.parameters P :=
  match b with
  | 0 => ((v, w), r)
  | 1 => ((v, r), w)
  | 2 => ((r, v), w)

theorem assembly_left {n : ℕ} {P : Sphere n} (b : Fin 3) (v w r : equator P) :
    directions (assembly b v w r) (pairLeft b) = v := by fin_cases b <;> rfl
theorem assembly_right {n : ℕ} {P : Sphere n} (b : Fin 3) (v w r : equator P) :
    directions (assembly b v w r) (pairRight b) = w := by fin_cases b <;> rfl

def pairCutTime (b : Fin 3) (s t : I) : I :=
  ⟨legClock (pairRight b) t - legClock (pairLeft b) s, by
    fin_cases b <;> constructor <;> dsimp [pairLeft, pairRight, legClock] <;>
      linarith [s.property.1, s.property.2, t.property.1, t.property.2]⟩

theorem pairCutTime_interior (b : Fin 3) (s t : I) :
    0 < (pairCutTime b s t : ℝ) ∧ (pairCutTime b s t : ℝ) < 1 := by
  fin_cases b <;> constructor <;> dsimp [pairCutTime, pairLeft, pairRight, legClock] <;>
    linarith [s.property.1, s.property.2, t.property.1, t.property.2]

def intoSource {n : ℕ} (P : Sphere n) (b : Fin 3) : parameters P ⟶ sourceSpace P :=
  TopCat.ofHom ⟨fun z => (pairCutTime b z.1.1 z.2.1.1,
    (rotationTime b z.1.1, assembly b z.1.2 z.2.1.2 z.2.2)), by
    fin_cases b <;> dsimp [pairCutTime, rotationTime, pairLeft, pairRight, legClock, assembly] <;> fun_prop⟩

def intoCut {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    parameters P ⟶ SelfCutThomCocycle.parameters n := intoSource P b ≫ NativeTripleSelfEvaluation.intoCut P v₀

theorem selfEvaluation_value (n : ℕ) (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : parameters P) :
    SelfCutThomCocycle.selfEvaluation n (intoCut P v₀ b z) =
      (meridian P z.1.2 z.1.1, meridian P z.2.1.2 z.2.1.1) := by
  have ha : ((rotationTime b z.1.1 : ℝ) : SobolevCircleRepresentative.Circle) +
      ((pairCutTime b z.1.1 z.2.1.1 : ℝ) : SobolevCircleRepresentative.Circle) =
      ((legClock (pairRight b) z.2.1.1 : ℝ) : SobolevCircleRepresentative.Circle) := by
    rw [← AddCircle.coe_add]
    apply congrArg (fun x : ℝ => (x : SobolevCircleRepresentative.Circle))
    change legClock (pairLeft b) z.1.1 +
      (legClock (pairRight b) z.2.1.1 - legClock (pairLeft b) z.1.1) = _
    ring
  change SelfCutThomCocycle.selfEvaluation n (NativeTripleSelfEvaluation.intoCut P v₀ (intoSource P b z)) = _
  rw [selfEvaluation_apply]
  apply Prod.ext
  · change sphereCircleMap (NativeH1TripleMeridian.native P v₀ (assembly b z.1.2 z.2.1.2 z.2.2))
      ((legClock (pairLeft b) z.1.1 : ℝ) : SobolevCircleRepresentative.Circle) = _
    rw [circle_meridian, assembly_left]
  · change sphereCircleMap (NativeH1TripleMeridian.native P v₀ (assembly b z.1.2 z.2.1.2 z.2.2))
      (((rotationTime b z.1.1 : ℝ) : SobolevCircleRepresentative.Circle) +
        ((pairCutTime b z.1.1 z.2.1.1 : ℝ) : SobolevCircleRepresentative.Circle)) = _
    rw [ha, circle_meridian, assembly_right]

abbrev graphBase {n : ℕ} (P : Sphere n) : TopCat.{0} := BorelEvaluation.sphere n ⊗ TopCat.of (equator P)
def graphMap {n : ℕ} (P : Sphere n) : graphBase P ⟶ BorelEvaluation.sphere n := fst _ _

def meridianEvaluation {n : ℕ} (P : Sphere n) : TopCat.of (I × equator P) ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun z => meridian P z.2 z.1, by
    have hc := (Path.continuous_uncurry_iff.mpr (meridian_continuous P)).comp continuous_swap
    exact hc⟩

def sphereCoordinates {n : ℕ} (P : Sphere n) : parameters P ⟶ BorelEvaluation.sphere n ⊗ graphBase P :=
  TopCat.ofHom ⟨fun z => (meridianEvaluation P z.1, (meridianEvaluation P z.2.1, z.2.2)),
    ((meridianEvaluation P).hom.continuous.comp continuous_fst).prodMk
      (((meridianEvaluation P).hom.continuous.comp continuous_snd.fst).prodMk continuous_snd.snd)⟩

theorem selfEvaluation_factor (n : ℕ) (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    intoCut P v₀ b ≫ SelfCutThomCocycle.selfEvaluation n =
      sphereCoordinates P ≫ NormalizedSphereGraphCap.evaluation n (graphBase P) (graphMap P) := by
  ext z : 1
  exact selfEvaluation_value n P v₀ b z

theorem original_normalized_cochain_pullback (n : ℕ) (hn : 1 ≤ n) (P : Sphere n)
    (v₀ : equator P) (b : Fin 3) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (intoCut P v₀ b) n (NormalizedSelfCut.cocycle n hn hρ) =
      cochainPullback (sphereCoordinates P) n
        (NormalizedSphereGraphCap.cocycle n hn (graphBase P) (graphMap P) hρ) := by
  unfold NormalizedSelfCut.cocycle NormalizedSphereGraphCap.cocycle
  rw [← SupportedCapNaturality.pullback_comp, ← SupportedCapNaturality.pullback_comp,
    selfEvaluation_factor]

theorem original_distance (n : ℕ) (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : parameters P) :
    SupportedSelfCut.distance n (intoCut P v₀ b z) =
      NormalizedSphereGraphCap.distance n (graphBase P) (graphMap P) (sphereCoordinates P z) := by
  have he := selfEvaluation_value n P v₀ b z
  have hl := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  change H1FiberBase.point (intoCut P v₀ b z).2 = meridian P z.1.2 z.1.1 at hl
  change H1SelfCutNeighborhood.endpoint (intoCut P v₀ b z) = meridian P z.2.1.2 z.2.1.1 at hr
  change ‖(H1SelfCutNeighborhood.endpoint (intoCut P v₀ b z) : Ambient n) -
    (H1FiberBase.point (intoCut P v₀ b z).2 : Ambient n)‖ = _
  rw [hl, hr]
  rfl

end
end Finsler.NativeMeridianPairCoordinates
