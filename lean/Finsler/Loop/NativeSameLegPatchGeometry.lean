module

public import Finsler.Loop.NativeSameLegBoundaryGeometry

/-! A genuine OPEN two-component cover of the original same-leg
source: the direction hemisphere and an actual start-distance exterior.
The exterior threshold may be chosen as 1/4 with the original radii.
No global normal field is required. -/
@[expose] public section
namespace Finsler.NativeSameLegPatchGeometry
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.SameMeridianTransverseEscape Finsler.NativeMovingNonnorthGeometry Finsler.NativeSameLegThomPrimitive
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def globalDirection {n : ℕ} (P : Sphere n) (k : Fin 3) : domain P ⟶ TopCat.of (equator P) :=
  TopCat.ofHom ⟨fun z => NativeTripleSelfEvaluation.directions z.1.2 k, by
    change Continuous (fun z : (ClosedInterval × NativeH1TripleMeridian.parameters P) × ULift ClosedInterval =>
      NativeTripleSelfEvaluation.directions z.1.2 k)
    fin_cases k <;> dsimp [NativeTripleSelfEvaluation.directions] <;> fun_prop⟩

theorem local_open {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) : IsOpen (localSet P v₀ k) := by
  change IsOpen {z : domain P | 0 < ⟪((globalDirection P k z).val : Ambient n),
    ((NorthMeridianEvaluationPoint.opposite v₀).val : Ambient n)⟫}
  exact isOpen_lt continuous_const ((globalDirection P k).hom.continuous.subtype_val.subtype_val.inner continuous_const)

def startMap (n : ℕ) : SelfCutThomCocycle.parameters n ⟶ TopCat.of (Sphere n) :=
  TopCat.ofHom ⟨fun z => H1FiberBase.point z.2, H1FiberBase.continuous_point.comp continuous_snd⟩

def outside {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (D : ℝ) : Set (domain P) :=
  {z | D < ‖(H1FiberBase.point (segmentFamily P v₀ k (cutIndex isLong) z).2 : Ambient n) -
    (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖}

theorem outside_open {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (D : ℝ) :
    IsOpen (outside P v₀ k isLong D) := by
  change IsOpen {z : domain P | D < ‖((startMap n (segmentFamily P v₀ k (cutIndex isLong) z)) : Ambient n) -
    (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖}
  exact isOpen_lt continuous_const
    ((((startMap n).hom.continuous.comp (segmentFamily P v₀ k (cutIndex isLong)).hom.continuous).subtype_val.sub continuous_const).norm)

theorem cover {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) {D : ℝ} (hD : D < 3 / 5) :
    localSet P v₀ k ∪ outside P v₀ k isLong D = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hz : z ∈ outside P v₀ k isLong D
  · exact Or.inr hz
  · apply Or.inl
    have he : ‖(H1FiberBase.point (segmentFamily P v₀ k (cutIndex isLong) z).2 : Ambient n) -
        (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ < 3 / 5 :=
      lt_of_le_of_lt (le_of_not_gt hz) hD
    rw [NativeSameLegThomReduction.original_start] at he
    exact first_near_direction P v₀ (NativeTripleSelfEvaluation.directions z.1.2 k) z.1.1 he

def rotationEnds {n : ℕ} (P : Sphere n) : Set (domain P) := {z | z.1.1 = 0 ∨ z.1.1 = 1}
def seam {n : ℕ} (P : Sphere n) (isLong : Bool) : Set (domain P) := {z | z.2.down = if isLong then 1 else 0}
def otherCutEnd {n : ℕ} (P : Sphere n) (isLong : Bool) : Set (domain P) := {z | z.2.down = if isLong then 0 else 1}

end
end Finsler.NativeSameLegPatchGeometry
