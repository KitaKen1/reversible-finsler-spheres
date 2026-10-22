module

public import Finsler.Loop.H1ConstantRelativeFiberChart
public import Finsler.Loop.MeridianQuarterHomotopies

/-! Actual strong-H1 evaluation product charts over a sphere with
one antipode removed. The concrete rotor is continuous on this whole
punctured base, not just the radius-one local ball. Two such actual
open evaluation domains cover the original loop space. -/
@[expose] public section
namespace Finsler.H1PuncturedEvaluationChart
open CategoryTheory
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.H1LocalFiber Finsler.H1FiberBase Finsler.CompactH1Alignment
open Finsler.H1OrthogonalLength Finsler.H1OrthogonalContinuity Finsler.H1AlignmentHomotopy
open Finsler.MeridianLoopFamily Finsler.NearbyRotor
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def base {n : ℕ} (y : Sphere n) : Set (Sphere n) := {x | x ≠ antipode y}
def fiber {n : ℕ} (y : Sphere n) : Set (SphereLoop n) := {u | point u ∈ base y}

theorem point_align {n : ℕ} (u : SphereLoop n) (y : Sphere n) : point (align u y) = y :=
  Subtype.ext (basepoint_align u y)

theorem sum_ne_zero {n : ℕ} (x y : Sphere n) (h : x ≠ antipode y) :
    (x : Ambient n) + (y : Ambient n) ≠ 0 := by
  intro hz
  apply h
  apply Subtype.ext
  exact eq_neg_of_add_eq_zero_left hz

theorem align_continuous {n : ℕ} {X : Type*} [TopologicalSpace X]
    (u : X → SphereLoop n) (y : X → Sphere n) (hu : Continuous u) (hy : Continuous y)
    (h : ∀ z, basepoint (u z) + (y z : Ambient n) ≠ 0) :
    Continuous (fun z => align (u z) (y z)) := by
  have hp : Continuous (fun z => (basepoint (u z), (y z : Ambient n))) :=
    (basepoint_continuous.comp hu).prodMk (continuous_subtype_val.comp hy)
  have hA : Continuous (fun z => (rotor (basepoint (u z)) (y z : Ambient n)).toContinuousLinearMap) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hn : basepoint (u z) ≠ 0 := by
      have he : ‖basepoint (u z)‖ = 1 := (u z).sphere_constraint ⟨0, by norm_num⟩
      exact norm_ne_zero_iff.mp (by rw [he]; norm_num)
    exact (rotor_continuousAt hn (h z)).comp
      (f := fun q : X => (basepoint (u q), (y q : Ambient n))) (x := z) hp.continuousAt
  exact continuous_rotateLoop_family _ hA u hu

def forward {n : ℕ} (y : Sphere n) (u : fiber y) : base y × based y :=
  (⟨point u.val, u.property⟩, ⟨align u.val y, basepoint_align u.val y⟩)

def inverse {n : ℕ} (y : Sphere n) (p : base y × based y) : fiber y :=
  ⟨align p.2.val p.1.val, by change point (align p.2.val p.1.val) ≠ antipode y; rw [point_align]; exact p.1.property⟩

theorem inverse_forward {n : ℕ} (y : Sphere n) (u : fiber y) : inverse y (forward y u) = u := by
  apply Subtype.ext
  exact align_reverse u.val y

theorem forward_inverse {n : ℕ} (y : Sphere n) (p : base y × based y) : forward y (inverse y p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    exact point_align p.2.val p.1.val
  · apply Subtype.ext
    have he : point p.2.val = y := Subtype.ext p.2.property
    change align (align p.2.val p.1.val) y = p.2.val
    simpa only [he] using align_reverse p.2.val p.1.val

theorem continuous_forward {n : ℕ} (y : Sphere n) : Continuous (forward y) := by
  have hp : Continuous (fun u : fiber y => point u.val) := continuous_point.comp continuous_subtype_val
  have hc := align_continuous (fun u : fiber y => u.val) (fun _ => y) continuous_subtype_val continuous_const
    (fun u => sum_ne_zero (point u.val) y u.property)
  exact (hp.subtype_mk _).prodMk (hc.subtype_mk _)

theorem continuous_inverse {n : ℕ} (y : Sphere n) : Continuous (inverse y) := by
  have hu : Continuous (fun p : base y × based y => p.2.val) := continuous_snd.subtype_val
  have hx : Continuous (fun p : base y × based y => p.1.val) := continuous_fst.subtype_val
  have hc := align_continuous (fun p : base y × based y => p.2.val) (fun p => p.1.val) hu hx (by
    intro p
    rw [p.2.property, add_comm]
    exact sum_ne_zero p.1.val y p.1.property)
  exact hc.subtype_mk _

def chart {n : ℕ} (y : Sphere n) : fiber y ≃ₜ base y × based y where
  toFun := forward y
  invFun := inverse y
  left_inv := inverse_forward y
  right_inv := forward_inverse y
  continuous_toFun := continuous_forward y
  continuous_invFun := continuous_inverse y

theorem base_open {n : ℕ} (y : Sphere n) : IsOpen (base y) := isClosed_singleton.isOpen_compl

theorem fiber_open {n : ℕ} (y : Sphere n) : IsOpen (fiber y) :=
  (base_open y).preimage continuous_point

theorem antipode_antipode {n : ℕ} (y : Sphere n) : antipode (antipode y) = y := by
  apply Subtype.ext
  exact neg_neg _

theorem base_cover {n : ℕ} (y : Sphere n) : base y ∪ base (antipode y) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = antipode y
  · right
    intro he
    have hyy : antipode y = y := hx.symm.trans (he.trans (antipode_antipode y))
    exact MeridianQuarterHomotopies.pole_ne_antipode y hyy.symm
  · exact Or.inl hx

theorem fiber_cover {n : ℕ} (y : Sphere n) : fiber y ∪ fiber (antipode y) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro u
  have he : point u ∈ base y ∪ base (antipode y) := by rw [base_cover]; trivial
  exact he

theorem chart_evaluation {n : ℕ} (y : Sphere n) (u : fiber y) :
    (chart y u).1.val = point u.val := rfl

end
end Finsler.H1PuncturedEvaluationChart
