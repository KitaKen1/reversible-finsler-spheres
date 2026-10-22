module

public import Finsler.Analysis.H1FiberBase
public import Finsler.Analysis.H1AlignmentHomotopy

/-! A genuine local product chart for evaluation at the basepoint.
All spaces carry the original strong H¹ or sphere topology. -/

@[expose] public section

namespace Finsler.H1LocalFiber

open Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1AlignmentHomotopy
open Finsler.H1OrthogonalLength Finsler.H1OrthogonalContinuity
open Finsler.NearbyRotor Finsler.RotorInverse Finsler.H1FiberBase
open Set
open scoped Topology

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000

def based (y : Sphere n) : Set (SphereLoop n) := {u | basepoint u = (y : Ambient n)}
def nearBases (y : Sphere n) : Set (Sphere n) := {x | dist (x : Ambient n) (y : Ambient n) < 1}
def nearFiber (y : Sphere n) : Set (SphereLoop n) :=
  {u | dist (basepoint u) (y : Ambient n) < 1}

def forward (y : Sphere n) (u : nearFiber y) : nearBases y × based y :=
  (⟨point u.val, u.property⟩, ⟨align u.val y, basepoint_align u.val y⟩)

def inverse (y : Sphere n) (p : nearBases y × based y) : nearFiber y :=
  ⟨align p.2.val p.1.val, by
    change dist (basepoint (align p.2.val p.1.val)) (y : Ambient n) < 1
    rw [basepoint_align]
    exact p.1.property⟩

theorem inverse_forward (y : Sphere n) (u : nearFiber y) : inverse y (forward y u) = u := by
  apply Subtype.ext
  exact align_reverse u.val y

theorem forward_inverse (y : Sphere n) (p : nearBases y × based y) :
    forward y (inverse y p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    exact basepoint_align p.2.val p.1.val
  · apply Subtype.ext
    change align (align p.2.val p.1.val) y = p.2.val
    have he : point p.2.val = y := Subtype.ext p.2.property
    simpa only [he] using align_reverse p.2.val p.1.val

theorem continuous_forward (y : Sphere n) : Continuous (forward y) := by
  have hp : Continuous (fun u : nearFiber y => point u.val) :=
    continuous_point.comp continuous_subtype_val
  have hraw : Continuous (fun u : nearFiber y => (u.val, y)) :=
    continuous_subtype_val.prodMk continuous_const
  have hmem (u : nearFiber y) : (u.val, y) ∈ nearLoops n := by
    change dist (y : Ambient n) (basepoint u.val) < 1
    rw [dist_comm]
    exact u.property
  have hpair : Continuous (fun u : nearFiber y =>
      (⟨(u.val, y), hmem u⟩ : nearLoops n)) := hraw.subtype_mk _
  have hc : Continuous (fun u : nearFiber y => align u.val y) :=
    ((alignedMap (n := n)).continuous.comp hpair).congr (fun u => rfl)
  exact (hp.subtype_mk _).prodMk (hc.subtype_mk _)

theorem continuous_inverse (y : Sphere n) : Continuous (inverse y) := by
  have hu : Continuous (fun p : nearBases y × based y => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hx : Continuous (fun p : nearBases y × based y => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hraw : Continuous (fun p : nearBases y × based y => (p.2.val, p.1.val)) := hu.prodMk hx
  have hmem (p : nearBases y × based y) : (p.2.val, p.1.val) ∈ nearLoops n := by
    change dist (p.1.val : Ambient n) (basepoint p.2.val) < 1
    rw [p.2.property]
    exact p.1.property
  have hpair : Continuous (fun p : nearBases y × based y =>
      (⟨(p.2.val, p.1.val), hmem p⟩ : nearLoops n)) := hraw.subtype_mk _
  have hc : Continuous (fun p : nearBases y × based y => align p.2.val p.1.val) :=
    ((alignedMap (n := n)).continuous.comp hpair).congr (fun p => rfl)
  exact hc.subtype_mk _

/-- Actual local product decomposition of the basepoint evaluation map. -/
def chart (y : Sphere n) : nearFiber y ≃ₜ nearBases y × based y where
  toFun := forward y
  invFun := inverse y
  left_inv := inverse_forward y
  right_inv := forward_inverse y
  continuous_toFun := continuous_forward y
  continuous_invFun := continuous_inverse y


end
end Finsler.H1LocalFiber
