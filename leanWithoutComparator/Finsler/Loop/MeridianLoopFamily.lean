module

public import Finsler.Loop.RationalSphereArc
public import Finsler.Loop.ClosedPathCircle
public import Finsler.Loop.ContinuousLoopModel

/-! An ACTUAL family of based loops: the outgoing meridian varies
over the equator, while the return meridian is fixed. Evaluation at
time 1/4 recovers the parameter exactly. No nonzero homology claim
or identification with a manuscript generator is assumed. -/

@[expose] public section
namespace Finsler.MeridianLoopFamily
open CategoryTheory Topology
open Finsler.SphereGeometry Finsler.IntervalSobolev
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev equator {n : ℕ} (P : Sphere n) := {v : Sphere n // ⟪(P : Ambient n), (v : Ambient n)⟫ = 0}

def antipode {n : ℕ} (P : Sphere n) : Sphere n :=
  ⟨-(P : Ambient n), by simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using
    (mem_sphere_zero_iff_norm.mp P.property)⟩

def outgoing {n : ℕ} (P : Sphere n) (v : equator P) : RationalSphereArc.orthogonalPairs n :=
  ⟨(P, v.val), v.property⟩

def incoming {n : ℕ} (P : Sphere n) (v : equator P) : RationalSphereArc.orthogonalPairs n :=
  ⟨(v.val, antipode P), by
    change ⟪(v.val : Ambient n), -(P : Ambient n)⟫ = 0
    rw [inner_neg_right, real_inner_comm, v.property, neg_zero]⟩

def meridian {n : ℕ} (P : Sphere n) (v : equator P) : Path P (antipode P) :=
  (RationalSphereArc.arc (outgoing P v)).trans (RationalSphereArc.arc (incoming P v))

theorem meridian_continuous {n : ℕ} (P : Sphere n) : Continuous (meridian P) := by
  apply Path.continuous_uncurry_iff.mp
  exact Path.trans_continuous_family _
    (RationalSphereArc.family_continuous (outgoing P) (by unfold outgoing; fun_prop)) _
    (RationalSphereArc.family_continuous (incoming P) (by unfold incoming; fun_prop))

def half : _root_.unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
def quarter : _root_.unitInterval := ⟨1 / 4, by constructor <;> norm_num⟩

theorem meridian_half {n : ℕ} (P : Sphere n) (v : equator P) : meridian P v half = v.val := by
  rw [meridian, Path.trans_apply]
  norm_num [half]
  rfl

def loop {n : ℕ} (P : Sphere n) (v₀ v : equator P) : Path P P :=
  (meridian P v).trans (meridian P v₀).symm

theorem loop_continuous {n : ℕ} (P : Sphere n) (v₀ : equator P) : Continuous (loop P v₀) :=
  (meridian_continuous P).path_trans continuous_const

theorem loop_quarter {n : ℕ} (P : Sphere n) (v₀ v : equator P) : loop P v₀ v quarter = v.val := by
  rw [loop, Path.trans_apply]
  norm_num [quarter]
  exact meridian_half P v

def ordinary {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.of (equator P) ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun v => ClosedPathCircle.circle (ClosedPathCircle.ofPath (loop P v₀ v)),
    (ClosedPathCircle.path_circle_continuous P).comp (loop_continuous P v₀)⟩

theorem ordinary_quarter {n : ℕ} (P : Sphere n) (v₀ v : equator P) :
    ordinary P v₀ v (((quarter : ℝ)) : SobolevCircleRepresentative.Circle) = v.val := by
  change ClosedPathCircle.circle (ClosedPathCircle.ofPath (loop P v₀ v))
    (((quarter : ℝ)) : SobolevCircleRepresentative.Circle) = v.val
  rw [ClosedPathCircle.circle_coe]
  exact loop_quarter P v₀ v

theorem ordinary_basepoint {n : ℕ} (P : Sphere n) (v₀ v : equator P) :
    ordinary P v₀ v 0 = P := by
  have h := ClosedPathCircle.circle_coe (ClosedPathCircle.ofPath (loop P v₀ v)) 0
  exact h.trans (loop P v₀ v).source

theorem ordinary_injective {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Function.Injective (ordinary P v₀) := by
  intro v w h
  apply Subtype.ext
  have he := congrArg (fun u : C(SobolevCircleRepresentative.Circle, Sphere n) =>
    u (((quarter : ℝ)) : SobolevCircleRepresentative.Circle)) h
  rw [ordinary_quarter, ordinary_quarter] at he
  exact he

theorem equator_compact {n : ℕ} (P : Sphere n) : IsCompact (Set.univ : Set (equator P)) := by
  let : CompactSpace (Sphere n) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient n) 1)
  have hc : IsCompact {v : Sphere n | ⟪(P : Ambient n), (v : Ambient n)⟫ = 0} :=
    (isClosed_eq (by fun_prop) continuous_const).isCompact
  let : CompactSpace (equator P) := isCompact_iff_compactSpace.mp hc
  exact isCompact_univ

end
end Finsler.MeridianLoopFamily
