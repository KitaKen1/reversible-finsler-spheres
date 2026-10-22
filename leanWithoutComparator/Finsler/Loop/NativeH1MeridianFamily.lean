module

public import Finsler.Loop.H1RationalSphereArc
public import Finsler.Loop.H1PathRepresentativeCalculus
public import Finsler.Loop.MeridianLoopFamily

/-! The SAME explicit meridian loops now form a genuine strong-H1
family with pointwise equality at EVERY interval/circle time. Thus
future self-cut calculations can use the original H1 split maps. -/
@[expose] public section
namespace Finsler.NativeH1MeridianFamily
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.H1PathRepresentativeCalculus Finsler.SobolevReverse Finsler.SobolevCircleRepresentative
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def meridianData {n : ℕ} (P : Sphere n) (v : equator P) : Space n :=
  halfConcat (H1RationalSphereArc.data (outgoing P v)) (H1RationalSphereArc.data (incoming P v))

theorem representative_meridian {n : ℕ} (P : Sphere n) (v : equator P) (t : _root_.unitInterval) :
    continuousRepresentative (meridianData P v) (t : ℝ) = (meridian P v t : Ambient n) :=
  represented_concat _ _ _ _ (H1RationalSphereArc.representative (outgoing P v))
    (H1RationalSphereArc.representative (incoming P v)) t

theorem continuous_meridianData {n : ℕ} (P : Sphere n) : Continuous (meridianData P) := by
  have ho : Continuous (fun v : equator P => outgoing P v) := (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  have hi : Continuous (fun v : equator P => incoming P v) := (continuous_subtype_val.prodMk continuous_const).subtype_mk _
  apply continuous_halfConcat _ _ ((H1RationalSphereArc.continuous_data n).comp ho)
    ((H1RationalSphereArc.continuous_data n).comp hi)
  intro v
  change continuousRepresentative (H1RationalSphereArc.data (outgoing P v)) 1 =
    continuousRepresentative (H1RationalSphereArc.data (incoming P v)) 0
  rw [H1RationalSphereArc.target, H1RationalSphereArc.source]
  rfl

def loopData {n : ℕ} (P : Sphere n) (v₀ v : equator P) : Space n :=
  halfConcat (meridianData P v) (reverseData (meridianData P v₀))

theorem representative_loop {n : ℕ} (P : Sphere n) (v₀ v : equator P) (t : _root_.unitInterval) :
    continuousRepresentative (loopData P v₀ v) (t : ℝ) = (loop P v₀ v t : Ambient n) :=
  represented_concat _ _ _ _ (representative_meridian P v)
    (represented_reverse _ _ (representative_meridian P v₀)) t

theorem continuous_loopData {n : ℕ} (P : Sphere n) (v₀ : equator P) : Continuous (loopData P v₀) := by
  apply continuous_halfConcat _ _ (continuous_meridianData P) continuous_const
  intro v
  have h₁ := representative_meridian P v 1
  have h₀ := represented_reverse _ _ (representative_meridian P v₀) 0
  simp only [Set.Icc.coe_one, Path.target] at h₁
  simp only [Set.Icc.coe_zero, Path.source] at h₀
  exact h₁.trans h₀.symm

def native {n : ℕ} (P : Sphere n) (v₀ v : equator P) : SphereLoop n :=
  ⟨⟨loopData P v₀ v, (mem_periodicSubmodule_iff _).mpr (by
    have h₁ := representative_loop P v₀ v 1
    have h₀ := representative_loop P v₀ v 0
    simp only [Set.Icc.coe_one, Path.target] at h₁
    simp only [Set.Icc.coe_zero, Path.source] at h₀
    exact h₁.trans h₀.symm)⟩,
    fun t => (congrArg norm (representative_loop P v₀ v t)).trans
      (mem_sphere_zero_iff_norm.mp (loop P v₀ v t).property)⟩

theorem continuous_native {n : ℕ} (P : Sphere n) (v₀ : equator P) : Continuous (native P v₀) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  exact sphereLoop_tendsto_iff.mpr (continuous_loopData P v₀).continuousAt

def family {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopCat.of (equator P) ⟶ BorelLoop.Loops n :=
  TopCat.ofHom ⟨native P v₀, continuous_native P v₀⟩

theorem circle_value {n : ℕ} (P : Sphere n) (v₀ v : equator P) (x : SobolevCircleRepresentative.Circle) :
    sphereCircleMap (native P v₀ v) x = ClosedPathCircle.circle (ClosedPathCircle.ofPath (loop P v₀ v)) x := by
  rw [sphereCircleMap_point, ClosedPathCircle.circle_apply]
  apply Subtype.ext
  exact representative_loop P v₀ v (circlePoint x)

theorem family_inclusion {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    family P v₀ ≫ ContinuousLoopModel.inclusion n = ordinary P v₀ := by
  ext v : 1
  apply ContinuousMap.ext
  intro x
  exact circle_value P v₀ v x

end
end Finsler.NativeH1MeridianFamily
