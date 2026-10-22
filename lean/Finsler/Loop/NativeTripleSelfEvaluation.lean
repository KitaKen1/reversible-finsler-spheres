module

public import Finsler.Loop.NativeH1TripleMeridian
public import Finsler.Loop.MeridianQuarterIncidence
public import Finsler.Loop.CompactSelfCoincidenceAvoidance

/-! Exact twelve-quarter self-incidence formulas for the ORIGINAL
strong-H1 rotated triple family. Compact off-parameter-diagonal
patches pull the actual normalized Thom cochain back to ZERO at
one common positive radius, before the tested/retained caps. -/
@[expose] public section
namespace Finsler.NativeTripleSelfEvaluation
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SobolevCircleRepresentative Finsler.SobolevShift
open Finsler.MeridianTripleQuarterClocks
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def directions {n : ℕ} {P : Sphere n} (z : NativeH1TripleMeridian.parameters P) : Fin 3 → equator P :=
  ![z.1.1, z.1.2, z.2]

theorem circle_quarter {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : NativeH1TripleMeridian.parameters P)
    (k : Fin 3) (q : Fin 4) (t : _root_.unitInterval) :
    sphereCircleMap (NativeH1TripleMeridian.native P v₀ z)
      ((clock k q t : ℝ) : SobolevCircleRepresentative.Circle) = piece P v₀ (directions z k) q t := by
  rw [NativeH1TripleMeridian.circle_value]
  have ht := clock_mem k q t
  calc
    _ = NativeH1TripleMeridian.triplePath P v₀ z ⟨clock k q t, ht⟩ :=
      ClosedPathCircle.circle_coe _ ⟨clock k q t, ht⟩
    _ = (triple P v₀ (directions z)).extend (clock k q t) :=
      (Path.extend_apply _ ht).symm
    _ = _ := triple_quarter P v₀ (directions z) k q t

theorem point_shift {n : ℕ} (u : SphereLoop n) (a : ℝ) :
    H1FiberBase.point (shiftSphere u a) = sphereCircleMap u (a : SobolevCircleRepresentative.Circle) := by
  have h := sphereCircleMap_coe (shiftSphere u a) 0
  change sphereCircleMap (shiftSphere u a) 0 = H1FiberBase.point (shiftSphere u a) at h
  rw [circleMap_shiftSphere, shiftedSphereMap_apply, add_zero] at h
  exact h.symm

theorem endpoint_shift {n : ℕ} (u : SphereLoop n) (a : ℝ) (t : _root_.unitInterval) :
    sphereRepresentative (shiftSphere u a) t =
      sphereCircleMap u ((a : SobolevCircleRepresentative.Circle) + ((t : ℝ) : SobolevCircleRepresentative.Circle)) := by
  have h := sphereCircleMap_coe (shiftSphere u a) t
  rw [circleMap_shiftSphere, shiftedSphereMap_apply] at h
  exact h.symm

abbrev sourceSpace {n : ℕ} (P : Sphere n) : TopCat.{0} :=
  TopCat.of (_root_.unitInterval × (_root_.unitInterval × NativeH1TripleMeridian.parameters P))

def intoCut {n : ℕ} (P : Sphere n) (v₀ : equator P) : sourceSpace P ⟶ SelfCutThomCocycle.parameters n :=
  TopCat.ofHom ⟨fun z => (z.1, shiftSphere (NativeH1TripleMeridian.native P v₀ z.2.2) (z.2.1 : ℝ)), by
    have hp : Continuous (fun z : sourceSpace P =>
        (z.2.1, NativeH1TripleMeridian.native P v₀ z.2.2)) :=
      (continuous_fst.comp continuous_snd).prodMk
        ((NativeH1TripleMeridian.continuous_native P v₀).comp (continuous_snd.comp continuous_snd))
    have hc := (H1LoopRotation.homotopy n).continuous.comp hp
    exact continuous_fst.prodMk hc⟩

theorem selfEvaluation_apply {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : sourceSpace P) :
    SelfCutThomCocycle.selfEvaluation n (intoCut P v₀ z) =
      (sphereCircleMap (NativeH1TripleMeridian.native P v₀ z.2.2)
        ((z.2.1 : ℝ) : SobolevCircleRepresentative.Circle),
      sphereCircleMap (NativeH1TripleMeridian.native P v₀ z.2.2)
        (((z.2.1 : ℝ) : SobolevCircleRepresentative.Circle) + ((z.1 : ℝ) : SobolevCircleRepresentative.Circle))) :=
  Prod.ext (point_shift _ _) (endpoint_shift _ _ _)

theorem quarter_pair {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : sourceSpace P)
    (k l : Fin 3) (q r : Fin 4) (s t : _root_.unitInterval)
    (h₀ : ((z.2.1 : ℝ) : SobolevCircleRepresentative.Circle) = ((clock k q s : ℝ) : SobolevCircleRepresentative.Circle))
    (h₁ : (((z.2.1 : ℝ) : SobolevCircleRepresentative.Circle) + ((z.1 : ℝ) : SobolevCircleRepresentative.Circle)) =
      ((clock l r t : ℝ) : SobolevCircleRepresentative.Circle)) :
    SelfCutThomCocycle.selfEvaluation n (intoCut P v₀ z) =
      (piece P v₀ (directions z.2.2 k) q s, piece P v₀ (directions z.2.2 l) r t) := by
  rw [selfEvaluation_apply]
  apply Prod.ext
  · rw [h₀, circle_quarter]
  · rw [h₁, circle_quarter]

theorem north_north_iff {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : sourceSpace P)
    (k l : Fin 3) (s t : _root_.unitInterval) (hs : 0 < (s : ℝ)) (ht : 0 < (t : ℝ))
    (h₀ : ((z.2.1 : ℝ) : SobolevCircleRepresentative.Circle) = ((clock k 0 s : ℝ) : SobolevCircleRepresentative.Circle))
    (h₁ : (((z.2.1 : ℝ) : SobolevCircleRepresentative.Circle) + ((z.1 : ℝ) : SobolevCircleRepresentative.Circle)) =
      ((clock l 0 t : ℝ) : SobolevCircleRepresentative.Circle)) :
    (SelfCutThomCocycle.selfEvaluation n (intoCut P v₀ z)).1 =
      (SelfCutThomCocycle.selfEvaluation n (intoCut P v₀ z)).2 ↔
        directions z.2.2 k = directions z.2.2 l ∧ s = t := by
  rw [quarter_pair P v₀ z k l 0 0 s t h₀ h₁]
  exact MeridianQuarterIncidence.north_north_iff P _ _ s t hs ht

theorem south_south_iff {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : sourceSpace P)
    (k l : Fin 3) (s t : _root_.unitInterval) (hs : (s : ℝ) < 1) (ht : (t : ℝ) < 1)
    (h₀ : ((z.2.1 : ℝ) : SobolevCircleRepresentative.Circle) = ((clock k 1 s : ℝ) : SobolevCircleRepresentative.Circle))
    (h₁ : (((z.2.1 : ℝ) : SobolevCircleRepresentative.Circle) + ((z.1 : ℝ) : SobolevCircleRepresentative.Circle)) =
      ((clock l 1 t : ℝ) : SobolevCircleRepresentative.Circle)) :
    (SelfCutThomCocycle.selfEvaluation n (intoCut P v₀ z)).1 =
      (SelfCutThomCocycle.selfEvaluation n (intoCut P v₀ z)).2 ↔
        directions z.2.2 k = directions z.2.2 l ∧ s = t := by
  rw [quarter_pair P v₀ z k l 1 1 s t h₀ h₁]
  exact MeridianQuarterIncidence.south_south_iff P _ _ s t hs ht

theorem north_south_iff {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : sourceSpace P)
    (k l : Fin 3) (s t : _root_.unitInterval)
    (h₀ : ((z.2.1 : ℝ) : SobolevCircleRepresentative.Circle) = ((clock k 0 s : ℝ) : SobolevCircleRepresentative.Circle))
    (h₁ : (((z.2.1 : ℝ) : SobolevCircleRepresentative.Circle) + ((z.1 : ℝ) : SobolevCircleRepresentative.Circle)) =
      ((clock l 1 t : ℝ) : SobolevCircleRepresentative.Circle)) :
    (SelfCutThomCocycle.selfEvaluation n (intoCut P v₀ z)).1 =
      (SelfCutThomCocycle.selfEvaluation n (intoCut P v₀ z)).2 ↔
        s = 1 ∧ t = 0 ∧ directions z.2.2 k = directions z.2.2 l := by
  rw [quarter_pair P v₀ z k l 0 1 s t h₀ h₁]
  exact MeridianQuarterIncidence.north_south_iff P _ _ s t

end
end Finsler.NativeTripleSelfEvaluation
