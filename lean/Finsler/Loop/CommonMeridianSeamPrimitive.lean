module

public import Finsler.Loop.CommonMeridianThomPrimitive
public import Finsler.Loop.EquatorHemisphereContraction

/-! The diagonal restriction of the coherent far-relative Thom
primitive is not silently assumed zero. It is CLOSED, and its actual
class vanishes because the real time x direction patch contracts.
Construct the additional lower-degree seam primitive explicitly.
Extension with exterior support and the full cap comparison remain. -/
@[expose] public section
namespace Finsler.CommonMeridianSeamPrimitive
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.CommonMeridianThomPrimitive
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def contractTime (s t : ClosedInterval) : ClosedInterval :=
  ⟨(1 - (s : ℝ)) * (t : ℝ), ⟨mul_nonneg (sub_nonneg.mpr s.property.2) t.property.1,
    (mul_le_mul_of_nonneg_left t.property.2 (sub_nonneg.mpr s.property.2)).trans (by linarith [s.property.1])⟩⟩

def center {n : ℕ} (P : Sphere n) (v : equator P) : diagonal P v :=
  (0, EquatorHemisphereContraction.center P v)

def contraction {n : ℕ} (P : Sphere n) (v : equator P) :
    TopCat.Homotopy (𝟙 (diagonal P v)) (TopCat.ofHom (ContinuousMap.const (diagonal P v) (center P v))) where
  toFun z := (contractTime z.1 z.2.1, EquatorHemisphereContraction.contraction P v (z.1, z.2.2))
  continuous_toFun := by
    have ht : Continuous (fun z : ClosedInterval × diagonal P v => contractTime z.1 z.2.1) := by
      unfold contractTime
      fun_prop
    have hv : Continuous (fun z : ClosedInterval × diagonal P v => (z.1, z.2.2)) := continuous_fst.prodMk continuous_snd.snd
    exact ht.prodMk ((EquatorHemisphereContraction.contraction P v).continuous.comp hv)
  map_zero_left z := by
    apply Prod.ext
    · apply Subtype.ext
      change (1 - (0 : ℝ)) * (z.1 : ℝ) = (z.1 : ℝ)
      ring
    · exact (EquatorHemisphereContraction.contraction P v).map_zero_left z.2
  map_one_left z := by
    apply Prod.ext
    · apply Subtype.ext
      change (1 - (1 : ℝ)) * (z.1 : ℝ) = 0
      ring
    · exact (EquatorHemisphereContraction.contraction P v).map_one_left z.2

theorem positive_cohomology_zero {n : ℕ} (P : Sphere n) (v : equator P) (q : ℕ) (hq : q ≠ 0)
    (a : cohomologyZMod2 (diagonal P v) q) : a = 0 := by
  have he := LoopSweepTwoPiece.cohomology_homotopy (contraction P v) q a
  rw [Finsler.DiagonalCohomology.pullback_id] at he
  exact he.trans (NativeMatchingTestedPairing.constant_pullback_zero (diagonal P v) (diagonal P v) (center P v) q hq a)

def seamCochain {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :=
  cochainPullback (diagonalMap P v) (n - 1)
    (RelativeCupCochain.toAmbient (pair P v ρ) (n - 1) (primitive hn P v hρ hρ1))

theorem seam_closed {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ((cochainCxZMod2 (diagonal P v)).d (n - 1) (n - 1 + 1)).hom (seamCochain hn P v hρ hρ1) = 0 := by
  have he : n - 1 + 1 = n := by omega
  rw [he]
  exact diagonal_primitive_closed hn P v hρ hρ1

theorem seam_class_zero {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    CochainClass.classOf (cochainCxZMod2 (diagonal P v)) (n - 1) (seamCochain hn P v hρ hρ1)
      (seam_closed hn P v hρ hρ1) = 0 :=
  positive_cohomology_zero P v (n - 1) (by omega) _

def seamPrimitive {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :=
  CochainClassExact.primitive (cochainCxZMod2 (diagonal P v)) (n - 1) (by omega)
    (seamCochain hn P v hρ hρ1) 0
    (seam_closed hn P v hρ hρ1) (map_zero _)
    ((seam_class_zero hn P v hρ hρ1).trans (CochainClass.classOf_zero _ _ (map_zero _)).symm)

theorem seamPrimitive_d {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ((cochainCxZMod2 (diagonal P v)).d ((n - 1) - 1) (n - 1)).hom (seamPrimitive hn P v hρ hρ1) =
      seamCochain hn P v hρ hρ1 := by
  have he := CochainClassExact.primitive_d (cochainCxZMod2 (diagonal P v)) (n - 1) (by omega)
    (seamCochain hn P v hρ hρ1) 0
    (seam_closed hn P v hρ hρ1) (map_zero _)
    ((seam_class_zero hn P v hρ hρ1).trans (CochainClass.classOf_zero _ _ (map_zero _)).symm)
  exact he.trans (sub_zero _)

end
end Finsler.CommonMeridianSeamPrimitive
