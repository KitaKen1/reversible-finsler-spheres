module

public import Finsler.Loop.NativeSameLegThomReduction

/-! Choose the Thom primitive on ONLY the common meridian's two
times and local direction. All unused equator factors are absent.
Both actual partial same-leg families map to this SAME base, and
their diagonal seams map to its SAME time diagonal. This prepares a
coherent seam correction rather than unrelated primitive choices. -/
@[expose] public section
namespace Finsler.CommonMeridianThomPrimitive
open CategoryTheory SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelEvaluation Finsler.RationalSphereArc Finsler.NativeSameLegClockGeometry
open Finsler.SameMeridianTransverseEscape
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

abbrev base {n : ℕ} (P : Sphere n) (v : equator P) : TopCat.{0} :=
  TopCat.of ((ClosedInterval × ClosedInterval) × MeridianTransverseField.hemisphere P v)

def firstPoint {n : ℕ} (P : Sphere n) (v : equator P) : base P v ⟶ sphere n :=
  TopCat.ofHom ⟨fun z => point (outgoing P z.2.val) z.1.1, by
    exact (point_continuous n).comp
      (((show Continuous (fun z : (ClosedInterval × ClosedInterval) × MeridianTransverseField.hemisphere P v =>
        outgoing P z.2.val) by unfold outgoing; fun_prop)).prodMk (by fun_prop))⟩

def secondPoint {n : ℕ} (P : Sphere n) (v : equator P) : base P v ⟶ sphere n :=
  TopCat.ofHom ⟨fun z => point (outgoing P z.2.val) z.1.2, by
    exact (point_continuous n).comp
      (((show Continuous (fun z : (ClosedInterval × ClosedInterval) × MeridianTransverseField.hemisphere P v =>
        outgoing P z.2.val) by unfold outgoing; fun_prop)).prodMk (by fun_prop))⟩

def normalPoint {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) : base P v ⟶ sphere n :=
  TopCat.ofHom ⟨fun z => MeridianTransverseField.field hn P v z.2,
    (MeridianTransverseField.field_continuous hn P v).comp continuous_snd⟩

theorem first_perpendicular {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) (z : base P v) :
    ⟪(firstPoint P v z : Ambient n), (normalPoint hn P v z : Ambient n)⟫ = 0 :=
  north_perp P _ _ (MeridianTransverseField.field_pole_perp hn P v z.2)
    (MeridianTransverseField.field_perp hn P v z.2) z.1.1

theorem second_perpendicular {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) (z : base P v) :
    ⟪(secondPoint P v z : Ambient n), (normalPoint hn P v z : Ambient n)⟫ = 0 :=
  north_perp P _ _ (MeridianTransverseField.field_pole_perp hn P v z.2)
    (MeridianTransverseField.field_perp hn P v z.2) z.1.2

abbrev pair {n : ℕ} (P : Sphere n) (v : equator P) (ρ : ℝ) :=
  OrthogonalRelativeThomZero.source (firstPoint P v) (secondPoint P v) (ρ := ρ)

def primitive {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :=
  OrthogonalThomPrimitive.primitive (firstPoint P v) (secondPoint P v) (normalPoint hn P v)
    (second_perpendicular hn P v) (first_perpendicular hn P v) hρ hρ1 (by omega)

theorem primitive_d {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ((RelativeCup.cx (pair P v ρ)).d (n - 1) n).hom (primitive hn P v hρ hρ1) =
      OrthogonalThomPrimitive.cocycle (firstPoint P v) (secondPoint P v) hρ (by omega) :=
  OrthogonalThomPrimitive.primitive_d (firstPoint P v) (secondPoint P v) (normalPoint hn P v)
    (second_perpendicular hn P v) (first_perpendicular hn P v) hρ hρ1 (by omega)

theorem primitive_far_zero {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cochainPullback (pair P v ρ).map (n - 1)
      (RelativeCupCochain.toAmbient (pair P v ρ) (n - 1) (primitive hn P v hρ hρ1)) = 0 :=
  RelativeCupCochain.restriction_toAmbient (pair P v ρ) (n - 1) _

theorem ambient_d {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ((cochainCxZMod2 (base P v)).d (n - 1) n).hom
      (RelativeCupCochain.toAmbient (pair P v ρ) (n - 1) (primitive hn P v hρ hρ1)) =
      cochainPullback (OrthogonalSphereEscape.pair (firstPoint P v) (secondPoint P v)) n
        (NormalizedDiagonalCocycle.ambient n (by omega) hρ) := by
  have hc := ConcreteCategory.congr_hom
    (((pair P v ρ).singularCochainComplexShortComplex coeff (ZMod 2) coeff).f.comm (n - 1) n)
    (primitive hn P v hρ hρ1)
  change ((cochainCxZMod2 (base P v)).d (n - 1) n).hom
      (RelativeCupCochain.toAmbient (pair P v ρ) (n - 1) (primitive hn P v hρ hρ1)) =
      RelativeCupCochain.toAmbient (pair P v ρ) n
        (((RelativeCup.cx (pair P v ρ)).d (n - 1) n).hom (primitive hn P v hρ hρ1)) at hc
  rw [primitive_d, OrthogonalThomPrimitive.cocycle, RelativeCupCochain.toAmbient_pullback,
    NormalizedDiagonalCocycle.relative_toAmbient, NativeSameLegThomReduction.coordinate_fst] at hc
  exact hc

abbrev diagonal {n : ℕ} (P : Sphere n) (v : equator P) :=
  TopCat.of (ClosedInterval × MeridianTransverseField.hemisphere P v)

def diagonalMap {n : ℕ} (P : Sphere n) (v : equator P) : diagonal P v ⟶ base P v :=
  TopCat.ofHom ⟨fun z => ((z.1, z.1), z.2), by fun_prop⟩

theorem diagonal_cochain_zero {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (diagonalMap P v ≫ OrthogonalSphereEscape.pair (firstPoint P v) (secondPoint P v)) n
      (NormalizedDiagonalCocycle.ambient n (by omega) hρ) = 0 :=
  NormalizedDiagonalCocycle.pullback_zero_of_diagonal (by omega) hρ _ (fun _ => rfl)

theorem diagonal_primitive_closed {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ((cochainCxZMod2 (diagonal P v)).d (n - 1) n).hom
      (cochainPullback (diagonalMap P v) (n - 1)
        (RelativeCupCochain.toAmbient (pair P v ρ) (n - 1) (primitive hn P v hρ hρ1))) = 0 := by
  have hc := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (diagonalMap P v).op).comm (n - 1) n)
      (RelativeCupCochain.toAmbient (pair P v ρ) (n - 1) (primitive hn P v hρ hρ1))
  change _ = cochainPullback (diagonalMap P v) n
    (((cochainCxZMod2 (base P v)).d (n - 1) n).hom
      (RelativeCupCochain.toAmbient (pair P v ρ) (n - 1) (primitive hn P v hρ hρ1))) at hc
  rw [ambient_d, ← Finsler.SupportedCapNaturality.pullback_comp, diagonal_cochain_zero hn] at hc
  exact hc

end
end Finsler.CommonMeridianThomPrimitive
