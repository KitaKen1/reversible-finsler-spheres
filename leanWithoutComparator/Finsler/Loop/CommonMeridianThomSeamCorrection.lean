module

public import Finsler.Loop.CommonMeridianSeamPrimitive
public import Finsler.Loop.CochainExtensionAvoidance
public import Finsler.Loop.TubeExtensionSquare

/-! Correct the SAME coherent Thom primitive on the time diagonal.
The seam's lower primitive is extended by zero on the singular-simplex
basis. That extension is literally zero on the disjoint exterior.
Subtract its coboundary: preserve the original Thom boundary, preserve
exterior zero, and obtain literal diagonal zero. No full-cap or scalar
vanishing is inferred before the original cap comparison is proved. -/
@[expose] public section
namespace Finsler.CommonMeridianThomSeamCorrection
open CategoryTheory SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.CommonMeridianThomPrimitive Finsler.CommonMeridianSeamPrimitive
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def diagonalSet {n : ℕ} (P : Sphere n) (v : equator P) : Set (base P v) := {z | z.1.1 = z.1.2}

def toDiagonal {n : ℕ} (P : Sphere n) (v : equator P) : TopCat.of (diagonalSet P v) ⟶ diagonal P v :=
  TopCat.ofHom ⟨fun z => (z.val.1.1, z.val.2), by fun_prop⟩

def diagonalSection {n : ℕ} (P : Sphere n) (v : equator P) : diagonal P v ⟶ TopCat.of (diagonalSet P v) :=
  TopCat.ofHom ⟨fun z => ⟨((z.1, z.1), z.2), rfl⟩, by fun_prop⟩

theorem diagonal_factor {n : ℕ} (P : Sphere n) (v : equator P) :
    diagonalSection P v ≫ SupportedCap.subspaceMap (base P v) (diagonalSet P v) = diagonalMap P v := by
  apply TopCat.ext
  intro z
  rfl

theorem diagonal_retract {n : ℕ} (P : Sphere n) (v : equator P) :
    diagonalSection P v ≫ toDiagonal P v = 𝟙 (diagonal P v) := by
  apply TopCat.ext
  intro z
  rfl

def extension {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :=
  TubeCochainExtension.extend (base P v) (diagonalSet P v) ((n - 1) - 1)
    (cochainPullback (toDiagonal P v) ((n - 1) - 1) (seamPrimitive hn P v hρ hρ1))

theorem extension_diagonal {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cochainPullback (diagonalMap P v) ((n - 1) - 1) (extension hn P v hρ hρ1) = seamPrimitive hn P v hρ hρ1 := by
  rw [← diagonal_factor, extension, TubeExtensionSquare.pullback_on_map, ← pullback_comp, diagonal_retract]
  exact congrArg (fun f => (f.f ((n - 1) - 1)).hom (seamPrimitive hn P v hρ hρ1))
    (singularCochainComplexZMod2.map_id (Opposite.op (diagonal P v)))

theorem far_avoids_diagonal {n : ℕ} (P : Sphere n) (v : equator P) {ρ : ℝ} (hρ : 0 < ρ)
    (z : OrthogonalRelativeThomZero.exterior (firstPoint P v) (secondPoint P v) (ρ := ρ)) : z.val ∉ diagonalSet P v := by
  intro hz
  have he : secondPoint P v z.val = firstPoint P v z.val := by
    change RationalSphereArc.point (outgoing P z.val.2.val) z.val.1.2 =
      RationalSphereArc.point (outgoing P z.val.2.val) z.val.1.1
    exact congrArg (RationalSphereArc.point (outgoing P z.val.2.val)) hz.symm
  have hf := z.property
  change ρ ≤ ‖(secondPoint P v z.val : Ambient n) - (firstPoint P v z.val : Ambient n)‖ at hf
  rw [he, sub_self, norm_zero] at hf
  exact (not_le_of_gt hρ) hf

theorem extension_far_zero {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cochainPullback (pair P v ρ).map ((n - 1) - 1) (extension hn P v hρ hρ1) = 0 :=
  CochainExtensionAvoidance.pullback_zero (diagonalSet P v) (pair P v ρ).map
    (far_avoids_diagonal P v hρ) _ _

def corrected {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    singularCochainGroup (ZMod 2) (base P v) (n - 1) := by
  let a : singularCochainGroup (ZMod 2) (base P v) (n - 1) :=
    RelativeCupCochain.toAmbient (pair P v ρ) (n - 1) (primitive hn P v hρ hρ1)
  let b : singularCochainGroup (ZMod 2) (base P v) (n - 1) :=
    ((cochainCxZMod2 (base P v)).d ((n - 1) - 1) (n - 1)).hom (extension hn P v hρ hρ1)
  exact a - b

theorem corrected_d {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ((cochainCxZMod2 (base P v)).d (n - 1) n).hom (corrected hn P v hρ hρ1) =
      cochainPullback (OrthogonalSphereEscape.pair (firstPoint P v) (secondPoint P v)) n
        (NormalizedDiagonalCocycle.ambient n (by omega) hρ) := by
  have hz := ConcreteCategory.congr_hom ((cochainCxZMod2 (base P v)).d_comp_d ((n - 1) - 1) (n - 1) n)
    (extension hn P v hρ hρ1)
  change ((cochainCxZMod2 (base P v)).d (n - 1) n).hom
    (((cochainCxZMod2 (base P v)).d ((n - 1) - 1) (n - 1)).hom (extension hn P v hρ hρ1)) = 0 at hz
  rw [corrected, map_sub, ambient_d, hz, sub_zero]

private theorem pullback_sub {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ)
    (a b : singularCochainGroup (ZMod 2) Y q) :
    cochainPullback f q (a - b) = cochainPullback f q a - cochainPullback f q b :=
  map_sub ((singularCochainComplexZMod2.map f.op).f q).hom a b

theorem corrected_far_zero {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cochainPullback (pair P v ρ).map (n - 1) (corrected hn P v hρ hρ1) = 0 := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (pair P v ρ).map.op).comm ((n - 1) - 1) (n - 1))
    (extension hn P v hρ hρ1)
  change ((cochainCxZMod2 (pair P v ρ).snd).d ((n - 1) - 1) (n - 1)).hom
    (cochainPullback (pair P v ρ).map ((n - 1) - 1) (extension hn P v hρ hρ1)) =
    cochainPullback (pair P v ρ).map (n - 1)
      (((cochainCxZMod2 (base P v)).d ((n - 1) - 1) (n - 1)).hom (extension hn P v hρ hρ1)) at he
  rw [extension_far_zero, map_zero] at he
  rw [corrected, pullback_sub, primitive_far_zero, ← he, sub_self]

theorem corrected_diagonal_zero {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v : equator P)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cochainPullback (diagonalMap P v) (n - 1) (corrected hn P v hρ hρ1) = 0 := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (diagonalMap P v).op).comm ((n - 1) - 1) (n - 1))
    (extension hn P v hρ hρ1)
  change ((cochainCxZMod2 (diagonal P v)).d ((n - 1) - 1) (n - 1)).hom
    (cochainPullback (diagonalMap P v) ((n - 1) - 1) (extension hn P v hρ hρ1)) =
    cochainPullback (diagonalMap P v) (n - 1)
      (((cochainCxZMod2 (base P v)).d ((n - 1) - 1) (n - 1)).hom (extension hn P v hρ hρ1)) at he
  rw [extension_diagonal, seamPrimitive_d] at he
  rw [corrected, pullback_sub, ← he]
  exact sub_self (seamCochain hn P v hρ hρ1)

end
end Finsler.CommonMeridianThomSeamCorrection
