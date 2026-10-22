module

public import Finsler.Topology.NormalizedDiagonalCocycle

/-! A far-supported primitive from the actual normalized endpoint-vanishing
Thom cocycle to the original specified representative. -/

@[expose] public section
namespace Finsler.NormalizedThomComparison

open CategoryTheory SphereOddDegree
open Finsler.CochainComparison Finsler.DiagonalCohomology Finsler.FarDiagonalCohomology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem classes_equal (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    CochainClass.classOf (RelativeCup.cx (farPair n ρ)) n
      (NormalizedDiagonalCocycle.relativeCocycle n (by omega) hρ)
      (NormalizedDiagonalCocycle.relative_closed n (by omega) hρ) =
    CochainClass.classOf (RelativeCup.cx (farPair n ρ)) n
      (FarThomRepresentative.specified n (by omega) hρ)
      (FarThomRepresentative.specified_closed n (by omega) hρ) :=
  (NormalizedDiagonalCocycle.relativeClass_specified n hn hρ hρ2).trans
    (FarThomRepresentative.specified_class n (by omega) hρ).symm

def relativePrimitive (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    RelativeCupCochain.relative (farPair n ρ) (n - 1) :=
  CochainClassExact.primitive (RelativeCup.cx (farPair n ρ)) n (by omega)
    (NormalizedDiagonalCocycle.relativeCocycle n (by omega) hρ)
    (FarThomRepresentative.specified n (by omega) hρ)
    (NormalizedDiagonalCocycle.relative_closed n (by omega) hρ)
    (FarThomRepresentative.specified_closed n (by omega) hρ) (classes_equal n hn hρ hρ2)

theorem relativePrimitive_boundary (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    ((RelativeCup.cx (farPair n ρ)).d (n - 1) n).hom (relativePrimitive n hn hρ hρ2) =
      NormalizedDiagonalCocycle.relativeCocycle n (by omega) hρ -
        FarThomRepresentative.specified n (by omega) hρ :=
  CochainClassExact.primitive_d (RelativeCup.cx (farPair n ρ)) n (by omega)
    (NormalizedDiagonalCocycle.relativeCocycle n (by omega) hρ)
    (FarThomRepresentative.specified n (by omega) hρ)
    (NormalizedDiagonalCocycle.relative_closed n (by omega) hρ)
    (FarThomRepresentative.specified_closed n (by omega) hρ) (classes_equal n hn hρ hρ2)

def ambientPrimitive (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    singularCochainGroup (ZMod 2) (product n) (n - 1) :=
  RelativeCupCochain.toAmbient (farPair n ρ) (n - 1) (relativePrimitive n hn hρ hρ2)

theorem ambientPrimitive_supported (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    cochainPullback (farPair n ρ).map (n - 1) (ambientPrimitive n hn hρ hρ2) = 0 :=
  RelativeCupCochain.restriction_toAmbient (farPair n ρ) (n - 1) (relativePrimitive n hn hρ hρ2)

theorem ambientPrimitive_boundary (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    ((cochainCxZMod2 (product n)).d (n - 1) n).hom (ambientPrimitive n hn hρ hρ2) =
      NormalizedDiagonalCocycle.ambient n (by omega) hρ -
        DiagonalCocycle.ambientCocycle n (by omega) := by
  have he := ConcreteCategory.congr_hom ((RelativeCup.ambientMap (farPair n ρ)).comm (n - 1) n)
    (relativePrimitive n hn hρ hρ2)
  change ((cochainCxZMod2 (product n)).d (n - 1) n).hom (ambientPrimitive n hn hρ hρ2) =
    RelativeCupCochain.toAmbient (farPair n ρ) n
      (((RelativeCup.cx (farPair n ρ)).d (n - 1) n).hom (relativePrimitive n hn hρ hρ2)) at he
  rw [he, relativePrimitive_boundary, map_sub, NormalizedDiagonalCocycle.relative_toAmbient,
    FarThomRepresentative.specified_toAmbient]

end
end Finsler.NormalizedThomComparison
