module

public import Finsler.Topology.NormalizedDiagonalCocycle
public import Finsler.Topology.DiagonalSymmetry
public import Finsler.Topology.CochainClassExact

/-! The ORIGINAL normalized far-relative Thom class is symmetric.
Its actual relative primitive stays supported on the SAME far pair.
This is a comparison for the specified normalized cochain, not a
replacement diagonal representative or an assigned local cap count. -/
@[expose] public section
namespace Finsler.FarNormalizedDiagonalSymmetry
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.DiagonalCohomology
open Finsler.FarDiagonalCohomology Finsler.DiagonalSymmetry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def exchangePair (n : ℕ) (ρ : ℝ) : farPair n ρ ⟶ farPair n ρ :=
  TopPair.ofSubsetMap (B := DiagonalAvoidanceCocycle.far n ρ)
    (B' := DiagonalAvoidanceCocycle.far n ρ) (exchange n) (by
      intro z hz
      change ρ ≤ ‖(z.1 : Ambient n) - z.2‖
      rw [norm_sub_rev]
      exact hz)

theorem exchangePair_fst (n : ℕ) (ρ : ℝ) : TopPair.Hom.fst (exchangePair n ρ) = exchange n := by
  ext z : 1
  exact TopPair.ofSubsetMap_fst_apply (B := DiagonalAvoidanceCocycle.far n ρ)
    (B' := DiagonalAvoidanceCocycle.far n ρ) (exchange n)
    (by intro x hx; change ρ ≤ ‖(x.1 : Ambient n) - x.2‖; rw [norm_sub_rev]; exact hx) z

theorem relativeClass_exchange (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (exchangePair n ρ) n).hom (NormalizedDiagonalCocycle.relativeClass n (by omega) hρ) =
        NormalizedDiagonalCocycle.relativeClass n (by omega) hρ := by
  apply relativeToPool_injective n hn hρ hρ2
  have he := congrArg (fun f => f.hom (NormalizedDiagonalCocycle.relativeClass n (by omega) hρ))
    (relative_to_absolute_natural (exchangePair n ρ) n)
  calc
    _ = (cohPullback (TopPair.Hom.fst (exchangePair n ρ)) n).hom
        ((relativeToPool (farPair n ρ) n).hom (NormalizedDiagonalCocycle.relativeClass n (by omega) hρ)) := he
    _ = (cohPullback (exchange n) n).hom (ambientClass n (by omega)) := by
      rw [exchangePair_fst, NormalizedDiagonalCocycle.relativeClass_image]
      rfl
    _ = ambientClass n (by omega) := ambientClass_exchange n (by omega)
    _ = _ := (NormalizedDiagonalCocycle.relativeClass_image n (by omega) hρ).symm

def swappedRelative (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.relative (farPair n ρ) n :=
  RelativeCupCochain.pullback (exchangePair n ρ) n (NormalizedDiagonalCocycle.relativeCocycle n hn hρ)

theorem swapped_closed (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    ((RelativeCup.cx (farPair n ρ)).d n (n + 1)).hom (swappedRelative n hn hρ) = 0 :=
  CochainClass.closed_map (RelativeCup.cx (farPair n ρ))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (exchangePair n ρ)) n
    (NormalizedDiagonalCocycle.relativeCocycle n hn hρ) (NormalizedDiagonalCocycle.relative_closed n hn hρ)

theorem swapped_class (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    CochainClass.classOf (RelativeCup.cx (farPair n ρ)) n (swappedRelative n (by omega) hρ)
      (swapped_closed n (by omega) hρ) = NormalizedDiagonalCocycle.relativeClass n (by omega) hρ := by
  have he := CochainClass.classOf_map (RelativeCup.cx (farPair n ρ))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (exchangePair n ρ)) n
    (NormalizedDiagonalCocycle.relativeCocycle n (by omega) hρ)
    (NormalizedDiagonalCocycle.relative_closed n (by omega) hρ) (swapped_closed n (by omega) hρ)
  exact he.symm.trans (relativeClass_exchange n hn hρ hρ2)

def relativePrimitive (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    RelativeCupCochain.relative (farPair n ρ) (n - 1) :=
  CochainClassExact.primitive (RelativeCup.cx (farPair n ρ)) n (by omega)
    (swappedRelative n (by omega) hρ) (NormalizedDiagonalCocycle.relativeCocycle n (by omega) hρ)
    (swapped_closed n (by omega) hρ) (NormalizedDiagonalCocycle.relative_closed n (by omega) hρ)
    (swapped_class n hn hρ hρ2)

theorem relativePrimitive_boundary (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    ((RelativeCup.cx (farPair n ρ)).d (n - 1) n).hom (relativePrimitive n hn hρ hρ2) =
      swappedRelative n (by omega) hρ - NormalizedDiagonalCocycle.relativeCocycle n (by omega) hρ :=
  CochainClassExact.primitive_d (RelativeCup.cx (farPair n ρ)) n (by omega)
    (swappedRelative n (by omega) hρ) (NormalizedDiagonalCocycle.relativeCocycle n (by omega) hρ)
    (swapped_closed n (by omega) hρ) (NormalizedDiagonalCocycle.relative_closed n (by omega) hρ)
    (swapped_class n hn hρ hρ2)

def ambientPrimitive (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    singularCochainGroup (ZMod 2) (product n) (n - 1) :=
  RelativeCupCochain.toAmbient (farPair n ρ) (n - 1) (relativePrimitive n hn hρ hρ2)

theorem ambientPrimitive_supported (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    cochainPullback (farPair n ρ).map (n - 1) (ambientPrimitive n hn hρ hρ2) = 0 :=
  RelativeCupCochain.restriction_toAmbient (farPair n ρ) (n - 1) (relativePrimitive n hn hρ hρ2)

theorem swapped_toAmbient (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.toAmbient (farPair n ρ) n (swappedRelative n hn hρ) =
      cochainPullback (exchange n) n (NormalizedDiagonalCocycle.ambient n hn hρ) := by
  unfold swappedRelative
  rw [RelativeCupCochain.toAmbient_pullback, exchangePair_fst,
    NormalizedDiagonalCocycle.relative_toAmbient]

theorem ambientPrimitive_boundary (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    ((cochainCxZMod2 (product n)).d (n - 1) n).hom (ambientPrimitive n hn hρ hρ2) =
      cochainPullback (exchange n) n (NormalizedDiagonalCocycle.ambient n (by omega) hρ) -
        NormalizedDiagonalCocycle.ambient n (by omega) hρ := by
  have he := ConcreteCategory.congr_hom
    ((RelativeCup.ambientMap (farPair n ρ)).comm (n - 1) n) (relativePrimitive n hn hρ hρ2)
  change ((cochainCxZMod2 (product n)).d (n - 1) n).hom (ambientPrimitive n hn hρ hρ2) =
    RelativeCupCochain.toAmbient (farPair n ρ) n
      (((RelativeCup.cx (farPair n ρ)).d (n - 1) n).hom (relativePrimitive n hn hρ hρ2)) at he
  rw [he, relativePrimitive_boundary, map_sub, swapped_toAmbient, NormalizedDiagonalCocycle.relative_toAmbient]

end
end Finsler.FarNormalizedDiagonalSymmetry
