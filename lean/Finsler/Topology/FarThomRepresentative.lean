module

public import Finsler.Topology.FarDiagonalCohomology
public import Finsler.Topology.CochainClassExact
public import Finsler.Topology.BorelCrossing

/-! An actual far-supported primitive compares the endpoint-vanishing
diagonal cocycle with the original specified Thom cocycle. The primitive
is obtained in the actual far-relative complex, retaining its support. -/

@[expose] public section
namespace Finsler.FarThomRepresentative

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison
open Finsler.DiagonalCohomology Finsler.FarDiagonalCohomology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def specified (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.relative (farPair n ρ) n :=
  RelativeCupCochain.pullback (fromDeleted n hρ) n (DiagonalCocycle.relativeCocycle n hn)

def endpointVanishing (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.relative (farPair n ρ) n :=
  RelativeCupCochain.pullback (fromAvoidance n ρ) n
    (DiagonalAvoidanceCocycle.relativeCocycle n hn hρ)

theorem specified_closed (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    ((RelativeCup.cx (farPair n ρ)).d n (n + 1)).hom (specified n hn hρ) = 0 :=
  CochainClass.closed_map (RelativeCup.cx (diagonalPair n))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff)
      (fromDeleted n hρ)) n (DiagonalCocycle.relativeCocycle n hn)
    (DiagonalCocycle.relative_closed n hn)

theorem endpointVanishing_closed (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    ((RelativeCup.cx (farPair n ρ)).d n (n + 1)).hom (endpointVanishing n hn hρ) = 0 :=
  CochainClass.closed_map (RelativeCup.cx (DiagonalAvoidanceCocycle.avoidancePair n ρ))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff)
      (fromAvoidance n ρ)) n (DiagonalAvoidanceCocycle.relativeCocycle n hn hρ)
    (DiagonalAvoidanceCocycle.relative_closed n hn hρ)

theorem specified_class (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    CochainClass.classOf (RelativeCup.cx (farPair n ρ)) n (specified n hn hρ)
      (specified_closed n hn hρ) = thomClass n hn hρ := by
  let f := TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff)
    (fromDeleted n hρ)
  have he := CochainClass.classOf_map (RelativeCup.cx (diagonalPair n)) f n
    (DiagonalCocycle.relativeCocycle n hn) (DiagonalCocycle.relative_closed n hn)
    (specified_closed n hn hρ)
  exact he.symm.trans (congrArg _ (DiagonalCocycle.relative_cocycle_class n hn))

theorem endpointVanishing_class (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    CochainClass.classOf (RelativeCup.cx (farPair n ρ)) n (endpointVanishing n hn hρ)
      (endpointVanishing_closed n hn hρ) = avoidanceClass n hn hρ := by
  let f := TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff)
    (fromAvoidance n ρ)
  have he := CochainClass.classOf_map
    (RelativeCup.cx (DiagonalAvoidanceCocycle.avoidancePair n ρ)) f n
    (DiagonalAvoidanceCocycle.relativeCocycle n hn hρ)
    (DiagonalAvoidanceCocycle.relative_closed n hn hρ) (endpointVanishing_closed n hn hρ)
  have hc := CochainClass.classOf_representative
    (RelativeCup.cx (DiagonalAvoidanceCocycle.avoidancePair n ρ)) n
    (DiagonalAvoidanceCocycle.relativeClass n hn hρ)
  exact he.symm.trans (congrArg _ hc)

theorem classes_equal (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    CochainClass.classOf (RelativeCup.cx (farPair n ρ)) n (endpointVanishing n (by omega) hρ)
      (endpointVanishing_closed n (by omega) hρ) =
    CochainClass.classOf (RelativeCup.cx (farPair n ρ)) n (specified n (by omega) hρ)
      (specified_closed n (by omega) hρ) :=
  (endpointVanishing_class n (by omega) hρ).trans
    ((thom_comparison n hn hρ hρ2).trans (specified_class n (by omega) hρ).symm)

def relativePrimitive (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    RelativeCupCochain.relative (farPair n ρ) (n - 1) :=
  CochainClassExact.primitive (RelativeCup.cx (farPair n ρ)) n (by omega)
    (endpointVanishing n (by omega) hρ) (specified n (by omega) hρ)
    (endpointVanishing_closed n (by omega) hρ) (specified_closed n (by omega) hρ)
    (classes_equal n hn hρ hρ2)

theorem relativePrimitive_boundary (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    ((RelativeCup.cx (farPair n ρ)).d (n - 1) n).hom (relativePrimitive n hn hρ hρ2) =
      endpointVanishing n (by omega) hρ - specified n (by omega) hρ :=
  CochainClassExact.primitive_d (RelativeCup.cx (farPair n ρ)) n (by omega)
    (endpointVanishing n (by omega) hρ) (specified n (by omega) hρ)
    (endpointVanishing_closed n (by omega) hρ) (specified_closed n (by omega) hρ)
    (classes_equal n hn hρ hρ2)

theorem specified_toAmbient (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.toAmbient (farPair n ρ) n (specified n hn hρ) =
      DiagonalCocycle.ambientCocycle n hn := by
  change RelativeCupCochain.toAmbient (farPair n ρ) n
    (RelativeCupCochain.pullback (fromDeleted n hρ) n (DiagonalCocycle.relativeCocycle n hn)) = _
  rw [RelativeCupCochain.toAmbient_pullback, fromDeleted_fst]
  exact BorelCrossing.cochain_id n _

theorem endpointVanishing_toAmbient (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.toAmbient (farPair n ρ) n (endpointVanishing n hn hρ) =
      DiagonalAvoidanceCocycle.ambientCocycle n hn hρ := by
  change RelativeCupCochain.toAmbient (farPair n ρ) n
    (RelativeCupCochain.pullback (fromAvoidance n ρ) n
      (DiagonalAvoidanceCocycle.relativeCocycle n hn hρ)) = _
  rw [RelativeCupCochain.toAmbient_pullback, fromAvoidance_fst]
  exact BorelCrossing.cochain_id n _

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
      DiagonalAvoidanceCocycle.ambientCocycle n (by omega) hρ -
        DiagonalCocycle.ambientCocycle n (by omega) := by
  have he := ConcreteCategory.congr_hom ((RelativeCup.ambientMap (farPair n ρ)).comm (n - 1) n)
    (relativePrimitive n hn hρ hρ2)
  change ((cochainCxZMod2 (product n)).d (n - 1) n).hom (ambientPrimitive n hn hρ hρ2) =
    RelativeCupCochain.toAmbient (farPair n ρ) n
      (((RelativeCup.cx (farPair n ρ)).d (n - 1) n).hom (relativePrimitive n hn hρ hρ2)) at he
  rw [he, relativePrimitive_boundary, map_sub, endpointVanishing_toAmbient, specified_toAmbient]

end
end Finsler.FarThomRepresentative
