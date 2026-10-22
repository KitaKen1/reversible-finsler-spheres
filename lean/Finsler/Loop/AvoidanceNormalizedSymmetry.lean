module

public import Finsler.Topology.AnnularThomComparison
public import Finsler.Topology.DiagonalSymmetry

/-! Symmetry of the SAME normalized Thom cochain relative to the actual
far union diagonal. The chosen primitive vanishes on both carriers;
this stronger support controls the original cut-time endpoints. -/
@[expose] public section
namespace Finsler.AvoidanceNormalizedSymmetry
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.DiagonalCohomology
open Finsler.DiagonalAvoidanceCocycle Finsler.DiagonalSymmetry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem exchange_avoids (n : ℕ) (ρ : ℝ) (z : product n) (hz : z ∈ avoid n ρ) :
    exchange n z ∈ avoid n ρ := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  cases i with
  | false =>
    change ρ ≤ ‖(z.1 : Ambient n) - z.2‖
    rw [norm_sub_rev]
    exact hi
  | true => exact (show z.1 = z.2 from hi).symm

theorem swapped_supported (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (inclusion n ρ) n
      (cochainPullback (exchange n) n (NormalizedDiagonalCocycle.ambient n hn hρ)) = 0 :=
  SupportedCapNaturality.pullback_support (exchange n) (avoid n ρ) (avoid n ρ)
    (exchange_avoids n ρ) n _ (NormalizedDiagonalCocycle.avoidance_supported n hn hρ)

def swapped (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.relative (avoidancePair n ρ) n :=
  (RelativeCupCochain.exists_lift (avoidancePair n ρ) n
    (cochainPullback (exchange n) n (NormalizedDiagonalCocycle.ambient n hn hρ))
    (swapped_supported n hn hρ)).choose

theorem swapped_toAmbient (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.toAmbient (avoidancePair n ρ) n (swapped n hn hρ) =
      cochainPullback (exchange n) n (NormalizedDiagonalCocycle.ambient n hn hρ) :=
  (RelativeCupCochain.exists_lift (avoidancePair n ρ) n _ (swapped_supported n hn hρ)).choose_spec

theorem swapped_closed (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    ((RelativeCup.cx (avoidancePair n ρ)).d n (n + 1)).hom (swapped n hn hρ) = 0 := by
  change RelativeCupCochain.differential (avoidancePair n ρ) n (swapped n hn hρ) = 0
  apply RelativeCupCochain.toAmbient_injective (avoidancePair n ρ) (n + 1)
  rw [RelativeCupCochain.toAmbient_differential, swapped_toAmbient, map_zero]
  exact SupportedCapNaturality.pullback_closed (exchange n) n _ (NormalizedDiagonalCocycle.ambient_closed n hn hρ)

private theorem image_of_class (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (relativeToPool (avoidancePair n ρ) n).hom
      (CochainClass.classOf (RelativeCup.cx (avoidancePair n ρ)) n (swapped n hn hρ)
        (swapped_closed n hn hρ)) = ambientClass n hn := by
  have he := RelativeCup.relativeToPool_classOf (avoidancePair n ρ) n
    (swapped n hn hρ) (swapped_closed n hn hρ)
  have hm := CochainClass.classOf_map (cochainCxZMod2 (product n))
    (singularCochainComplexZMod2.map (exchange n).op) n
    (NormalizedDiagonalCocycle.ambient n hn hρ) (NormalizedDiagonalCocycle.ambient_closed n hn hρ)
    (SupportedCapNaturality.pullback_closed (exchange n) n _ (NormalizedDiagonalCocycle.ambient_closed n hn hρ))
  rw [NormalizedDiagonalCocycle.ambient_class] at hm
  exact he.trans ((CochainClass.classOf_congr _ n (swapped_toAmbient n hn hρ) _ _).trans
    (hm.symm.trans (ambientClass_exchange n hn)))

theorem classes_equal (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    CochainClass.classOf (RelativeCup.cx (avoidancePair n ρ)) n (swapped n (by omega) hρ)
      (swapped_closed n (by omega) hρ) =
    CochainClass.classOf (RelativeCup.cx (avoidancePair n ρ)) n (AnnularThomComparison.oldRelative n (by omega) hρ)
      (AnnularThomComparison.old_closed n (by omega) hρ) := by
  apply AvoidanceUniqueness.relativeToPool_injective n hn hρ hρ2
  have he := RelativeCup.relativeToPool_classOf (avoidancePair n ρ) n
    (AnnularThomComparison.oldRelative n (by omega) hρ) (AnnularThomComparison.old_closed n (by omega) hρ)
  exact (image_of_class n (by omega) hρ).trans
    (he.trans ((CochainClass.classOf_congr _ n (AnnularThomComparison.old_toAmbient n (by omega) hρ) _ _).trans
      (NormalizedDiagonalCocycle.ambient_class n (by omega) hρ))).symm

def relativePrimitive (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    RelativeCupCochain.relative (avoidancePair n ρ) (n - 1) :=
  CochainClassExact.primitive (RelativeCup.cx (avoidancePair n ρ)) n (by omega)
    (swapped n (by omega) hρ) (AnnularThomComparison.oldRelative n (by omega) hρ)
    (swapped_closed n (by omega) hρ) (AnnularThomComparison.old_closed n (by omega) hρ)
    (classes_equal n hn hρ hρ2)

theorem relativePrimitive_boundary (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    ((RelativeCup.cx (avoidancePair n ρ)).d (n - 1) n).hom (relativePrimitive n hn hρ hρ2) =
      swapped n (by omega) hρ - AnnularThomComparison.oldRelative n (by omega) hρ :=
  CochainClassExact.primitive_d (RelativeCup.cx (avoidancePair n ρ)) n (by omega)
    (swapped n (by omega) hρ) (AnnularThomComparison.oldRelative n (by omega) hρ)
    (swapped_closed n (by omega) hρ) (AnnularThomComparison.old_closed n (by omega) hρ)
    (classes_equal n hn hρ hρ2)

def ambientPrimitive (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    singularCochainGroup (ZMod 2) (product n) (n - 1) :=
  RelativeCupCochain.toAmbient (avoidancePair n ρ) (n - 1) (relativePrimitive n hn hρ hρ2)

theorem primitive_supported (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    cochainPullback (inclusion n ρ) (n - 1) (ambientPrimitive n hn hρ hρ2) = 0 :=
  RelativeCupCochain.restriction_toAmbient (avoidancePair n ρ) (n - 1) (relativePrimitive n hn hρ hρ2)

theorem primitive_boundary (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    ((cochainCxZMod2 (product n)).d (n - 1) n).hom (ambientPrimitive n hn hρ hρ2) =
      cochainPullback (exchange n) n (NormalizedDiagonalCocycle.ambient n (by omega) hρ) -
        NormalizedDiagonalCocycle.ambient n (by omega) hρ := by
  have he := ConcreteCategory.congr_hom ((RelativeCup.ambientMap (avoidancePair n ρ)).comm (n - 1) n)
    (relativePrimitive n hn hρ hρ2)
  change ((cochainCxZMod2 (product n)).d (n - 1) n).hom (ambientPrimitive n hn hρ hρ2) =
    RelativeCupCochain.toAmbient (avoidancePair n ρ) n
      (((RelativeCup.cx (avoidancePair n ρ)).d (n - 1) n).hom (relativePrimitive n hn hρ hρ2)) at he
  rw [he, relativePrimitive_boundary, map_sub, swapped_toAmbient, AnnularThomComparison.old_toAmbient]

theorem primitive_range_zero (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2)
    {X : TopCat.{0}} (f : X ⟶ product n) (hf : ∀ x, f x ∈ avoid n ρ) :
    cochainPullback f (n - 1) (ambientPrimitive n hn hρ hρ2) = 0 := by
  let g : X ⟶ TopCat.of (avoid n ρ) := TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ inclusion n ρ := by ext x : 1; rfl
  rw [he, SupportedCapNaturality.pullback_comp, primitive_supported]
  simp [cochainPullback]

end
end Finsler.AvoidanceNormalizedSymmetry
