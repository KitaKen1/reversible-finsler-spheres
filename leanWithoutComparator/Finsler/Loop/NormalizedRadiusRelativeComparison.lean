module

public import Finsler.Topology.AnnularThomComparison

/-! Compare two actual normalized diagonal Thom representatives relative
to the SAME outer far set union diagonal. The genuine comparison
primitive therefore vanishes on the far carrier and at time endpoints. -/

@[expose] public section
namespace Finsler.NormalizedRadiusRelativeComparison

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.DiagonalCohomology Finsler.DiagonalAvoidanceCocycle
open Finsler.SphereGeometry Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem avoid_subset (n : ℕ) {ρ H : ℝ} (hρH : ρ ≤ H) : avoid n H ⊆ avoid n ρ := by
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  cases i
  · exact hρH.trans hi
  · exact hi

def outerRestriction (n : ℕ) {ρ H : ℝ} (hρH : ρ ≤ H) : TopCat.of (avoid n H) ⟶ TopCat.of (avoid n ρ) :=
  TopCat.ofHom (ContinuousMap.inclusion (avoid_subset n hρH))

theorem outer_source (n : ℕ) {ρ H : ℝ} (hρH : ρ ≤ H) :
    outerRestriction n hρH ≫ inclusion n ρ = inclusion n H := rfl

theorem supported_outer (n : ℕ) (hn : 1 ≤ n) {ρ H : ℝ} (hρ : 0 < ρ) (hρH : ρ ≤ H) :
    cochainPullback (inclusion n H) n (NormalizedDiagonalCocycle.ambient n hn hρ) = 0 := by
  rw [← outer_source n hρH, pullback_comp, NormalizedDiagonalCocycle.avoidance_supported]
  exact map_zero _

def relative (n : ℕ) (hn : 1 ≤ n) {ρ H : ℝ} (hρ : 0 < ρ) (hρH : ρ ≤ H) :
    RelativeCupCochain.relative (avoidancePair n H) n :=
  (RelativeCupCochain.exists_lift (avoidancePair n H) n (NormalizedDiagonalCocycle.ambient n hn hρ)
    (supported_outer n hn hρ hρH)).choose

theorem toAmbient (n : ℕ) (hn : 1 ≤ n) {ρ H : ℝ} (hρ : 0 < ρ) (hρH : ρ ≤ H) :
    RelativeCupCochain.toAmbient (avoidancePair n H) n (relative n hn hρ hρH) =
      NormalizedDiagonalCocycle.ambient n hn hρ :=
  (RelativeCupCochain.exists_lift (avoidancePair n H) n (NormalizedDiagonalCocycle.ambient n hn hρ)
    (supported_outer n hn hρ hρH)).choose_spec

theorem closed (n : ℕ) (hn : 1 ≤ n) {ρ H : ℝ} (hρ : 0 < ρ) (hρH : ρ ≤ H) :
    ((RelativeCup.cx (avoidancePair n H)).d n (n + 1)).hom (relative n hn hρ hρH) = 0 := by
  change RelativeCupCochain.differential (avoidancePair n H) n (relative n hn hρ hρH) = 0
  apply RelativeCupCochain.toAmbient_injective (avoidancePair n H) (n + 1)
  rw [RelativeCupCochain.toAmbient_differential, toAmbient, map_zero]
  exact NormalizedDiagonalCocycle.ambient_closed n hn hρ

theorem image (n : ℕ) (hn : 1 ≤ n) {ρ H : ℝ} (hρ : 0 < ρ) (hρH : ρ ≤ H) :
    (relativeToPool (avoidancePair n H) n).hom
      (CochainClass.classOf (RelativeCup.cx (avoidancePair n H)) n (relative n hn hρ hρH)
        (closed n hn hρ hρH)) = ambientClass n hn := by
  have he := RelativeCup.relativeToPool_classOf (avoidancePair n H) n (relative n hn hρ hρH) (closed n hn hρ hρH)
  exact he.trans ((CochainClass.classOf_congr _ n (toAmbient n hn hρ hρH) _ _).trans
    (NormalizedDiagonalCocycle.ambient_class n hn hρ))

variable (n : ℕ) (hn : 2 ≤ n) {ρ₀ ρ₁ H : ℝ}
  (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁) (h₀H : ρ₀ ≤ H) (h₁H : ρ₁ ≤ H) (hH : 0 < H) (hH2 : H ≤ 2)

include hH hH2 in
theorem classes_equal :
    CochainClass.classOf (RelativeCup.cx (avoidancePair n H)) n (relative n (by omega) h₀ h₀H) (closed n (by omega) h₀ h₀H) =
    CochainClass.classOf (RelativeCup.cx (avoidancePair n H)) n (relative n (by omega) h₁ h₁H) (closed n (by omega) h₁ h₁H) := by
  apply AvoidanceUniqueness.relativeToPool_injective n hn hH hH2
  exact (image n (by omega) h₀ h₀H).trans (image n (by omega) h₁ h₁H).symm

def relativePrimitive : RelativeCupCochain.relative (avoidancePair n H) (n - 1) :=
  CochainClassExact.primitive (RelativeCup.cx (avoidancePair n H)) n (by omega)
    (relative n (by omega) h₀ h₀H) (relative n (by omega) h₁ h₁H)
    (closed n (by omega) h₀ h₀H) (closed n (by omega) h₁ h₁H)
    (classes_equal n hn h₀ h₁ h₀H h₁H hH hH2)

theorem relativePrimitive_boundary :
    ((RelativeCup.cx (avoidancePair n H)).d (n - 1) n).hom (relativePrimitive n hn h₀ h₁ h₀H h₁H hH hH2) =
      relative n (by omega) h₀ h₀H - relative n (by omega) h₁ h₁H :=
  CochainClassExact.primitive_d (RelativeCup.cx (avoidancePair n H)) n (by omega)
    (relative n (by omega) h₀ h₀H) (relative n (by omega) h₁ h₁H)
    (closed n (by omega) h₀ h₀H) (closed n (by omega) h₁ h₁H)
    (classes_equal n hn h₀ h₁ h₀H h₁H hH hH2)

def primitive : singularCochainGroup (ZMod 2) (product n) (n - 1) :=
  RelativeCupCochain.toAmbient (avoidancePair n H) (n - 1) (relativePrimitive n hn h₀ h₁ h₀H h₁H hH hH2)

theorem primitive_supported : cochainPullback (inclusion n H) (n - 1) (primitive n hn h₀ h₁ h₀H h₁H hH hH2) = 0 :=
  RelativeCupCochain.restriction_toAmbient (avoidancePair n H) (n - 1) (relativePrimitive n hn h₀ h₁ h₀H h₁H hH hH2)

theorem primitive_boundary :
    ((cochainCxZMod2 (product n)).d (n - 1) n).hom (primitive n hn h₀ h₁ h₀H h₁H hH hH2) =
      NormalizedDiagonalCocycle.ambient n (by omega) h₀ - NormalizedDiagonalCocycle.ambient n (by omega) h₁ := by
  have he := ConcreteCategory.congr_hom ((RelativeCup.ambientMap (avoidancePair n H)).comm (n - 1) n)
    (relativePrimitive n hn h₀ h₁ h₀H h₁H hH hH2)
  change ((cochainCxZMod2 (product n)).d (n - 1) n).hom (primitive n hn h₀ h₁ h₀H h₁H hH hH2) =
    RelativeCupCochain.toAmbient (avoidancePair n H) n
      (((RelativeCup.cx (avoidancePair n H)).d (n - 1) n).hom (relativePrimitive n hn h₀ h₁ h₀H h₁H hH hH2)) at he
  rw [he, relativePrimitive_boundary, map_sub, toAmbient, toAmbient]

theorem primitive_pullback_zero {X : TopCat.{0}} (f : X ⟶ product n) (hf : ∀ x, f x ∈ avoid n H) :
    cochainPullback f (n - 1) (primitive n hn h₀ h₁ h₀H h₁H hH hH2) = 0 := by
  let g : X ⟶ TopCat.of (avoid n H) := TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : g ≫ inclusion n H = f := rfl
  rw [← he, pullback_comp, primitive_supported]
  exact map_zero _

end
end Finsler.NormalizedRadiusRelativeComparison
