module

public import Finsler.Topology.AnnularThomCocycle
public import Finsler.Topology.AvoidanceUniqueness

/-! The annular representative and the existing normalized Thom cochain
agree in the actual relative group for far union diagonal. The comparison
primitive therefore vanishes on both the far set and the diagonal, which
kills its actual self-cut time endpoints. No equality of absolute images
is used without the proved relative injectivity. -/

@[expose] public section
namespace Finsler.AnnularThomComparison

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelEvaluation
open Finsler.DiagonalCohomology Finsler.DiagonalAvoidanceCocycle
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem annular_avoidance_zero (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (inclusion n ρ) n (AnnularThomCocycle.ambient n hn h) = 0 := by
  apply AnnularThomCocycle.pullback_zero_of_range n hn h
  intro z
  obtain ⟨i, hi⟩ := mem_iUnion.mp z.property
  cases i with
  | false => exact mem_iUnion.mpr ⟨false, hi⟩
  | true =>
    refine mem_iUnion.mpr ⟨true, ?_⟩
    have he : z.val.1 = z.val.2 := hi
    change ‖(z.val.2 : Ambient n) - z.val.1‖ ≤ δ
    rw [he, sub_self, norm_zero]
    exact h.1.le

def oldRelative (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.relative (avoidancePair n ρ) n :=
  (RelativeCupCochain.exists_lift (avoidancePair n ρ) n (NormalizedDiagonalCocycle.ambient n hn hρ)
    (NormalizedDiagonalCocycle.avoidance_supported n hn hρ)).choose

def newRelative (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    RelativeCupCochain.relative (avoidancePair n ρ) n :=
  (RelativeCupCochain.exists_lift (avoidancePair n ρ) n (AnnularThomCocycle.ambient n hn h)
    (annular_avoidance_zero n hn h)).choose

theorem old_toAmbient (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.toAmbient (avoidancePair n ρ) n (oldRelative n hn hρ) =
      NormalizedDiagonalCocycle.ambient n hn hρ :=
  (RelativeCupCochain.exists_lift (avoidancePair n ρ) n (NormalizedDiagonalCocycle.ambient n hn hρ)
    (NormalizedDiagonalCocycle.avoidance_supported n hn hρ)).choose_spec

theorem new_toAmbient (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    RelativeCupCochain.toAmbient (avoidancePair n ρ) n (newRelative n hn h) =
      AnnularThomCocycle.ambient n hn h :=
  (RelativeCupCochain.exists_lift (avoidancePair n ρ) n (AnnularThomCocycle.ambient n hn h)
    (annular_avoidance_zero n hn h)).choose_spec

theorem old_closed (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    ((RelativeCup.cx (avoidancePair n ρ)).d n (n + 1)).hom (oldRelative n hn hρ) = 0 := by
  change RelativeCupCochain.differential (avoidancePair n ρ) n (oldRelative n hn hρ) = 0
  apply RelativeCupCochain.toAmbient_injective (avoidancePair n ρ) (n + 1)
  rw [RelativeCupCochain.toAmbient_differential, old_toAmbient, map_zero]
  exact NormalizedDiagonalCocycle.ambient_closed n hn hρ

theorem new_closed (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    ((RelativeCup.cx (avoidancePair n ρ)).d n (n + 1)).hom (newRelative n hn h) = 0 := by
  change RelativeCupCochain.differential (avoidancePair n ρ) n (newRelative n hn h) = 0
  apply RelativeCupCochain.toAmbient_injective (avoidancePair n ρ) (n + 1)
  rw [RelativeCupCochain.toAmbient_differential, new_toAmbient, map_zero]
  exact AnnularThomCocycle.ambient_closed n hn h

private theorem old_image (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (relativeToPool (avoidancePair n ρ) n).hom
      (CochainClass.classOf (RelativeCup.cx (avoidancePair n ρ)) n (oldRelative n hn hρ)
        (old_closed n hn hρ)) = ambientClass n hn := by
  have he := RelativeCup.relativeToPool_classOf (avoidancePair n ρ) n (oldRelative n hn hρ) (old_closed n hn hρ)
  exact he.trans ((CochainClass.classOf_congr _ n (old_toAmbient n hn hρ) _ _).trans
    (NormalizedDiagonalCocycle.ambient_class n hn hρ))

private theorem new_image (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    (relativeToPool (avoidancePair n ρ) n).hom
      (CochainClass.classOf (RelativeCup.cx (avoidancePair n ρ)) n (newRelative n hn h)
        (new_closed n hn h)) = ambientClass n hn := by
  have he := RelativeCup.relativeToPool_classOf (avoidancePair n ρ) n (newRelative n hn h) (new_closed n hn h)
  exact he.trans ((CochainClass.classOf_congr _ n (new_toAmbient n hn h) _ _).trans
    (AnnularThomCocycle.ambient_class n hn h))

theorem classes_equal (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2) :
    CochainClass.classOf (RelativeCup.cx (avoidancePair n ρ)) n (newRelative n (by omega) h)
      (new_closed n (by omega) h) =
    CochainClass.classOf (RelativeCup.cx (avoidancePair n ρ)) n (oldRelative n (by omega) (h.1.trans h.2.2))
      (old_closed n (by omega) (h.1.trans h.2.2)) := by
  apply AvoidanceUniqueness.relativeToPool_injective n hn (h.1.trans h.2.2) hρ2
  exact (new_image n (by omega) h).trans (old_image n (by omega) (h.1.trans h.2.2)).symm

def relativePrimitive (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2) :
    RelativeCupCochain.relative (avoidancePair n ρ) (n - 1) :=
  CochainClassExact.primitive (RelativeCup.cx (avoidancePair n ρ)) n (by omega)
    (newRelative n (by omega) h) (oldRelative n (by omega) (h.1.trans h.2.2))
    (new_closed n (by omega) h) (old_closed n (by omega) (h.1.trans h.2.2)) (classes_equal n hn h hρ2)

theorem relativePrimitive_boundary (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2) :
    ((RelativeCup.cx (avoidancePair n ρ)).d (n - 1) n).hom (relativePrimitive n hn h hρ2) =
      newRelative n (by omega) h - oldRelative n (by omega) (h.1.trans h.2.2) :=
  CochainClassExact.primitive_d (RelativeCup.cx (avoidancePair n ρ)) n (by omega)
    (newRelative n (by omega) h) (oldRelative n (by omega) (h.1.trans h.2.2))
    (new_closed n (by omega) h) (old_closed n (by omega) (h.1.trans h.2.2)) (classes_equal n hn h hρ2)

def ambientPrimitive (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2) :
    singularCochainGroup (ZMod 2) (product n) (n - 1) :=
  RelativeCupCochain.toAmbient (avoidancePair n ρ) (n - 1) (relativePrimitive n hn h hρ2)

theorem ambientPrimitive_supported (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2) :
    cochainPullback (inclusion n ρ) (n - 1) (ambientPrimitive n hn h hρ2) = 0 :=
  RelativeCupCochain.restriction_toAmbient (avoidancePair n ρ) (n - 1) (relativePrimitive n hn h hρ2)

theorem ambientPrimitive_boundary (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2) :
    ((cochainCxZMod2 (product n)).d (n - 1) n).hom (ambientPrimitive n hn h hρ2) =
      AnnularThomCocycle.ambient n (by omega) h - NormalizedDiagonalCocycle.ambient n (by omega) (h.1.trans h.2.2) := by
  have he := ConcreteCategory.congr_hom ((RelativeCup.ambientMap (avoidancePair n ρ)).comm (n - 1) n)
    (relativePrimitive n hn h hρ2)
  change ((cochainCxZMod2 (product n)).d (n - 1) n).hom (ambientPrimitive n hn h hρ2) =
    RelativeCupCochain.toAmbient (avoidancePair n ρ) n
      (((RelativeCup.cx (avoidancePair n ρ)).d (n - 1) n).hom (relativePrimitive n hn h hρ2)) at he
  rw [he, relativePrimitive_boundary, map_sub, new_toAmbient, old_toAmbient]

end
end Finsler.AnnularThomComparison
