module

public import Finsler.Geometry.FixedCoefficientModel

/-! Fixed signed-coordinate, energy, flow and index comparison. -/

@[expose] public section

namespace Finsler.FixedProductRegion

open Set Finsler.FixedCoefficientModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {B : Type*} [TopologicalSpace B] {b p : ℕ}
variable (P : B → Prop) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)

def embed (u : {x : B // P x} × eucFixed d₁ × eucFixed d₂) :
    B × EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin p) :=
  (u.1.1, u.2.1.1, u.2.2.1)

theorem continuous_embed : Continuous (embed P d₁ d₂) :=
  (continuous_subtype_val.comp continuous_fst).prodMk
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))

variable (U : Set (B × EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin p)))

def fixedRegionHomeo :
    {w : U // P w.1.1 ∧ w.1.2.1 ∈ eucFixed d₁ ∧ w.1.2.2 ∈ eucFixed d₂} ≃ₜ
      {u : {x : B // P x} × eucFixed d₁ × eucFixed d₂ // embed P d₁ d₂ u ∈ U} where
  toFun w := ⟨(⟨w.1.1.1, w.2.1⟩, ⟨w.1.1.2.1, w.2.2.1⟩, ⟨w.1.1.2.2, w.2.2.2⟩), w.1.2⟩
  invFun u := ⟨⟨embed P d₁ d₂ u.1, u.2⟩, u.1.1.2, u.1.2.1.2, u.1.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hc : Continuous fun w :
        {w : U // P w.1.1 ∧ w.1.2.1 ∈ eucFixed d₁ ∧ w.1.2.2 ∈ eucFixed d₂} => w.1.1 :=
      continuous_subtype_val.comp continuous_subtype_val
    exact ((continuous_fst.comp hc).subtype_mk _).prodMk
      (((continuous_fst.comp (continuous_snd.comp hc)).subtype_mk _).prodMk
        ((continuous_snd.comp (continuous_snd.comp hc)).subtype_mk _))
  continuous_invFun :=
    (((continuous_embed P d₁ d₂).comp continuous_subtype_val).subtype_mk _).subtype_mk _

def standardRegion : Set
    ({x : B // P x} × EuclideanSpace ℝ (Fin (Fintype.card {i : Fin b // d₁ i = 1})) ×
      EuclideanSpace ℝ (Fin (Fintype.card {i : Fin p // d₂ i = 1}))) :=
  {v | embed P d₁ d₂ ((productHomeo d₁ d₂ {x : B // P x}).symm v) ∈ U}

def standardRegionHomeo :
    {w : U // P w.1.1 ∧ w.1.2.1 ∈ eucFixed d₁ ∧ w.1.2.2 ∈ eucFixed d₂} ≃ₜ
      standardRegion P d₁ d₂ U :=
  (fixedRegionHomeo P d₁ d₂ U).trans
    ((productHomeo d₁ d₂ {x : B // P x}).subtype (fun u => by
      change embed P d₁ d₂ u ∈ U ↔
        embed P d₁ d₂ ((productHomeo d₁ d₂ {x : B // P x}).symm
          (productHomeo d₁ d₂ {x : B // P x} u)) ∈ U
      rw [Homeomorph.symm_apply_apply]))

theorem standard_base
    (w : {w : U // P w.1.1 ∧ w.1.2.1 ∈ eucFixed d₁ ∧ w.1.2.2 ∈ eucFixed d₂}) :
    (standardRegionHomeo P d₁ d₂ U w).1.1.1 = w.1.1.1 := rfl

theorem standard_energy (h : B → ℝ)
    (w : {w : U // P w.1.1 ∧ w.1.2.1 ∈ eucFixed d₁ ∧ w.1.2.2 ∈ eucFixed d₂}) :
    h (standardRegionHomeo P d₁ d₂ U w).1.1.1 -
        ‖(standardRegionHomeo P d₁ d₂ U w).1.2.1‖ ^ 2 +
        ‖(standardRegionHomeo P d₁ d₂ U w).1.2.2‖ ^ 2 =
      h w.1.1.1 - ‖w.1.1.2.1‖ ^ 2 + ‖w.1.1.2.2‖ ^ 2 :=
  product_energy d₁ d₂ (fun x : {x : B // P x} => h x.1)
    (fixedRegionHomeo P d₁ d₂ U w).1

theorem standard_inverse_embed (v : standardRegion P d₁ d₂ U) :
    ((standardRegionHomeo P d₁ d₂ U).symm v).1.1 =
      embed P d₁ d₂ ((productHomeo d₁ d₂ {x : B // P x}).symm v.1) := rfl

end

end Finsler.FixedProductRegion
