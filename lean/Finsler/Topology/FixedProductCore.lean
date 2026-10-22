module

public import Finsler.Topology.FixedProductFlow
public import Finsler.Topology.ModelTrap
public import Finsler.Topology.LensCore

/-! Small-fibre bounds and core comparison pass through the fixed coefficient isometries.
The bounded fixed label and all fibres over its fixed base have the same lens cohomology. -/

@[expose] public section

namespace Finsler.FixedProductCore

open Set Finsler.FlowLens Finsler.LensFamily Finsler.ProductModel Finsler.ConeLens
open Finsler.FixedCoefficientModel Finsler.FixedProductFlow
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {B : TopCat.{0}} {b p : ℕ}
variable (P : Set B) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
variable {U : Set (Model B b (EuclideanSpace ℝ (Fin p)))} {W : Set B} {ρ : ℝ}

theorem standard_small
    (hS : ∀ w : Model B b (EuclideanSpace ℝ (Fin p)), w.1 ∈ W → ‖w.2.1‖ < ρ →
      ‖w.2.2‖ < ρ → w ∈ U)
    (v : standardModel P d₁ d₂) (hv : v.1.1 ∈ W) (hu : ‖v.2.1‖ < ρ) (hy : ‖v.2.2‖ < ρ) :
    v ∈ Finsler.FixedProductRegion.standardRegion (fun z : B => z ∈ P) d₁ d₂ U := by
  apply hS _ hv
  · change ‖((FixedCoefficientModel.modelEquiv d₁).symm v.2.1 : EuclideanSpace ℝ (Fin b))‖ < ρ
    exact ((FixedCoefficientModel.modelEquiv d₁).symm.norm_map _).trans_lt hu
  · change ‖((FixedCoefficientModel.modelEquiv d₂).symm v.2.2 : EuclideanSpace ℝ (Fin p))‖ < ρ
    exact ((FixedCoefficientModel.modelEquiv d₂).symm.norm_map _).trans_lt hy

theorem standard_bounds
    (hS' : ∀ w ∈ U, w.1 ∈ W ∧ ‖w.2.2‖ < ρ)
    (v : standardModel P d₁ d₂)
    (hv : v ∈ Finsler.FixedProductRegion.standardRegion (fun z : B => z ∈ P) d₁ d₂ U) :
    v.1.1 ∈ W ∧ ‖v.2.2‖ < ρ := by
  obtain ⟨hb, hy⟩ := hS' _ hv
  refine ⟨hb, ?_⟩
  change ‖((FixedCoefficientModel.modelEquiv d₂).symm v.2.2 : EuclideanSpace ℝ (Fin p))‖ < ρ at hy
  exact ((FixedCoefficientModel.modelEquiv d₂).symm.norm_map _).symm.trans_lt hy

theorem nonempty_core_equiv {h : B → ℝ} (ψ : Descent B h) (hh : Continuous h)
    (hP : ∀ t (z : B), 0 ≤ t → z ∈ P → ψ.flow t z ∈ P)
    (hS : ∀ w : Model B b (EuclideanSpace ℝ (Fin p)), w.1 ∈ W → ‖w.2.1‖ < ρ →
      ‖w.2.2‖ < ρ → w ∈ U) (hS' : ∀ w ∈ U, w.1 ∈ W ∧ ‖w.2.2‖ < ρ)
    (hρ : 0 < ρ) {a' a c T : ℝ} (ha : a' < a) (hT : 1 ≤ T) (hw : 2 * (c - a') < ρ ^ 2)
    (q : ℕ) :
    Nonempty (
      lensH (standardDescent P d₁ d₂ ψ hh hP)
        (Finsler.FixedProductRegion.standardRegion (fun z : B => z ∈ P) d₁ d₂ U) a c T q ≃ₗ[ZMod 2]
      lensH (standardDescent P d₁ d₂ ψ hh hP)
        (over (Fintype.card {i : Fin b // d₁ i = 1})
          (EuclideanSpace ℝ (Fin (Fintype.card {i : Fin p // d₂ i = 1})))
          (Subtype.val ⁻¹' W)) a c T q) := by
  let k := Fintype.card {i : Fin b // d₁ i = 1}
  let V := EuclideanSpace ℝ (Fin (Fintype.card {i : Fin p // d₂ i = 1}))
  let hhP : Continuous (fun z : TopCat.of P => h z) := hh.comp continuous_subtype_val
  apply Finsler.LensCore.nonempty_core_equiv (standardDescent P d₁ d₂ ψ hh hP)
    (energy_continuous (cone k V hhP)) ha
  intro v hv hv'
  exact Finsler.ModelTrap.core_iff k V (Finsler.SubspaceK.subDescent ψ hP) hhP
    (fun w hw hu hy => standard_small P d₁ d₂ hS w hw hu hy)
    (fun w hw => (standard_bounds P d₁ d₂ hS' w hw).1) hρ hT hw v hv hv'

end

end Finsler.FixedProductCore
