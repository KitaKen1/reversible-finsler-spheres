module

public import Finsler.Geometry.FixedProductRegion
public import Finsler.Topology.RestrictedLensPairs
public import Finsler.Topology.ProductModel

/-! The fixed part of an actual product flow is the standard product over the fixed base.
The coefficient isometries preserve energy and the expanding/contracting scalar flows.
Ordinary lens cohomology is compared through these same flow maps. -/

@[expose] public section

namespace Finsler.FixedProductFlow

open Set Finsler.FlowLens Finsler.LensFamily Finsler.LensContinuation
open Finsler.ProductModel Finsler.ConeLens Finsler.FixedCoefficientModel
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {B : TopCat.{0}} {b p : ℕ}
variable (P : Set B) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)

def fixedSet : Set (Model B b (EuclideanSpace ℝ (Fin p))) :=
  {w | w.1 ∈ P ∧ w.2.1 ∈ eucFixed d₁ ∧ w.2.2 ∈ eucFixed d₂}

def splitHomeo : fixedSet P d₁ d₂ ≃ₜ (P × eucFixed d₁ × eucFixed d₂) where
  toFun w := (⟨w.1.1, w.2.1⟩, ⟨w.1.2.1, w.2.2.1⟩, ⟨w.1.2.2, w.2.2.2⟩)
  invFun v := ⟨(v.1.1, v.2.1.1, v.2.2.1), v.1.2, v.2.1.2, v.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (((continuous_fst.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _).prodMk
        ((continuous_snd.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _))
  continuous_invFun := by
    exact ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))).subtype_mk _

abbrev standardModel : TopCat.{0} :=
  Model (TopCat.of P) (Fintype.card {i : Fin b // d₁ i = 1})
    (EuclideanSpace ℝ (Fin (Fintype.card {i : Fin p // d₂ i = 1})))

def standardHomeo : fixedSet P d₁ d₂ ≃ₜ standardModel P d₁ d₂ :=
  (splitHomeo P d₁ d₂).trans (productHomeo d₁ d₂ P)

theorem region_mem (U : Set (Model B b (EuclideanSpace ℝ (Fin p))))
    (w : fixedSet P d₁ d₂) :
    standardHomeo P d₁ d₂ w ∈ Finsler.FixedProductRegion.standardRegion (fun z : B => z ∈ P) d₁ d₂ U ↔
      w.1 ∈ U := by
  change Finsler.FixedProductRegion.embed (fun z : B => z ∈ P) d₁ d₂
    ((productHomeo d₁ d₂ P).symm ((productHomeo d₁ d₂ P) (splitHomeo P d₁ d₂ w))) ∈ U ↔ _
  rw [Homeomorph.symm_apply_apply]
  rfl

variable {h : B → ℝ} (ψ : Descent B h) (hh : Continuous h)
variable (hP : ∀ t (z : B), 0 ≤ t → z ∈ P → ψ.flow t z ∈ P)

abbrev standardDescent :=
  descent (Fintype.card {i : Fin b // d₁ i = 1})
    (EuclideanSpace ℝ (Fin (Fintype.card {i : Fin p // d₂ i = 1})))
    (Finsler.SubspaceK.subDescent ψ hP) (hh.comp continuous_subtype_val)

include hP in
theorem flow_preserves : ∀ t (w : Model B b (EuclideanSpace ℝ (Fin p))), 0 ≤ t →
    w ∈ fixedSet P d₁ d₂ → (descent b (EuclideanSpace ℝ (Fin p)) ψ hh).flow t w ∈ fixedSet P d₁ d₂ := by
  intro t w ht hw
  exact ⟨hP t w.1 ht hw.1, (eucFixed d₁).smul_mem _ hw.2.1,
    (eucFixed d₂).smul_mem _ hw.2.2⟩

theorem energy (w : fixedSet P d₁ d₂) :
    (cone (Fintype.card {i : Fin b // d₁ i = 1})
      (EuclideanSpace ℝ (Fin (Fintype.card {i : Fin p // d₂ i = 1})))
      (hh.comp continuous_subtype_val)).energy (standardHomeo P d₁ d₂ w) =
        (cone b (EuclideanSpace ℝ (Fin p)) hh).energy w.1 :=
  product_energy d₁ d₂ (fun z : P => h z) (splitHomeo P d₁ d₂ w)

theorem flow (t : ℝ) (ht : 0 ≤ t) (w : fixedSet P d₁ d₂) :
    standardHomeo P d₁ d₂
      ((Finsler.SubspaceK.subDescent (descent b (EuclideanSpace ℝ (Fin p)) ψ hh)
        (flow_preserves P d₁ d₂ ψ hh hP)).flow t w) =
      (standardDescent P d₁ d₂ ψ hh hP).flow t (standardHomeo P d₁ d₂ w) := by
  change (productHomeo d₁ d₂ P)
      ((Finsler.SubspaceK.subDescent ψ hP).flow t (splitHomeo P d₁ d₂ w).1,
        Real.exp (max t 0) • (splitHomeo P d₁ d₂ w).2.1,
        Real.exp (-(max t 0)) • (splitHomeo P d₁ d₂ w).2.2) = _
  rw [max_eq_left ht]
  exact product_flow d₁ d₂ (Finsler.SubspaceK.subDescent ψ hP).flow t (splitHomeo P d₁ d₂ w)

theorem nonempty_lens_equiv (U : Set (Model B b (EuclideanSpace ℝ (Fin p))))
    (a c T : ℝ) (hT : 0 ≤ T) (q : ℕ) :
    Nonempty (
      H (triv (pairOf (X := Model B b (EuclideanSpace ℝ (Fin p)))
        (inter_subset_inter_left (fixedSet P d₁ d₂)
          (partY_sub_partU (cone b (EuclideanSpace ℝ (Fin p)) hh).energy
            (descent b (EuclideanSpace ℝ (Fin p)) ψ hh) U a c T)))) q ≃ₗ[ZMod 2]
      lensH (standardDescent P d₁ d₂ ψ hh hP)
        (Finsler.FixedProductRegion.standardRegion (fun z : B => z ∈ P) d₁ d₂ U) a c T q) := by
  let D := Finsler.SubspaceK.subDescent (descent b (EuclideanSpace ℝ (Fin p)) ψ hh)
    (flow_preserves P d₁ d₂ ψ hh hP)
  let E := standardDescent P d₁ d₂ ψ hh hP
  let ξ := standardHomeo P d₁ d₂
  let g₁ := fun w : TopCat.of (fixedSet P d₁ d₂) =>
    (cone b (EuclideanSpace ℝ (Fin p)) hh).energy w.1
  let g₂ : standardModel P d₁ d₂ → ℝ := (cone (Fintype.card {i : Fin b // d₁ i = 1})
    (EuclideanSpace ℝ (Fin (Fintype.card {i : Fin p // d₂ i = 1})))
    (hh.comp continuous_subtype_val)).energy
  let U₂ := Finsler.FixedProductRegion.standardRegion (fun z : B => z ∈ P) d₁ d₂ U
  have he (w : fixedSet P d₁ d₂) : g₂ (ξ w) = g₁ w := energy P d₁ d₂ hh w
  have ht : ∀ w : fixedSet P d₁ d₂,
      w ∈ partU g₁ (Subtype.val ⁻¹' U) c ↔ ξ w ∈ partU g₂ U₂ c := by
    intro w
    change (g₁ w < c ∧ w.1 ∈ U) ↔ (g₂ (ξ w) < c ∧ ξ w ∈ U₂)
    rw [he w, region_mem P d₁ d₂ U w]
  have hs : ∀ w : fixedSet P d₁ d₂,
      w ∈ partY g₁ D (Subtype.val ⁻¹' U) a c T ↔ ξ w ∈ partY g₂ E U₂ a c T := by
    intro w
    change (g₁ w < c ∧ g₁ (D.flow T w) < a ∧ w.1 ∈ U) ↔
      (g₂ (ξ w) < c ∧ g₂ (E.flow T (ξ w)) < a ∧ ξ w ∈ U₂)
    have hf : ξ (D.flow T w) = E.flow T (ξ w) := flow P d₁ d₂ ψ hh hP T hT w
    rw [← hf, he w, he (D.flow T w), region_mem P d₁ d₂ U w]
  have hbij := bijective_Hmap_of_homeomorph
    (partY_sub_partU g₁ D (Subtype.val ⁻¹' U) a c T)
    (partY_sub_partU g₂ E U₂ a c T) ξ ht hs q
  exact ⟨(Finsler.RestrictedLensPairs.lensHEquiv
    (descent b (EuclideanSpace ℝ (Fin p)) ψ hh) (flow_preserves P d₁ d₂ ψ hh hP)
    U a c T hT q).symm.trans (LinearEquiv.ofBijective _ hbij).symm⟩

end

end Finsler.FixedProductFlow
