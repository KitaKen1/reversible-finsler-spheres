module

public import Finsler.Geometry.FixedFrameCoordinates
public import Finsler.Geometry.LabelDeform

/-! Euclidean models of the fixed signed coefficient spaces. An orthonormal basis gives
an isometry to the standard Euclidean space of dimension equal to the number of +1 signs.
The product energy and its expanding/contracting scalar flow are preserved. -/

@[expose] public section

namespace Finsler.FixedCoefficientModel

open Finsler.FixedFrameCoordinates Finsler.RotationNatural

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 5

def eucFixed {b : ℕ} (d : Fin b → ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin b)) :=
  (fixedCoeff d).comap (WithLp.linearEquiv 2 ℝ (Fin b → ℝ)).toLinearMap

theorem mem_eucFixed {b : ℕ} (d : Fin b → ℝ) (u : EuclideanSpace ℝ (Fin b)) :
    u ∈ eucFixed d ↔ diagonal d (WithLp.ofLp u) = WithLp.ofLp u := Iff.rfl

def eucFixedEquiv {b : ℕ} (d : Fin b → ℝ) : eucFixed d ≃ₗ[ℝ] fixedCoeff d where
  toFun u := ⟨WithLp.ofLp u.1, u.2⟩
  invFun x := ⟨WithLp.toLp 2 x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_eucFixed {b : ℕ} (d : Fin b → ℝ) :
    Module.finrank ℝ (eucFixed d) = Fintype.card {i : Fin b // d i = 1} := by
  classical
  rw [(eucFixedEquiv d).finrank_eq, finrank_fixedCoeff]

def modelEquiv {b : ℕ} (d : Fin b → ℝ) :
    eucFixed d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card {i : Fin b // d i = 1})) :=
  (stdOrthonormalBasis ℝ (eucFixed d)).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (finrank_eucFixed d)))

def productHomeo {b p : ℕ} (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (B : Type*) [TopologicalSpace B] :
    (B × eucFixed d₁ × eucFixed d₂) ≃ₜ
      (B × EuclideanSpace ℝ (Fin (Fintype.card {i : Fin b // d₁ i = 1})) ×
        EuclideanSpace ℝ (Fin (Fintype.card {i : Fin p // d₂ i = 1}))) :=
  (Homeomorph.refl B).prodCongr
    ((modelEquiv d₁).toHomeomorph.prodCongr (modelEquiv d₂).toHomeomorph)

theorem product_energy {b p : ℕ} (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    {B : Type*} [TopologicalSpace B] (h : B → ℝ) (w : B × eucFixed d₁ × eucFixed d₂) :
    h (productHomeo d₁ d₂ B w).1 - ‖(productHomeo d₁ d₂ B w).2.1‖ ^ 2 +
        ‖(productHomeo d₁ d₂ B w).2.2‖ ^ 2 =
      h w.1 - ‖(w.2.1 : EuclideanSpace ℝ (Fin b))‖ ^ 2 +
        ‖(w.2.2 : EuclideanSpace ℝ (Fin p))‖ ^ 2 := by
  change h w.1 - ‖modelEquiv d₁ w.2.1‖ ^ 2 + ‖modelEquiv d₂ w.2.2‖ ^ 2 = _
  rw [(modelEquiv d₁).norm_map, (modelEquiv d₂).norm_map]
  rfl

theorem product_flow {b p : ℕ} (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    {B : Type*} [TopologicalSpace B] (ψ : ℝ → B → B) (t : ℝ)
    (w : B × eucFixed d₁ × eucFixed d₂) :
    productHomeo d₁ d₂ B (ψ t w.1, Real.exp t • w.2.1, Real.exp (-t) • w.2.2) =
      (ψ t (productHomeo d₁ d₂ B w).1,
        Real.exp t • (productHomeo d₁ d₂ B w).2.1,
        Real.exp (-t) • (productHomeo d₁ d₂ B w).2.2) := by
  exact Prod.ext rfl (Prod.ext ((modelEquiv d₁).map_smul _ _) ((modelEquiv d₂).map_smul _ _))

end

end Finsler.FixedCoefficientModel
