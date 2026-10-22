module

public import Finsler.Analysis.InvolutionConjugacy
public import Finsler.Analysis.LabelFamilyAverage

/-! Construct a compatible family by pairing each positive label with its reversal.
The negative sets, functions and fields are transported rather than chosen independently. -/

@[expose] public section

namespace Finsler.ReversalFamily

open Set Finsler.InvolutionConjugacy Finsler.EquivariantField
open scoped ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

def flip : (ι × Bool) ≃ (ι × Bool) where
  toFun i := (i.1, !i.2)
  invFun i := (i.1, !i.2)
  left_inv i := by cases i with | mk i o => cases o <;> rfl
  right_inv i := by cases i with | mk i o => cases o <;> rfl

def setFamily (r : E →L[ℝ] E) (U : ι → Set E) (i : ι × Bool) : Set E :=
  cond i.2 (U i.1) (r ⁻¹' U i.1)

def funFamily (r : E →L[ℝ] E) (β : ι → E → ℝ) (i : ι × Bool) : E → ℝ :=
  cond i.2 (β i.1) (conjFun r (β i.1))

def fieldFamily (r : E →L[ℝ] E) (W : ι → E → E) (i : ι × Bool) : E → E :=
  cond i.2 (W i.1) (conjField r (W i.1))

variable (r h : E →L[ℝ] E) (hr : ∀ x, r (r x) = x)
  (hrh : ∀ x, r (h x) = h (r x))

include hr

theorem set_rev_iff (U : ι → Set E) (i : ι × Bool) (x : E) :
    r x ∈ setFamily r U (flip i) ↔ x ∈ setFamily r U i := by
  rcases i with ⟨i, o⟩
  cases o <;> simp [setFamily, flip, hr]

theorem fun_rev (β : ι → E → ℝ) (i : ι × Bool) (x : E) :
    funFamily r β i (r x) = funFamily r β (flip i) x := by
  rcases i with ⟨i, o⟩
  cases o <;> simp [funFamily, flip, conjFun, hr]

theorem field_rev (W : ι → E → E) (i : ι × Bool) (x : E) :
    fieldFamily r W (flip i) (r x) = r (fieldFamily r W i x) := by
  rcases i with ⟨i, o⟩
  cases o <;> simp [fieldFamily, flip, conjField, hr]

theorem set_isCompact {T : ι → Set E} (hT : ∀ i, IsCompact (T i)) (i : ι × Bool) :
    IsCompact (setFamily r T i) := by
  rcases i with ⟨i, o⟩
  cases o
  · exact (invHomeo r hr).isCompact_preimage.mpr (hT i)
  · exact hT i

theorem tsupport_subset {β : ι → E → ℝ} {T : ι → Set E}
    (hβ : ∀ i, tsupport (β i) ⊆ T i) (i : ι × Bool) :
    tsupport (funFamily r β i) ⊆ setFamily r T i := by
  rcases i with ⟨i, o⟩
  cases o
  · change tsupport (conjFun r (β i)) ⊆ r ⁻¹' T i
    rw [tsupport_conjFun r hr]
    exact preimage_mono (hβ i)
  · exact hβ i

theorem sets_subset_invariant {U : ι → Set E} {O : Set E}
    (hU : ∀ i, U i ⊆ O) (hOr : ∀ x ∈ O, r x ∈ O) (i : ι × Bool) :
    setFamily r U i ⊆ O := by
  rcases i with ⟨i, o⟩
  cases o
  · intro x hx
    have hO := hOr (r x) (hU i hx)
    rwa [hr] at hO
  · exact hU i

omit hr in
theorem set_isOpen {U : ι → Set E} (hU : ∀ i, IsOpen (U i)) (i : ι × Bool) :
    IsOpen (setFamily r U i) := by
  rcases i with ⟨i, o⟩
  cases o
  · exact (hU i).preimage r.continuous
  · exact hU i

omit hr in
theorem sets_subset {T U : ι → Set E} (hTU : ∀ i, T i ⊆ U i) (i : ι × Bool) :
    setFamily r T i ⊆ setFamily r U i := by
  rcases i with ⟨i, o⟩
  cases o
  · exact preimage_mono (hTU i)
  · exact hTU i

omit hr in
theorem field_contDiffOn {W : ι → E → E} {U : ι → Set E}
    (hW : ∀ i, ContDiffOn ℝ ∞ (W i) (U i)) (i : ι × Bool) :
    ContDiffOn ℝ ∞ (fieldFamily r W i) (setFamily r U i) := by
  rcases i with ⟨i, o⟩
  cases o
  · exact conjField_contDiffOn r (hW i)
  · exact hW i

omit hr in
theorem fun_differentiable {β : ι → E → ℝ} (hβ : ∀ i x, DifferentiableAt ℝ (β i) x)
    (i : ι × Bool) (x : E) : DifferentiableAt ℝ (funFamily r β i) x := by
  rcases i with ⟨i, o⟩
  cases o
  · exact (hβ i (r x)).comp x r.differentiableAt
  · exact hβ i x

include hrh

omit hr in
theorem set_half_iff {U : ι → Set E} (hU : ∀ i x, h x ∈ U i ↔ x ∈ U i)
    (i : ι × Bool) (x : E) : h x ∈ setFamily r U i ↔ x ∈ setFamily r U i := by
  rcases i with ⟨i, o⟩
  cases o
  · exact preimage_invariant r h hrh (hU i) x
  · exact hU i x

omit hr in
theorem fun_half {β : ι → E → ℝ} (hβ : ∀ i x, β i (h x) = β i x)
    (i : ι × Bool) (x : E) : funFamily r β i (h x) = funFamily r β i x := by
  rcases i with ⟨i, o⟩
  cases o
  · exact conjFun_equivariant r h hrh (hβ i) x
  · exact hβ i x

omit hr in
theorem field_half {W : ι → E → E} {U : ι → Set E}
    (hW : ∀ i x, x ∈ U i → W i (h x) = h (W i x))
    (i : ι × Bool) {x : E} (hx : x ∈ setFamily r U i) :
    fieldFamily r W i (h x) = h (fieldFamily r W i x) := by
  rcases i with ⟨i, o⟩
  cases o
  · exact conjField_equivariant r h hrh (hW i) hx
  · exact hW i x hx

omit hr hrh in
theorem sets_disjoint {U : ι → Set E}
    (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUr : ∀ i j, Disjoint (U i) (r ⁻¹' U j))
    (i j : ι × Bool) (hij : i ≠ j) : Disjoint (setFamily r U i) (setFamily r U j) := by
  rcases i with ⟨i, oi⟩
  rcases j with ⟨j, oj⟩
  cases oi <;> cases oj
  · exact (hU i j (fun he => hij (by cases he; rfl))).preimage r
  · exact (hUr j i).symm
  · exact hUr i j
  · exact hU i j (fun he => hij (by cases he; rfl))

omit hrh in
theorem sum_fun_rev [Fintype ι] (β : ι → E → ℝ) (x : E) :
    (∑ i : ι × Bool, funFamily r β i (r x)) = ∑ i : ι × Bool, funFamily r β i x := by
  simp only [fun_rev r hr]
  exact Equiv.sum_comp flip (fun i => funFamily r β i x)

omit hr in
theorem sum_fun_half [Fintype ι] {β : ι → E → ℝ} (hβ : ∀ i x, β i (h x) = β i x)
    (x : E) : (∑ i : ι × Bool, funFamily r β i (h x)) = ∑ i : ι × Bool, funFamily r β i x := by
  simp only [fun_half r h hrh hβ]

end

end Finsler.ReversalFamily
