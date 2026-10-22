module

public import Finsler.Analysis.EquivariantField

/-! transport local functions and fields by a linear involution.
 -/

@[expose] public section

namespace Finsler.InvolutionConjugacy

open Set Topology Finsler.EquivariantField
open scoped ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (r : E →L[ℝ] E) (hr : ∀ x, r (r x) = x)

def conjFun (f : E → ℝ) (x : E) : ℝ := f (r x)
def conjField (V : E → E) (x : E) : E := r (V (r x))

include hr

theorem conjFun_twice (f : E → ℝ) : conjFun r (conjFun r f) = f :=
  funext fun x => congrArg f (hr x)

theorem conjField_twice (V : E → E) : conjField r (conjField r V) = V := by
  funext x
  simp only [conjField, hr]

theorem conj_derivative {f : E → ℝ} {x : E} (hd : DifferentiableAt ℝ f (r x))
    (V : E → E) :
    fderiv ℝ (conjFun r f) x (conjField r V x) = fderiv ℝ f (r x) (V (r x)) := by
  have h := hd.hasFDerivAt.comp x r.hasFDerivAt
  change fderiv ℝ (f ∘ r) x (r (V (r x))) = _
  rw [h.fderiv]
  change fderiv ℝ f (r x) (r (r (V (r x)))) = _
  rw [hr]

theorem tsupport_conjFun (f : E → ℝ) : tsupport (conjFun r f) = r ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f (invHomeo r hr)

theorem conjFun_hasCompactSupport {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (conjFun r f) := hf.comp_homeomorph (invHomeo r hr)

theorem conjField_hasCompactSupport {V : E → E} (hV : HasCompactSupport V) :
    HasCompactSupport (conjField r V) :=
  (hV.comp_homeomorph (invHomeo r hr)).comp_left (map_zero r)

omit hr in
theorem conjField_contDiff {V : E → E} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (conjField r V) := r.contDiff.comp (hV.comp r.contDiff)

omit hr in
theorem conjField_contDiffOn {V : E → E} {U : Set E} (hV : ContDiffOn ℝ ∞ V U) :
    ContDiffOn ℝ ∞ (conjField r V) (r ⁻¹' U) :=
  r.contDiff.comp_contDiffOn (hV.comp r.contDiff.contDiffOn (fun _ hx => hx))

omit hr in
theorem conjField_matches {V W : E → E} {T : Set E} (hVW : ∀ x ∈ T, V x = W x)
    {x : E} (hx : x ∈ r ⁻¹' T) : conjField r V x = conjField r W x :=
  congrArg r (hVW _ hx)

variable (h : E →L[ℝ] E) (hrh : ∀ x, r (h x) = h (r x))

include hrh

omit hr in
theorem preimage_invariant {U : Set E} (hU : ∀ x, h x ∈ U ↔ x ∈ U) (x : E) :
    h x ∈ r ⁻¹' U ↔ x ∈ r ⁻¹' U := by
  change r (h x) ∈ U ↔ r x ∈ U
  rw [hrh, hU]

omit hr in
theorem conjFun_equivariant {f : E → ℝ} (hf : ∀ x, f (h x) = f x) (x : E) :
    conjFun r f (h x) = conjFun r f x := by
  unfold conjFun
  rw [hrh, hf]

omit hr in
theorem conjField_equivariant {V : E → E} {U : Set E}
    (hV : ∀ x ∈ U, V (h x) = h (V x)) {x : E} (hx : x ∈ r ⁻¹' U) :
    conjField r V (h x) = h (conjField r V x) := by
  unfold conjField
  rw [hrh, hV _ hx, hrh]

end

end Finsler.InvolutionConjugacy
