module

public import TauCeti.Analysis.Distribution.DuBoisReymond
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic

/-! An interval function with zero weak derivative is almost everywhere constant.
The mean-zero test-function construction follows Tau Ceti's du Bois--Reymond
proof, but local integrability replaces continuity and the conclusion is a.e.
This does not assume a continuous representative of the existing H¹ graph. -/

@[expose] public section

namespace Finsler.IntervalWeakConstant

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology ContDiff

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_ae_const_of_test_derivatives {a b : ℝ} {f : ℝ → F}
    (hf : LocallyIntegrableOn f (Ioo a b) volume)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo a b →
      ∫ x, deriv ψ x • f x = 0) :
    ∃ c : F, f =ᵐ[volume.restrict (Ioo a b)] fun _ => c := by
  rcases le_or_gt b a with hba | hab
  · refine ⟨0, ?_⟩
    simp [Ioo_eq_empty (not_lt.mpr hba), Filter.EventuallyEq]
  have hint : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioo a b →
      Integrable fun x => g x • f x := by
    intro g hg hgc hgs
    exact TauCeti.integrable_smul_of_locallyIntegrableOn
      (Ω := ⟨Ioo a b, isOpen_Ioo⟩) hf ⟨g, hg, hgc, hgs⟩
  let β : ContDiffBump ((a + b) / 2) := ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  have hrOut : β.rOut = (b - a) / 4 := rfl
  set ρ : ℝ → ℝ := β.normed volume with hρ_def
  have hρ : ContDiff ℝ ∞ ρ := β.contDiff_normed
  have hρc : HasCompactSupport ρ := β.hasCompactSupport_normed
  have hρs : tsupport ρ ⊆ Ioo a b := by
    rw [hρ_def, β.tsupport_normed_eq, hrOut]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hρint : ∫ x, ρ x = 1 := β.integral_normed
  refine ⟨∫ x, ρ x • f x, ?_⟩
  have key : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioo a b →
      ∫ x, g x • (f x - ∫ y, ρ y • f y) = 0 := by
    intro g hg hgc hgs
    have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
    have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
    set φ : ℝ → ℝ := fun x => g x - (∫ y, g y) * ρ x with hφ_def
    have hφ : ContDiff ℝ ∞ φ := hg.sub (contDiff_const.mul hρ)
    have hφs : tsupport φ ⊆ Ioo a b := by
      refine (closure_minimal (fun x hx => ?_)
        ((isClosed_tsupport g).union (isClosed_tsupport ρ))).trans (union_subset hgs hρs)
      by_contra hx'
      simp only [mem_union, not_or] at hx'
      exact hx (by simp [hφ_def, image_eq_zero_of_notMem_tsupport hx'.1,
        image_eq_zero_of_notMem_tsupport hx'.2])
    have hφint : ∫ x, φ x = 0 := by
      simp only [hφ_def]
      rw [integral_sub hgi (hρi.const_mul _), MeasureTheory.integral_const_mul, hρint,
        mul_one, sub_self]
    obtain ⟨ψ, hψ, hψc, hψs, hψd⟩ :=
      hφ.exists_contDiff_deriv_eq_of_integral_eq_zero hφs hφint
    have h0 := h ψ hψ hψc hψs
    rw [hψd] at h0
    simp only [hφ_def, sub_smul, mul_smul] at h0
    have hρf : Integrable fun x => (∫ y, g y) • ρ x • f x :=
      (hint ρ hρ hρc hρs).smul _
    rw [integral_sub (hint g hg hgc hgs) hρf, MeasureTheory.integral_smul,
      sub_eq_zero] at h0
    simp only [smul_sub]
    rw [integral_sub (hint g hg hgc hgs) (hgi.smul_const _),
      _root_.integral_smul_const, h0, sub_self]
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.sub (locallyIntegrableOn_const _)) key
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hae] with x hx hmem
  exact sub_eq_zero.mp (hx hmem)

theorem exists_ae_const_of_weak_line_zero {a b : ℝ} {f : ℝ → F}
    (h : TauCeti.HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ f (fun _ => 0) 1) :
    ∃ c : F, f =ᵐ[volume.restrict (Ioo a b)] fun _ => c := by
  apply exists_ae_const_of_test_derivatives h.locallyIntegrableOn
  intro ψ hψ hψc hψs
  have he := h.integral_lineDeriv_smul_eq_neg_integral_smul ⟨ψ, hψ, hψc, hψs⟩
  change (∫ x, lineDeriv ℝ ψ x 1 • f x) = -∫ x, ψ x • (0 : F) at he
  have hd (x : ℝ) : lineDeriv ℝ ψ x 1 = deriv ψ x := by
    rw [(hψ.differentiable (by simp) x).lineDeriv_eq_fderiv, fderiv_apply_one_eq_deriv]
  simpa only [hd, smul_zero, integral_zero, neg_zero] using he

theorem exists_ae_const_of_equal_weak_derivatives {a b : ℝ} {f g v : ℝ → F}
    (hf : TauCeti.HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ f v 1)
    (hg : TauCeti.HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ g v 1) :
    ∃ c : F, (fun t => f t - g t) =ᵐ[volume.restrict (Ioo a b)] fun _ => c := by
  have hsub := hf.sub hg
  have hz : (fun t => v t - v t) = (fun _ : ℝ => (0 : F)) := funext fun _ => sub_self _
  change TauCeti.HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
    (fun t => f t - g t) (fun t => v t - v t) 1 at hsub
  rw [hz] at hsub
  exact exists_ae_const_of_weak_line_zero hsub

end

end Finsler.IntervalWeakConstant
