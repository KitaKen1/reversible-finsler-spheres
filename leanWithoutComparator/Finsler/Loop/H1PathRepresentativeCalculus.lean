module

public import Finsler.Analysis.H1ConcatContinuity
public import Finsler.Analysis.IntervalH1Reverse
public import Mathlib.Topology.Path

/-! Exact matching of original strong-H1 concatenation/reversal
with actual ordinary Path operations. No smoothing or new graph
model is introduced. -/
@[expose] public section
namespace Finsler.H1PathRepresentativeCalculus
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevConcat
open Finsler.SobolevReverse Finsler.H1ConcatContinuity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def halfConcat {n : ℕ} (u w : Space n) : Space n :=
  concat u w (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)

theorem continuous_halfConcat {n : ℕ} {X : Type*} [TopologicalSpace X]
    (u w : X → Space n) (hu : Continuous u) (hw : Continuous w)
    (hm : ∀ x, continuousRepresentative (u x) 1 = continuousRepresentative (w x) 0) :
    Continuous (fun x => halfConcat (u x) (w x)) := by
  have hpair : Continuous (fun x : X => (⟨(u x, w x),
      show (u x, w x) ∈ matching n from sub_eq_zero.mpr (hm x)⟩ : matching n)) :=
    (hu.prodMk hw).subtype_mk _
  have hc := (continuous_concatenation (n := n) (1 / 2) (by norm_num) (by norm_num)).comp hpair
  exact hc.congr (fun _ => rfl)

theorem represented_concat {n : ℕ} {P Q R : Sphere n} (u w : Space n)
    (γ : Path P Q) (δ : Path Q R)
    (hu : ∀ t : _root_.unitInterval, continuousRepresentative u (t : ℝ) = (γ t : Ambient n))
    (hw : ∀ t : _root_.unitInterval, continuousRepresentative w (t : ℝ) = (δ t : Ambient n))
    (t : _root_.unitInterval) :
    continuousRepresentative (halfConcat u w) (t : ℝ) = (γ.trans δ t : Ambient n) := by
  have hm : continuousRepresentative u 1 = continuousRepresentative w 0 := by
    have h₁ := hu 1
    have h₀ := hw 0
    simp only [Set.Icc.coe_one, γ.target] at h₁
    simp only [Set.Icc.coe_zero, δ.source] at h₀
    exact h₁.trans h₀.symm
  rw [Path.trans_apply]
  split_ifs with h
  · rw [halfConcat, representative_concat_left u w (by norm_num) (by norm_num) ⟨t.property.1, h⟩]
    have ht : 2 * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [t.property.1]
    simpa only [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num] using hu ⟨2 * (t : ℝ), ht⟩
  · rw [halfConcat, representative_concat_right u w (by norm_num) (by norm_num) hm
      ⟨(not_le.mp h).le, t.property.2⟩]
    have ht : 2 * (t : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [t.property.2]
    have he : rightMap (1 / 2 : ℝ) (t : ℝ) = 2 * (t : ℝ) - 1 := by unfold rightMap; norm_num; ring
    rw [he]
    exact hw ⟨2 * (t : ℝ) - 1, ht⟩

theorem represented_reverse {n : ℕ} {P Q : Sphere n} (u : Space n) (γ : Path P Q)
    (hu : ∀ t : _root_.unitInterval, continuousRepresentative u (t : ℝ) = (γ t : Ambient n))
    (t : _root_.unitInterval) :
    continuousRepresentative (reverseData u) (t : ℝ) = (γ.symm t : Ambient n) := by
  rw [representative_reverseData u t.property]
  exact hu (unitInterval.symm t)

end
end Finsler.H1PathRepresentativeCalculus
