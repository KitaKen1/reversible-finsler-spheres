module

public import Finsler.Loop.ContinuousLoopModel
public import Finsler.Geometry.SphereRetraction

/-! Actual normalized affine homotopies for uniformly close sphere
maps. The affine vector is proved nonzero at every time; the genuine
sphere retraction supplies continuity, including both endpoints. -/

@[expose] public section
namespace Finsler.CloseSphereHomotopy
open CategoryTheory
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelEvaluation
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1000000

theorem blend_ne_zero {n : ℕ} (t : ClosedInterval) (P Q : Sphere n) (hPQ : dist P Q < 1) :
    (1 - (t : ℝ)) • (P : Ambient n) + (t : ℝ) • (Q : Ambient n) ≠ 0 := by
  have he : (1 - (t : ℝ)) • (P : Ambient n) + (t : ℝ) • (Q : Ambient n) - P =
      (t : ℝ) • ((Q : Ambient n) - P) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  have hQ : ‖(Q : Ambient n) - P‖ < 1 := by
    simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hPQ
  have hb : ‖(1 - (t : ℝ)) • (P : Ambient n) + (t : ℝ) • (Q : Ambient n) - P‖ < 1 := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    rcases t.property with ⟨ht₀, ht₁⟩
    nlinarith [norm_nonneg ((Q : Ambient n) - P)]
  intro hz
  have hP : ‖(P : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp P.property
  rw [hz, zero_sub, norm_neg, hP] at hb
  exact (lt_irrefl (1 : ℝ)) hb

def homotopy {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) (h : ∀ x, dist (f x) (g x) < 1) :
    TopCat.Homotopy f g where
  toFun z := SphereRetraction.normalize ((1 - (z.1 : ℝ)) • (f z.2 : Ambient n) + (z.1 : ℝ) • (g z.2 : Ambient n))
  continuous_toFun := by
    have hc : Continuous (fun z : ClosedInterval × X =>
        (1 - (z.1 : ℝ)) • (f z.2 : Ambient n) + (z.1 : ℝ) • (g z.2 : Ambient n)) :=
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp (f.hom.continuous.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (g.hom.continuous.comp continuous_snd)))
    let b : ClosedInterval × X → Ambient n := fun z =>
      (1 - (z.1 : ℝ)) • (f z.2 : Ambient n) + (z.1 : ℝ) • (g z.2 : Ambient n)
    let v : ClosedInterval × X → SphereRetraction.nonzeroAmbient n := fun z =>
      ⟨b z, blend_ne_zero z.1 (f z.2) (g z.2) (h z.2)⟩
    have hv : Continuous v := hc.subtype_mk _
    have hn := (SphereRetraction.normalizedNonzero_smooth n).continuous.comp hv
    exact hn.congr (fun z => (SphereRetraction.normalize_coe (v z)).symm)
  map_zero_left x := by
    change SphereRetraction.normalize ((1 - (0 : ℝ)) • (f x : Ambient n) + (0 : ℝ) • (g x : Ambient n)) = f x
    rw [sub_zero, one_smul, zero_smul, add_zero]
    exact SphereRetraction.normalize_inclusion (f x)
  map_one_left x := by
    change SphereRetraction.normalize ((1 - (1 : ℝ)) • (f x : Ambient n) + (1 : ℝ) • (g x : Ambient n)) = g x
    rw [sub_self, zero_smul, one_smul, zero_add]
    exact SphereRetraction.normalize_inclusion (g x)

theorem fixed {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) (h : ∀ x, dist (f x) (g x) < 1)
    (x : X) (hx : f x = g x) (t : ClosedInterval) : homotopy f g h (t, x) = f x := by
  change SphereRetraction.normalize ((1 - (t : ℝ)) • (f x : Ambient n) + (t : ℝ) • (g x : Ambient n)) = f x
  rw [← hx, ← add_smul, sub_add_cancel, one_smul]
  exact SphereRetraction.normalize_inclusion (f x)

end
end Finsler.CloseSphereHomotopy
