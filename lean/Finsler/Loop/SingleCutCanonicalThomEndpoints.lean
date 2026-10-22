module

public import Finsler.Loop.SingleCutCanonicalThomCochains

/-! Literal endpoint support for the canonical Thom/tested cup and
the annular comparison primitive. Each time slice has its own source
set, so no unproved vanishing on a union or positive collar is used. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalThomEndpoints

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.FirstInputSelfCutCochains
open Finsler.SingleCutCanonicalThomCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1)))

def sliceSet (t : ClosedInterval) : Set (ambient α) := {z | z.1 = t}

def sliceFamily (t : ClosedInterval) : TopCat.of (sliceSet α t) ⟶ TopCat.of (SphereLoop (m + 1)) :=
  TopCat.ofHom ⟨fun z => α z.val.2, α.continuous.comp (continuous_snd.comp continuous_subtype_val)⟩

theorem slice_square (t : ClosedInterval) :
    SupportedCap.subspaceMap (ambient α) (sliceSet α t) ≫ AnnularSelfCut.familyMap α =
      sliceFamily α t ≫ SelfCutThomCocycle.atTime (m + 1) t := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact Prod.ext z.property rfl

variable {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)

theorem canonicalThom_slice_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (sliceSet α t)) (m + 1)
      (canonicalThom α h) = 0 := by
  rw [canonicalThom, ← pullback_comp, slice_square, pullback_comp]
  rcases ht with rfl | rfl
  · rw [NormalizedSelfCut.time_zero]
    exact map_zero _
  · rw [NormalizedSelfCut.time_one]
    exact map_zero _

variable (r : ℝ) (hr : r < 1) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

theorem gamma_slice_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (sliceSet α t)) ((m + 1) + p)
      (canonicalGamma α r hr h p T) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ rfl _ _ (Or.inl (canonicalThom_slice_zero α h t ht))

variable (hm : 1 ≤ m) (hρ2 : ρ ≤ 2)

theorem thomPrimitive_slice_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (sliceSet α t)) m
      (thomPrimitive α h hm hρ2) = 0 := by
  rw [thomPrimitive, ← pullback_comp, slice_square, pullback_comp]
  rcases ht with rfl | rfl
  · have hz := AnnularSelfCut.primitive_time_zero (m + 1) (show 2 ≤ m + 1 by omega) h hρ2
    change cochainPullback (SelfCutThomCocycle.atTime (m + 1) 0) m
      (AnnularSelfCut.primitive (m + 1) (by omega) h hρ2) = 0 at hz
    rw [hz]
    exact map_zero _
  · have hz := AnnularSelfCut.primitive_time_one (m + 1) (show 2 ≤ m + 1 by omega) h hρ2
    change cochainPullback (SelfCutThomCocycle.atTime (m + 1) 1) m
      (AnnularSelfCut.primitive (m + 1) (by omega) h hρ2) = 0 at hz
    rw [hz]
    exact map_zero _

theorem primitive_slice_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (sliceSet α t)) (m + p)
      (comparisonPrimitive α r hr h p T hm hρ2) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ rfl _ _ (Or.inl (thomPrimitive_slice_zero α h hm hρ2 t ht))

end
end Finsler.SingleCutCanonicalThomEndpoints
