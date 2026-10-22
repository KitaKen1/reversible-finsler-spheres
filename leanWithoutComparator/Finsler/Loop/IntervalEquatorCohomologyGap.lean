module

public import Finsler.Loop.NativeBallDiagonalCohomology
public import Finsler.Loop.CommonMeridianSeamPrimitive

/-! Contract the actual interval factor, keeping the original equator.
In every positive degree outside that equator's dimension the entire
interval/equator family has zero cohomology. This uses actual maps and
the pinned sphere calculation, without a Kunneth assumption. -/
@[expose] public section
namespace Finsler.IntervalEquatorCohomologyGap
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def projection (X : TopCat.{0}) : DoubleRelativeTimeCylinder.cylinder X ⟶ X :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

def contraction (X : TopCat.{0}) :
    TopCat.Homotopy (𝟙 (DoubleRelativeTimeCylinder.cylinder X))
      (projection X ≫ DoubleRelativeTimeCylinder.atTime X 0) where
  toFun z := (CommonMeridianSeamPrimitive.contractTime z.1 z.2.1, z.2.2)
  continuous_toFun := by
    have ht : Continuous (fun z : _root_.unitInterval × DoubleRelativeTimeCylinder.cylinder X =>
        CommonMeridianSeamPrimitive.contractTime z.1 z.2.1) := by
      unfold CommonMeridianSeamPrimitive.contractTime
      fun_prop
    exact ht.prodMk continuous_snd.snd
  map_zero_left z := by
    apply Prod.ext
    · apply Subtype.ext
      change (1 - (0 : ℝ)) * (z.1 : ℝ) = (z.1 : ℝ)
      ring
    · rfl
  map_one_left z := by
    apply Prod.ext
    · apply Subtype.ext
      change (1 - (1 : ℝ)) * (z.1 : ℝ) = 0
      ring
    · rfl

theorem cohomology_reduced (X : TopCat.{0}) (q : ℕ)
    (a : cohomologyZMod2 (DoubleRelativeTimeCylinder.cylinder X) q) :
    a = (cohPullback (projection X) q).hom
      ((cohPullback (DoubleRelativeTimeCylinder.atTime X 0) q).hom a) := by
  have he := LoopSweepTwoPiece.cohomology_homotopy (contraction X) q a
  rw [Finsler.DiagonalCohomology.pullback_id, Finsler.Cup.pullback_comp] at he
  exact he

theorem equator_zero (m q : ℕ) (P : Sphere (m + 1)) (hq : 1 ≤ q) (hqm : q ≠ m)
    (a : cohomologyZMod2 (TopCat.of (ClosedInterval × equator P)) q) : a = 0 := by
  have he := cohomology_reduced (TopCat.of (equator P)) q a
  have hz := NativeBallDiagonalCohomology.equator_cohomology_zero m q P hq hqm
    ((cohPullback (DoubleRelativeTimeCylinder.atTime (TopCat.of (equator P)) 0) q).hom a)
  rw [hz, map_zero] at he
  exact he

end
end Finsler.IntervalEquatorCohomologyGap
