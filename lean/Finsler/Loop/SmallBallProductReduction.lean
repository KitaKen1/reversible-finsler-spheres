module

public import Finsler.Loop.SmallSphereBallContraction
public import Finsler.Loop.LoopSweepTwoPiece

/-! Two actual small spherical balls contract to their centers,
keeping an arbitrary third factor fixed. Every actual map out of
this product has the same cohomology pullback as its true center
slice followed by the remaining-factor projection. -/
@[expose] public section
namespace Finsler.SmallBallProductReduction
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

abbrev space {n : ℕ} (Q : Sphere n) (Z : TopCat.{0}) : TopCat.{0} :=
  TopCat.of (SmallSphereBallContraction.space Q × (SmallSphereBallContraction.space Q × Z))

def remaining {n : ℕ} (Q : Sphere n) (Z : TopCat.{0}) : space Q Z ⟶ Z :=
  TopCat.ofHom ⟨fun z => z.2.2, continuous_snd.snd⟩
def sectionMap {n : ℕ} (Q : Sphere n) (Z : TopCat.{0}) : Z ⟶ space Q Z :=
  TopCat.ofHom ⟨fun z => (SmallSphereBallContraction.center Q, (SmallSphereBallContraction.center Q, z)),
    continuous_const.prodMk (continuous_const.prodMk continuous_id)⟩

def contraction {n : ℕ} (Q : Sphere n) (Z : TopCat.{0}) :
    TopCat.Homotopy (𝟙 (space Q Z)) (remaining Q Z ≫ sectionMap Q Z) where
  toFun z := (SmallSphereBallContraction.contraction Q (z.1, z.2.1),
    (SmallSphereBallContraction.contraction Q (z.1, z.2.2.1), z.2.2.2))
  continuous_toFun := by
    have hl : Continuous (fun z : _root_.unitInterval × space Q Z => (z.1, z.2.1)) := continuous_fst.prodMk continuous_snd.fst
    have hr : Continuous (fun z : _root_.unitInterval × space Q Z => (z.1, z.2.2.1)) := continuous_fst.prodMk continuous_snd.snd.fst
    have hcl := (SmallSphereBallContraction.contraction Q).continuous.comp hl
    have hcr := (SmallSphereBallContraction.contraction Q).continuous.comp hr
    exact (hcl.prodMk (hcr.prodMk continuous_snd.snd.snd)).congr (fun _ => rfl)
  map_zero_left z := by
    change (SmallSphereBallContraction.contraction Q (0, z.1),
      (SmallSphereBallContraction.contraction Q (0, z.2.1), z.2.2)) = z
    exact Prod.ext ((SmallSphereBallContraction.contraction Q).map_zero_left z.1)
      (Prod.ext ((SmallSphereBallContraction.contraction Q).map_zero_left z.2.1) rfl)
  map_one_left z := by
    change (SmallSphereBallContraction.contraction Q (1, z.1),
      (SmallSphereBallContraction.contraction Q (1, z.2.1), z.2.2)) = _
    exact Prod.ext ((SmallSphereBallContraction.contraction Q).map_one_left z.1)
      (Prod.ext ((SmallSphereBallContraction.contraction Q).map_one_left z.2.1) rfl)

theorem remaining_section {n : ℕ} (Q : Sphere n) (Z : TopCat.{0}) : sectionMap Q Z ≫ remaining Q Z = 𝟙 Z := by
  apply TopCat.ext
  intro z
  rfl

theorem pullback_reduced {n : ℕ} (Q : Sphere n) (Z Y : TopCat.{0}) (f : space Q Z ⟶ Y)
    (q : ℕ) (a : SphereOddDegree.cohomologyZMod2 Y q) :
    (cohPullback f q).hom a = (cohPullback (remaining Q Z) q).hom
      ((cohPullback (sectionMap Q Z ≫ f) q).hom a) := by
  have he := LoopSweepTwoPiece.cohomology_homotopy
    (TopCat.Homotopy.comp (TopCat.Homotopy.refl f) (contraction Q Z)) q a
  change (cohPullback f q).hom a = (cohPullback ((remaining Q Z ≫ sectionMap Q Z) ≫ f) q).hom a at he
  rw [Category.assoc] at he
  exact he.trans (ConcreteCategory.congr_hom
    ((SphereOddDegree.singularCohomologyZMod2 q).map_comp (sectionMap Q Z ≫ f).op (remaining Q Z).op) a)

end
end Finsler.SmallBallProductReduction
