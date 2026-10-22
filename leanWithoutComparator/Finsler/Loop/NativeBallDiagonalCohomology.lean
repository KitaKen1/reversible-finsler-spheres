module

public import Finsler.Loop.LocalOriginalRelativeOutputRelative
public import Finsler.Loop.MeridianEquatorHomology
public import Finsler.Topology.DiagonalCohomology

/-! The ACTUAL diagonal in the native whole-ball chart retracts onto
the remaining equator. Its positive cohomology vanishes outside the
equator dimension, using the pinned Tau Ceti sphere calculation.
This supplies the extra lower primitive needed to correct a seam. -/
@[expose] public section
namespace Finsler.NativeBallDiagonalCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem equator_homology_zero (m q : ℕ) (P : Sphere (m + 1)) (hq : 1 ≤ q) (hqm : q ≠ m) :
    IsZero (homologyZMod2 (TopCat.of (equator P)) q) := by
  let e : TopCat.of (equator P) ≅ TopCat.of (MeridianEquatorHomology.orthogonalSphere P) :=
    TopCat.isoOfHomeo (MeridianEquatorHomology.homeomorph P)
  have he := ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).mapIso e
  cases q with
  | zero => omega
  | succ j =>
    have hz := (TauCeti.isZero_reducedSingularHomologyFunctor_sphere_of_ne coeff
      (MeridianEquatorHomology.orthogonal_dimension P) hqm).of_iso
      ((TauCeti.reducedSingularHomologySuccIso coeff j).app
        (TopCat.of (MeridianEquatorHomology.orthogonalSphere P))).symm
    exact hz.of_iso he

theorem equator_cohomology_zero (m q : ℕ) (P : Sphere (m + 1)) (hq : 1 ≤ q) (hqm : q ≠ m)
    (a : cohomologyZMod2 (TopCat.of (equator P)) q) : a = 0 := by
  let : Subsingleton (homologyZMod2 (TopCat.of (equator P)) q) :=
    ModuleCat.subsingleton_of_isZero (equator_homology_zero m q P hq hqm)
  apply (kroneckerEquiv (TopCat.of (equator P)) q).toLinearEquiv.injective
  ext z
  have hz : z = 0 := Subsingleton.elim _ _
  rw [hz, map_zero, map_zero]

def diagonalSet {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (LocalNativeBallCut.space P v₀) :=
  {z | z.1 = z.2.1}

abbrev diagonal {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopCat.{0} := TopCat.of (diagonalSet P v₀)

def remaining {n : ℕ} (P : Sphere n) (v₀ : equator P) : diagonal P v₀ ⟶ TopCat.of (equator P) :=
  TopCat.ofHom ⟨fun z => z.val.2.2, by fun_prop⟩

def sectionMap {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopCat.of (equator P) ⟶ diagonal P v₀ :=
  TopCat.ofHom ⟨fun z => ⟨(SmallSphereBallContraction.center (LocalNativeBallCut.center P v₀),
    (SmallSphereBallContraction.center (LocalNativeBallCut.center P v₀), z)), rfl⟩, by fun_prop⟩

def contraction {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.Homotopy (𝟙 (diagonal P v₀)) (remaining P v₀ ≫ sectionMap P v₀) where
  toFun z := ⟨(SmallSphereBallContraction.contraction (LocalNativeBallCut.center P v₀) (z.1, z.2.val.1),
    (SmallSphereBallContraction.contraction (LocalNativeBallCut.center P v₀) (z.1, z.2.val.1), z.2.val.2.2)), rfl⟩
  continuous_toFun := by
    have hin : Continuous (fun z : _root_.unitInterval × diagonal P v₀ => (z.1, z.2.val.1)) :=
      continuous_fst.prodMk (continuous_snd.subtype_val.fst)
    have hc := (SmallSphereBallContraction.contraction (LocalNativeBallCut.center P v₀)).continuous.comp
      hin
    exact (hc.prodMk (hc.prodMk (continuous_snd.subtype_val.snd.snd))).subtype_mk _
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · exact (SmallSphereBallContraction.contraction (LocalNativeBallCut.center P v₀)).map_zero_left z.val.1
    · apply Prod.ext
      · exact ((SmallSphereBallContraction.contraction (LocalNativeBallCut.center P v₀)).map_zero_left z.val.1).trans z.property
      · rfl
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · exact (SmallSphereBallContraction.contraction (LocalNativeBallCut.center P v₀)).map_one_left z.val.1
    · apply Prod.ext
      · exact (SmallSphereBallContraction.contraction (LocalNativeBallCut.center P v₀)).map_one_left z.val.1
      · rfl

theorem cohomology_zero (m q : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (hq : 1 ≤ q) (hqm : q ≠ m)
    (a : cohomologyZMod2 (diagonal P v₀) q) : a = 0 := by
  have he := LoopSweepTwoPiece.cohomology_homotopy (contraction P v₀) q a
  rw [Finsler.DiagonalCohomology.pullback_id, Finsler.Cup.pullback_comp] at he
  have hz := equator_cohomology_zero m q P hq hqm ((cohPullback (sectionMap P v₀) q).hom a)
  rw [hz, map_zero] at he
  exact he

end
end Finsler.NativeBallDiagonalCohomology
