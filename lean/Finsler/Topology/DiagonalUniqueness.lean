module

public import Finsler.Topology.DiagonalCohomology
public import TauCeti.Topology.Category.TopPair

/-! The actual relative diagonal class is unique in dimensions at least two.
Its restriction to every sphere slice has the canonical top-class normalization. -/

@[expose] public section

namespace Finsler.DiagonalUniqueness

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.DiagonalGeometry Finsler.SphereTopClass
open Finsler.BorelEvaluation Finsler.CochainComparison Finsler.DiagonalCohomology
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem deleted_cohomology_zero (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≠ n)
    (a : cohomologyZMod2 (diagonalPair n).snd k) : a = 0 := by
  let f : (diagonalPair n).snd ⟶ sphere n := (diagonalPair n).map ≫ prFirst n
  let g : sphere n ⟶ (diagonalPair n).snd := TopCat.ofHom (sectionMap n)
  let H : TopCat.Homotopy (𝟙 (diagonalPair n).snd) (f ≫ g) := retractionHomotopy n
  have he := homotopy_pullback H k a
  have hz : (cohPullback g k).hom a = 0 := cohomology_eq_zero_of_ne n k hk hkn _
  rw [pullback_id, Cup.pullback_comp, hz, map_zero] at he
  exact he

theorem relative_image_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective ((diagonalPair n).singularCohomologyπ coeff (ZMod 2) coeff n).hom := by
  have hzero (a : (diagonalPair n).snd.singularCohomology coeff (ZMod 2) coeff (n - 1)) : a = 0 := by
    let e := Finsler.CochainComparison.cohomologyEquiv (diagonalPair n).snd (n - 1)
    calc
      a = e (e.symm a) := (e.apply_symm_apply a).symm
      _ = e 0 := congrArg e (deleted_cohomology_zero n (n - 1) (by omega) (by omega) _)
      _ = 0 := map_zero _
  have he := (diagonalPair n).singularCohomology_exact_relative coeff (ZMod 2) coeff
    (n - 1) n (by omega)
  intro a b hab
  have hz : ((diagonalPair n).singularCohomologyπ coeff (ZMod 2) coeff n).hom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp he (a - b) hz
  rw [hzero c, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

theorem existsUnique_relative_diagonal (n : ℕ) (hn : 2 ≤ n) :
    ∃! T : (diagonalPair n).singularCohomology coeff (ZMod 2) coeff n,
      ((diagonalPair n).singularCohomologyπ coeff (ZMod 2) coeff n).hom T =
        Finsler.CochainComparison.cohomologyEquiv (product n) n (ambientClass n (by omega)) := by
  refine ⟨relativeClass n (by omega), relativeClass_image n (by omega), fun T hT => ?_⟩
  apply relative_image_injective n hn
  exact hT.trans (relativeClass_image n (by omega)).symm

def puncturedPair (n : ℕ) (y : Sphere n) : TopPair.{0} :=
  TopPair.ofSubset (X := sphere n) ({y}ᶜ : Set (Sphere n))

def fiberPairMap (n : ℕ) (y : Sphere n) : puncturedPair n y ⟶ diagonalPair n :=
  TopPair.ofSubsetMap (B := ({y}ᶜ : Set (Sphere n))) (B' := deleted n) (fiber n y) (by
    intro x hx
    change y ≠ x
    exact Ne.symm (by simpa using hx))

theorem fiberPairMap_fst (n : ℕ) (y : Sphere n) :
    TopPair.Hom.fst (fiberPairMap n y) = fiber n y := by
  ext x : 1
  exact TopPair.ofSubsetMap_fst_apply (B := ({y}ᶜ : Set (Sphere n))) (B' := deleted n)
    (fiber n y) (by
      intro z hz
      change y ≠ z
      exact Ne.symm (by simpa using hz)) x

def fiberClass (n : ℕ) (hn : 1 ≤ n) (y : Sphere n) :
    (puncturedPair n y).singularCohomology coeff (ZMod 2) coeff n :=
  (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
    (fiberPairMap n y) n).hom (relativeClass n hn)

/-- Every transverse sphere slice carries the canonical nonzero F₂ top class. -/
theorem fiberClass_normalized (n : ℕ) (hn : 1 ≤ n) (y : Sphere n) :
    (relativeToPool (puncturedPair n y) n).hom (fiberClass n hn y) = topClass n hn := by
  have hnatur := congrArg (fun f => f.hom (relativeClass n hn))
    (relative_to_absolute_natural (fiberPairMap n y) n)
  change (relativeToPool (puncturedPair n y) n).hom (fiberClass n hn y) =
    (cohPullback (TopPair.Hom.fst (fiberPairMap n y)) n).hom
      ((relativeToPool (diagonalPair n) n).hom (relativeClass n hn)) at hnatur
  calc
    _ = (cohPullback (TopPair.Hom.fst (fiberPairMap n y)) n).hom
        (ambientClass n hn) := hnatur.trans (congrArg
          (fun a => (cohPullback (TopPair.Hom.fst (fiberPairMap n y)) n).hom a)
          (relativeClass_pool_image n hn))
    _ = (cohPullback (fiber n y) n).hom (ambientClass n hn) := congrArg
      (fun f => (cohPullback f n).hom (ambientClass n hn)) (fiberPairMap_fst n y)
    _ = topClass n hn := fiber_pullback n hn y

theorem fiberClass_ne_zero (n : ℕ) (hn : 1 ≤ n) (y : Sphere n) : fiberClass n hn y ≠ 0 := by
  intro h
  have he := fiberClass_normalized n hn y
  rw [h, map_zero] at he
  exact topClass_ne_zero n hn he.symm


end
end Finsler.DiagonalUniqueness
