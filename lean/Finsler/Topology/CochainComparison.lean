module

public import Finsler.Topology.RelativeCohomology
public import Finsler.Topology.Cup

/-! Compare Lean Pool's absolute cochains with the ambient cochains in
Tau Ceti's relative theory. The component maps are identities; the different
functor constructions are compared as complexes, not assumed equal. -/

@[expose] public section

namespace Finsler.CochainComparison

open CategoryTheory SphereOddDegree

noncomputable section

abbrev coeff := Finsler.RelativeCohomology.coeff

abbrev native (X : TopCat.{0}) := X.singularCochainComplex coeff (ZMod 2) coeff

def cochainIso (X : TopCat.{0}) : cochainCxZMod2 X ≅ native X :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    rfl)

theorem cochain_natural {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (singularCochainComplexZMod2.map f.op) ≫ (cochainIso X).hom =
      (cochainIso Y).hom ≫
        TopCat.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) f := by
  ext i
  rfl

def cohomologyIso (X : TopCat.{0}) (n : ℕ) :
    cohomologyZMod2 X n ≅ X.singularCohomology coeff (ZMod 2) coeff n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (cochainIso X)

theorem cohomology_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    cohPullback f n ≫ (cohomologyIso X n).hom =
      (cohomologyIso Y n).hom ≫
        TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f n := by
  simpa only [HomologicalComplex.homologyMap_comp, cohomologyIso, cohPullback,
    Functor.mapIso_hom, singularCohomologyZMod2, singularCohomologyFunctor, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map] using
    congrArg (fun g => HomologicalComplex.homologyMap g n) (cochain_natural f)

theorem cohomology_natural_apply {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : cohomologyZMod2 Y n) :
    (cohomologyIso X n).hom.hom ((cohPullback f n).hom a) =
      (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f n).hom
        ((cohomologyIso Y n).hom.hom a) :=
  ConcreteCategory.congr_hom (cohomology_natural f n) a

/-- A Lean Pool absolute class has a lift in Tau Ceti's actual relative
cohomology, with no comparison hypothesis left in the statement. -/
theorem relative_lift (P : TopPair.{0}) (n : ℕ) (a : cohomologyZMod2 P.fst n)
    (ha : (cohPullback P.map n).hom a = 0) :
    ∃ b : P.singularCohomology coeff (ZMod 2) coeff n,
      (P.singularCohomologyπ coeff (ZMod 2) coeff n).hom b =
        (cohomologyIso P.fst n).hom.hom a := by
  apply Finsler.RelativeCohomology.relative_lift
  rw [← cohomology_natural_apply, ha, map_zero]

abbrev cohomologyEquiv (X : TopCat.{0}) (n : ℕ) := (cohomologyIso X n).toLinearEquiv

theorem cohomology_inv_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : Y.singularCohomology coeff (ZMod 2) coeff n) :
    (cohPullback f n).hom ((cohomologyEquiv Y n).symm a) =
      (cohomologyEquiv X n).symm
        ((TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f n).hom a) := by
  apply (cohomologyEquiv X n).injective
  rw [LinearEquiv.apply_symm_apply]
  change (cohomologyEquiv X n) ((cohPullback f n).hom ((cohomologyEquiv Y n).symm a)) = _
  have h := cohomology_natural_apply f n ((cohomologyEquiv Y n).symm a)
  change (cohomologyEquiv X n) _ =
    (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f n).hom
      ((cohomologyEquiv Y n) ((cohomologyEquiv Y n).symm a)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- Exactness on actual relative cohomology, expressed entirely using Lean
Pool's absolute class and restriction map. -/
theorem relative_lift_iff (P : TopPair.{0}) (n : ℕ) (a : cohomologyZMod2 P.fst n) :
    (cohPullback P.map n).hom a = 0 ↔
      ∃ b : P.singularCohomology coeff (ZMod 2) coeff n,
        (P.singularCohomologyπ coeff (ZMod 2) coeff n).hom b =
          (cohomologyEquiv P.fst n) a := by
  constructor
  · exact relative_lift P n a
  · rintro ⟨b, hb⟩
    apply (cohomologyEquiv P.snd n).injective
    change (cohomologyIso P.snd n).hom.hom ((cohPullback P.map n).hom a) = _
    rw [cohomology_natural_apply]
    change _ = (cohomologyEquiv P.snd n) 0
    change (P.singularCohomologyπ coeff (ZMod 2) coeff n).hom b =
      (cohomologyIso P.fst n).hom.hom a at hb
    rw [map_zero, ← hb]
    exact ConcreteCategory.congr_hom
      (P.singularCohomologyπ_comp_singularCohomologyMap coeff (ZMod 2) coeff n) b

def relativeToPool (P : TopPair.{0}) (n : ℕ) :
    P.singularCohomology coeff (ZMod 2) coeff n ⟶ cohomologyZMod2 P.fst n :=
  P.singularCohomologyπ coeff (ZMod 2) coeff n ≫ (cohomologyIso P.fst n).inv

theorem relative_to_absolute_natural {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ) :
    TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f n ≫
      relativeToPool P n = relativeToPool Q n ≫ cohPullback (TopPair.Hom.fst f) n := by
  ext b
  change (cohomologyEquiv P.fst n).symm
    ((P.singularCohomologyπ coeff (ZMod 2) coeff n).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f n).hom b)) =
    (cohPullback (TopPair.Hom.fst f) n).hom
      ((cohomologyEquiv Q.fst n).symm
        ((Q.singularCohomologyπ coeff (ZMod 2) coeff n).hom b))
  rw [cohomology_inv_natural]
  exact congrArg ((cohomologyEquiv P.fst n).symm)
    (ConcreteCategory.congr_hom
      (TopPair.singularCohomologyπ_naturality (R := coeff) (k := ZMod 2) (M := coeff) f n) b).symm

end

end Finsler.CochainComparison
