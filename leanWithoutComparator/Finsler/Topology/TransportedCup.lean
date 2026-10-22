module

public import Finsler.Topology.CochainComparison

/-! Transport the checked absolute cup product to Tau Ceti's ambient
cohomology. This does not identify it with Tau Ceti's separate tensor-product
cup construction, and does not yet construct a relative cup module action.
The last theorem proves the weaker, useful relative-image closure statement. -/

@[expose] public section

namespace Finsler.TransportedCup

open CategoryTheory SphereOddDegree Finsler.CochainComparison

noncomputable section

abbrev absolute (X : TopCat.{0}) (n : ℕ) :=
  X.singularCohomology coeff (ZMod 2) coeff n

def cup {X : TopCat.{0}} (p q : ℕ) (a : absolute X p) (b : absolute X q) :
    absolute X (p + q) :=
  (cohomologyEquiv X (p + q))
    (cupZMod2 ((cohomologyEquiv X p).symm a) ((cohomologyEquiv X q).symm b))

theorem comparison {X : TopCat.{0}} (p q : ℕ)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) :
    cup p q ((cohomologyEquiv X p) a) ((cohomologyEquiv X q) b) =
      (cohomologyEquiv X (p + q)) (cupZMod2 a b) := by
  simp only [cup, LinearEquiv.symm_apply_apply]

theorem naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (a : absolute Y p) (b : absolute Y q) :
    (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f (p + q)).hom
        (cup p q a b) =
      cup p q
        ((TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f p).hom a)
        ((TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f q).hom b) := by
  unfold cup
  change (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f (p + q)).hom
    ((cohomologyIso Y (p + q)).hom.hom _) = _
  rw [← cohomology_natural_apply, Finsler.Cup.naturality]
  rw [cohomology_inv_natural, cohomology_inv_natural]
  rfl

theorem zero_left {X : TopCat.{0}} (p q : ℕ) (b : absolute X q) :
    cup p q (0 : absolute X p) b = 0 := by
  simp only [cup, map_zero, Finsler.Cup.zero_cup]

theorem zero_right {X : TopCat.{0}} (p q : ℕ) (a : absolute X p) :
    cup p q a (0 : absolute X q) = 0 := by
  simp only [cup, map_zero, Finsler.Cup.cup_zero]

/-- A factorization killing the ambient class kills its transported absolute
cup action. A punctured-sphere factorization is still a geometric input. -/
theorem evaluation_zero {X P Y : TopCat.{0}} (f : X ⟶ P) (g : P ⟶ Y)
    (p q : ℕ) (e : absolute Y p) (b : absolute X q)
    (he : (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) g p).hom e = 0) :
    cup p q
      ((TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (f ≫ g) p).hom e) b = 0 := by
  have h : (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (f ≫ g) p).hom e = 0 := by
    rw [TopCat.singularCohomologyMap_comp]
    change (TopCat.singularCohomologyMap f p).hom
      ((TopCat.singularCohomologyMap g p).hom e) = 0
    rw [he, map_zero]
  rw [h, zero_left]

/-- The image of relative cohomology is closed under left multiplication by
ambient absolute classes. This proves existence of a lift, not a canonical
relative cup operation or its naturality. -/
theorem relative_image_closed (P : TopPair.{0}) (p q : ℕ)
    (a : absolute P.fst p) (b : P.singularCohomology coeff (ZMod 2) coeff q) :
    ∃ c : P.singularCohomology coeff (ZMod 2) coeff (p + q),
      (P.singularCohomologyπ coeff (ZMod 2) coeff (p + q)).hom c =
        cup p q a ((P.singularCohomologyπ coeff (ZMod 2) coeff q).hom b) := by
  apply Finsler.RelativeCohomology.relative_lift
  rw [naturality]
  have hb : (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) P.map q).hom
      ((P.singularCohomologyπ coeff (ZMod 2) coeff q).hom b) = 0 :=
    ConcreteCategory.congr_hom
      (P.singularCohomologyπ_comp_singularCohomologyMap coeff (ZMod 2) coeff q) b
  rw [hb, zero_right]

end

end Finsler.TransportedCup
