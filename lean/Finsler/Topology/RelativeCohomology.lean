module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.ZMod.Defs

/-! Tau Ceti's actual relative cochain model, specialized to F₂.
This is a second usable cohomology model, alongside Lean Pool's absolute model.
CochainComparison supplies the absolute comparison, and RelativeCup descends
the corresponding actual relative pairing. -/

@[expose] public section

namespace Finsler.RelativeCohomology

open CategoryTheory

noncomputable section

abbrev coeff : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ZMod 2)

theorem cochain_short_exact (P : TopPair.{0}) :
    (P.singularCochainComplexShortComplex coeff (ZMod 2) coeff).ShortExact :=
  P.shortExact_singularCochainComplexShortComplex coeff (ZMod 2) coeff

theorem exact_at_ambient (P : TopPair.{0}) (n : ℕ) :
    (ShortComplex.mk _ _
      (P.singularCohomologyπ_comp_singularCohomologyMap coeff (ZMod 2) coeff n)).Exact :=
  P.singularCohomology_exact_space coeff (ZMod 2) coeff n

theorem relative_lift (P : TopPair.{0}) (n : ℕ)
    (a : P.fst.singularCohomology coeff (ZMod 2) coeff n)
    (ha : (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) P.map n).hom a = 0) :
    ∃ b : P.singularCohomology coeff (ZMod 2) coeff n,
      (P.singularCohomologyπ coeff (ZMod 2) coeff n).hom b = a :=
  (ShortComplex.moduleCat_exact_iff _).mp (exact_at_ambient P n) a ha

theorem boundary_natural {P Q : TopPair.{0}} (f : P ⟶ Q) (n m : ℕ) (h : n + 1 = m) :
    (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (TopPair.Hom.snd f) n) ≫ P.singularCohomologyδ coeff (ZMod 2) coeff n m h =
      Q.singularCohomologyδ coeff (ZMod 2) coeff n m h ≫
        TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f m :=
  (TopPair.singularCohomologyδ_naturality (R := coeff) (k := ZMod 2) (M := coeff)
    f n m h).symm

end

end Finsler.RelativeCohomology
