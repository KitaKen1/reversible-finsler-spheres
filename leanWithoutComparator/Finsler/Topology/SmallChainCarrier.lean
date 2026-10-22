module

public import Finsler.Topology.CochainComparison
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-! Locality of the actual small-chain approximation, over the project's F₂.
The subdivision cover U and the carrier family V are independent: the
approximation prism chosen using U still preserves every carrier V. -/

@[expose] public section

namespace Finsler.SmallChainCarrier

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open Finsler.CochainComparison TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

abbrev chains (X : TopCat.{0}) := (TopCat.toSSet.obj X).chainComplex coeff
abbrev small (X : TopCat.{0}) {ι : Type*} (V : ι → Set X) :=
  (X.smallSingularSubcomplex V : SSet).chainComplex coeff
abbrev inclusion (X : TopCat.{0}) {ι : Type*} (V : ι → Set X) :=
  SSet.chainComplexMap (X.smallSingularSubcomplex V).ι coeff
abbrev supported (X : TopCat.{0}) {ι : Type*} (V : ι → Set X) (n : ℕ) :=
  TauCeti.smallSingularChains coeff V n

theorem boundary_preserves {X : TopCat.{0}} {ι : Type*} (V : ι → Set X) {n : ℕ}
    {f : coeff ⟶ (chains X).X (n + 1)} (hf : f ∈ supported X V (n + 1)) :
    f ≫ (chains X).d (n + 1) n ∈ supported X V n := by
  obtain ⟨g, rfl⟩ := (TauCeti.mem_smallSingularChains_iff _).mp hf
  refine (TauCeti.mem_smallSingularChains_iff _).mpr
    ⟨g ≫ (small X V).d (n + 1) n, ?_⟩
  simp only [Category.assoc, HomologicalComplex.Hom.comm]

theorem iteratedPrism_preserves {X : TopCat.{0}} {ι : Type*} (V : ι → Set X) {n : ℕ}
    {f : coeff ⟶ (chains X).X n} (hf : f ∈ supported X V n) (m : ℕ) :
    f ≫ ((singularSubdivisionHomotopy coeff X).idPow m).hom n (n + 1) ∈
      supported X V (n + 1) := by
  rw [Homotopy.idPow_hom, Preadditive.comp_sum]
  refine (supported X V (n + 1)).sum_mem fun k hk => ?_
  rw [← Category.assoc, singularSubdivisionHomotopy_hom]
  apply TauCeti.smallSingularChains.comp_singularPrismX
  exact TauCeti.smallSingularChains.comp_singularSubdivisionChainMap_pow_of_le
    (m := 0) (Nat.zero_le k) (by simpa using hf)

def restrictedApproxHom {X : TopCat.{0}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set X) (n : ℕ) :
    (small X V).X n ⟶ (small X V).X (n + 1) :=
  Cofan.IsColimit.desc ((X.smallSingularSubcomplex V : SSet).isColimitChainComplexXCofan coeff n)
    fun σ => ((TauCeti.mem_smallSingularChains_iff _).mp
      (iteratedPrism_preserves V (TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff) σ)
        (singularSubdivisionDepth coeff U n σ.val))).choose

theorem restrictedApproxHom_inclusion {X : TopCat.{0}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set X) (n : ℕ) :
    restrictedApproxHom U V n ≫ (inclusion X V).f (n + 1) =
      (inclusion X V).f n ≫ singularSmallApproxHom coeff U n (n + 1) := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex V : SSet)) (R := coeff)
  intro σ
  have hs := iteratedPrism_preserves V
    (TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff) σ)
    (singularSubdivisionDepth coeff U n σ.val)
  have hc : (X.smallSingularSubcomplex V : SSet).ιChainComplex σ ≫ restrictedApproxHom U V n =
      ((TauCeti.mem_smallSingularChains_iff _).mp hs).choose :=
    Cofan.IsColimit.fac _ _ σ
  calc
    _ = ((TauCeti.mem_smallSingularChains_iff _).mp hs).choose ≫
        (inclusion X V).f (n + 1) := by rw [← Category.assoc, hc]
    _ = (TopCat.toSSet.obj X).ιChainComplex σ.val ≫
        ((singularSubdivisionHomotopy coeff X).idPow
          (singularSubdivisionDepth coeff U n σ.val)).hom n (n + 1) :=
      ((TauCeti.mem_smallSingularChains_iff _).mp hs).choose_spec
    _ = _ := by
      rw [← Category.assoc, SSet.ι_chainComplexMap_f,
        ιChainComplex_singularSmallApproxHom]
      rfl

theorem approximationPrism_preserves {X : TopCat.{0}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set X) {n : ℕ}
    {f : coeff ⟶ (chains X).X n} (hf : f ∈ supported X V n) :
    f ≫ singularSmallApproxHom coeff U n (n + 1) ∈ supported X V (n + 1) := by
  obtain ⟨g, rfl⟩ := (TauCeti.mem_smallSingularChains_iff _).mp hf
  refine (TauCeti.mem_smallSingularChains_iff _).mpr ⟨g ≫ restrictedApproxHom U V n, ?_⟩
  rw [Category.assoc, restrictedApproxHom_inclusion, Category.assoc]

/-- The approximation itself preserves every independent carrier family V. -/
theorem approximation_preserves {X : TopCat.{0}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set X) {n : ℕ}
    {f : coeff ⟶ (chains X).X n} (hf : f ∈ supported X V n) :
    f ≫ (singularSmallApprox coeff U).f n ∈ supported X V n := by
  cases n with
  | zero =>
    rw [singularSmallApprox_f, Homotopy.dNext_zero_chainComplex,
      Homotopy.prevD_chainComplex, zero_add, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc]
    exact (supported X V 0).sub_mem hf
      (boundary_preserves V (approximationPrism_preserves U V hf))
  | succ n =>
    rw [singularSmallApprox_f, Homotopy.dNext_succ_chainComplex,
      Homotopy.prevD_chainComplex, Preadditive.comp_sub, Category.comp_id,
      Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
    exact (supported X V (n + 1)).sub_mem hf ((supported X V (n + 1)).add_mem
      (approximationPrism_preserves U V (boundary_preserves V hf))
      (boundary_preserves V (approximationPrism_preserves U V hf)))

def parentFamily {X : TopCat.{0}} {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) : PUnit → Set X :=
  fun _ => Set.range (X.toSSetObjEquiv _ σ)

theorem simplex_parent {X : TopCat.{0}} {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ∈ supported X (parentFamily σ) n := by
  have hs : σ ∈ (X.smallSingularSubcomplex (parentFamily σ)).obj (Opposite.op ⦋n⦌) := by
    exact (TopCat.mem_smallSingularSubcomplex_iff X (parentFamily σ) σ).mpr
      ⟨PUnit.unit, Set.Subset.rfl⟩
  exact TauCeti.ιChainComplex_mem_smallSingularChains
    (R := coeff) (U := parentFamily σ) ⟨σ, hs⟩

/-- Every simplex in the approximation prism stays in its original parent image,
even when a different family U determines the subdivision depth. -/
theorem approximationPrism_parent {X : TopCat.{0}} {ι : Type*} (U : ι → Set X)
    {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ singularSmallApproxHom coeff U n (n + 1) ∈
      supported X (parentFamily σ) (n + 1) :=
  approximationPrism_preserves U (parentFamily σ) (simplex_parent σ)

theorem approximation_parent {X : TopCat.{0}} {ι : Type*} (U : ι → Set X)
    {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (singularSmallApprox coeff U).f n ∈
      supported X (parentFamily σ) n :=
  approximation_preserves U (parentFamily σ) (simplex_parent σ)

theorem subdivision_parent {X : TopCat.{0}} {n : ℕ}
    (σ : TopCat.toSSet.obj X _⦋n⦌) (m : ℕ) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫
      (End.of (singularSubdivisionChainMap coeff X) ^ m).f n ∈
        supported X (parentFamily σ) n :=
  TauCeti.smallSingularChains.comp_singularSubdivisionChainMap_pow_of_le
    (m := 0) (Nat.zero_le m) (by simpa using simplex_parent σ)


end
end Finsler.SmallChainCarrier
