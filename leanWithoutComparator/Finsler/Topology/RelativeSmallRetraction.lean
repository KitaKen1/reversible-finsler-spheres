module

public import Finsler.Topology.SmallRetractionComparison
public import Finsler.Topology.TimeCylinderComparison
import all TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-! The genuine retraction-naturality homotopy vanishes on source small
chains. A time cylinder whose two endpoint maps factor through those
small chains therefore has no input-boundary correction after a closed
filtered cap. The time-cylinder chain itself need not be a cycle. -/

@[expose] public section
namespace Finsler.RelativeSmallRetraction

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ)
  (f : X ⟶ Y) (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i)))

theorem comparison_hom (i j : ℕ) :
    (SmallRetractionComparison.comparison U V hU hcoverU hV hcoverV f r hf).hom i j =
      singularSmallApproxHom coeff U i j ≫ (push f ≫ smallSingularRetraction coeff V hV hcoverV).f j := by
  simp only [SmallRetractionComparison.comparison, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.compRight_hom, singularSmallApproxHomotopy, Pi.zero_apply, zero_add, add_zero]

theorem small_zero (i j : ℕ) :
    (inclusion X U).f i ≫
      (SmallRetractionComparison.comparison U V hU hcoverU hV hcoverV f r hf).hom i j = 0 := by
  have hz : (inclusion X U).f i ≫ singularSmallApproxHom coeff U i j = 0 :=
    ι_comp_singularSmallApproxHom coeff U i j
  rw [comparison_hom, ← Category.assoc, hz, zero_comp]

theorem factor_zero {A : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (e : A ⟶ small X U) (i j : ℕ) :
    (e ≫ inclusion X U).f i ≫
      (SmallRetractionComparison.comparison U V hU hcoverU hV hcoverV f r hf).hom i j = 0 := by
  rw [HomologicalComplex.comp_f, Category.assoc, small_zero, comp_zero]

theorem prism_boundary {A E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {a₀ a₁ : A ⟶ chains X} (H : Homotopy a₀ a₁)
    (e₀ e₁ : A ⟶ small X U) (he₀ : a₀ = e₀ ≫ inclusion X U) (he₁ : a₁ = e₁ ≫ inclusion X U)
    (d : ℕ) (u : ∀ q, (small Y V).X (d + q + 1) ⟶ E.X q)
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      (small Y V).d (d + q + 2) (d + q + 1) ≫ u q) (q : ℕ) :
    (A.iCycles (d + q) ≫ H.hom (d + q) (d + q + 1)) ≫
      (((push f ≫ smallSingularRetraction coeff V hV hcoverV).f (d + q + 1) -
        (smallSingularRetraction coeff U hU hcoverU ≫ SmallRetractionComparison.map U V f r hf).f (d + q + 1)) ≫ u q) =
      (A.iCycles (d + q) ≫ H.hom (d + q) (d + q + 1) ≫
        (SmallRetractionComparison.comparison U V hU hcoverU hV hcoverV f r hf).hom (d + q + 1) (d + q + 2) ≫
        u (q + 1)) ≫ E.d (q + 1) q := by
  have hz₀ (q : ℕ) : a₀.f (d + q) ≫
      ((SmallRetractionComparison.comparison U V hU hcoverU hV hcoverV f r hf).hom (d + q) (d + q + 1) ≫ u q) = 0 := by
    rw [he₀, ← Category.assoc, factor_zero, zero_comp]
  have hz₁ (q : ℕ) : a₁.f (d + q) ≫
      ((SmallRetractionComparison.comparison U V hU hcoverU hV hcoverV f r hf).hom (d + q) (d + q + 1) ≫ u q) = 0 := by
    rw [he₁, ← Category.assoc, factor_zero, zero_comp]
  simpa only [Category.assoc] using TimeCylinderComparison.cycle_boundary H
    (SmallRetractionComparison.comparison U V hU hcoverU hV hcoverV f r hf) d u hu hz₀ hz₁ q

end
end Finsler.RelativeSmallRetraction
