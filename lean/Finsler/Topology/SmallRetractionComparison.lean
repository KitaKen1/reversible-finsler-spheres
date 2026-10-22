module

public import Finsler.Topology.FilteredFactorwiseComparison

/-! The actual small-chain retractions are natural up to a concrete
chain homotopy taking values in the target small-chain complex itself.
Every closed filtered cap can therefore postcompose this homotopy while
retaining its genuine output sublevel. Strict chain naturality is not used. -/

@[expose] public section
namespace Finsler.SmallRetractionComparison

open CategoryTheory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ)
  (f : X ⟶ Y) (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i)))

def map : small X U ⟶ small Y V :=
  SSet.chainComplexMap (X.smallSingularSubcomplexMap U V f r hf) coeff

theorem map_inclusion : map U V f r hf ≫ inclusion Y V = inclusion X U ≫ push f := by
  simpa only [map, inclusion, push, Functor.map_comp] using
    congrArg (fun g => SSet.chainComplexMap g coeff)
      (TopCat.smallSingularSubcomplexMap_ι U V f r hf)

theorem factorization :
    smallSingularRetraction coeff U hU hcoverU ≫ map U V f r hf =
      singularSmallApprox coeff U ≫ push f ≫ smallSingularRetraction coeff V hV hcoverV := by
  let rx := smallSingularRetraction coeff U hU hcoverU
  let ry := smallSingularRetraction coeff V hV hcoverV
  have hy : inclusion Y V ≫ ry = 𝟙 _ := ι_comp_smallSingularRetraction coeff V hV hcoverV
  have hx : rx ≫ inclusion X U = singularSmallApprox coeff U := smallSingularRetraction_comp_ι coeff U hU hcoverU
  calc
    _ = (rx ≫ map U V f r hf) ≫ (inclusion Y V ≫ ry) := by rw [hy, Category.comp_id]
    _ = rx ≫ (map U V f r hf ≫ inclusion Y V) ≫ ry := by simp only [Category.assoc]
    _ = rx ≫ (inclusion X U ≫ push f) ≫ ry := by rw [map_inclusion]
    _ = _ := by
      simp only [← Category.assoc]
      rw [hx]

def comparison : Homotopy
    (push f ≫ smallSingularRetraction coeff V hV hcoverV)
    (smallSingularRetraction coeff U hU hcoverU ≫ map U V f r hf) :=
  (Homotopy.ofEq (Category.id_comp (push f ≫ smallSingularRetraction coeff V hV hcoverV)).symm).trans
    (((singularSmallApproxHomotopy coeff U).compRight
      (push f ≫ smallSingularRetraction coeff V hV hcoverV)).trans
      (Homotopy.ofEq (factorization U V hU hcoverU hV hcoverV f r hf).symm))

theorem filtered_boundary (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (k p : ℕ)
    (u : ∀ q, (small Y V).X (k + (p + q)) ⟶ E.X q)
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      (small Y V).d (k + (p + (q + 1))) (k + (p + q)) ≫ u q) (q : ℕ) :
    (chains X).iCycles (k + (p + q)) ≫
      (((push f ≫ smallSingularRetraction coeff V hV hcoverV).f (k + (p + q)) -
        (smallSingularRetraction coeff U hU hcoverU ≫ map U V f r hf).f (k + (p + q))) ≫ u q) =
      ((chains X).iCycles (k + (p + q)) ≫
        (comparison U V hU hcoverU hV hcoverV f r hf).hom (k + (p + q)) (k + (p + q) + 1) ≫ u (q + 1)) ≫ E.d (q + 1) q :=
  FilteredFactorwiseComparison.cap_boundary (comparison U V hU hcoverU hV hcoverV f r hf) k p u hu q

end
end Finsler.SmallRetractionComparison
