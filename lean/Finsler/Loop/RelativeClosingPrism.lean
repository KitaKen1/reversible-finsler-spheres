module

public import Finsler.Loop.RelativePrismSweep
public import Finsler.Loop.SelfHomotopySweepNaturality
public import Finsler.Loop.UncappedTimeSplit

/-! Close a REAL partial sweep by a return lying in the ACTUAL
relative subspace. The ORIGINAL interval triangle gives the explicit
comparison boundary; the whole return prism is killed by the real
relative quotient. No return-cancellation or homology equality is
assumed. Valid in every degree, including source degreezero. -/
@[expose] public section
namespace Finsler.RelativeClosingPrism
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {X Y : TopCat.{0}} (B : Set Y) {f g : X ⟶ Y}

abbrev target : TopPair.{0} := RelativePrismSweep.targetPair B

theorem prism_quotient_zero (R : TopCat.Homotopy g f)
    (hR : ∀ z : _root_.unitInterval × X, R z ∈ B) (q : ℕ) :
    (R.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ ((target B).singularChainComplexπ coeff).f (q + 1) = 0 := by
  have he := HomotopyRangeRestriction.include_prism R B hR q
  have hz := congrArg (fun k => k.f (q + 1)) ((target B).chainComplexMap_comp_singularChainComplexπ coeff)
  change (push (SupportedCap.subspaceMap Y B)).f (q + 1) ≫
    ((target B).singularChainComplexπ coeff).f (q + 1) = 0 at hz
  rw [← he, Category.assoc, hz, comp_zero]

theorem carried_homology_zero (R : TopCat.Homotopy g f) (hg : ∀ x, g x ∈ B) (hf : ∀ x, f x ∈ B)
    (hR : ∀ z : _root_.unitInterval × X, R z ∈ B) (q : ℕ) :
    SelfHomotopySweep.homology (RelativePrismSweep.ordinary B R hg hf) q = 0 := by
  have hc : SelfHomotopySweep.component (RelativePrismSweep.ordinary B R hg hf) q = 0 :=
    (RelativePrismSweep.ordinary_component B R hg hf q).trans (prism_quotient_zero B R hR q)
  have hz : SelfHomotopySweep.cycles (RelativePrismSweep.ordinary B R hg hf) q = 0 := by
    apply (cancel_mono (((target B).singularChainComplex coeff).iCycles (q + 1))).mp
    rw [SelfHomotopySweep.cycles_i, hc, comp_zero, zero_comp]
  apply (cancel_epi ((chains X).homologyπ q)).mp
  rw [SelfHomotopySweep.homologyπ_homology, hz, zero_comp, comp_zero]

variable (H : TopCat.Homotopy f f) (K : TopCat.Homotopy f g) (R : TopCat.Homotopy g f)
  (hf : ∀ x, f x ∈ B) (hg : ∀ x, g x ∈ B)
  (hK : UncappedTimeSplit.first H.h = K.h) (hR : UncappedTimeSplit.second H.h = R.h)

def comparison (q : ℕ) : (chains X).X q ⟶ ((target B).singularChainComplex coeff).X (q + 2) :=
  UncappedTimeSplit.comparison H.h q ≫ ((target B).singularChainComplexπ coeff).f (q + 2)

include hK hR in
theorem component_split (q : ℕ) :
    (chains X).iCycles q ≫ SelfHomotopySweep.component (RelativePrismSweep.ordinary B H hf hf) q =
      (chains X).iCycles q ≫ SelfHomotopySweep.component (RelativePrismSweep.ordinary B K hf hg) q +
      (chains X).iCycles q ≫ SelfHomotopySweep.component (RelativePrismSweep.ordinary B R hg hf) q +
      ((chains X).iCycles q ≫ comparison B H q) ≫ ((target B).singularChainComplex coeff).d (q + 2) (q + 1) := by
  have he := congrArg (fun a => a ≫ ((target B).singularChainComplexπ coeff).f (q + 1))
    (UncappedTimeSplit.full_split H.h q)
  rw [hK, hR, UncappedTimeSplit.prism_component H, UncappedTimeSplit.prism_component K,
    UncappedTimeSplit.prism_component R] at he
  simp only [Preadditive.add_comp, Category.assoc] at he
  have hc := ((target B).singularChainComplexπ coeff).comm (q + 2) (q + 1)
  change ((target B).singularChainComplexπ coeff).f (q + 2) ≫
    ((target B).singularChainComplex coeff).d (q + 2) (q + 1) =
      (chains Y).d (q + 2) (q + 1) ≫ ((target B).singularChainComplexπ coeff).f (q + 1) at hc
  rw [← hc] at he
  rw [RelativePrismSweep.ordinary_component, RelativePrismSweep.ordinary_component,
    RelativePrismSweep.ordinary_component]
  simpa only [comparison, Category.assoc] using he

include hK hR in
theorem cycles_split (q : ℕ) :
    SelfHomotopySweep.cycles (RelativePrismSweep.ordinary B H hf hf) q =
      SelfHomotopySweep.cycles (RelativePrismSweep.ordinary B K hf hg) q +
      SelfHomotopySweep.cycles (RelativePrismSweep.ordinary B R hg hf) q +
      ((chains X).iCycles q ≫ comparison B H q) ≫
        ((target B).singularChainComplex coeff).toCycles (q + 2) (q + 1) := by
  apply (cancel_mono (((target B).singularChainComplex coeff).iCycles (q + 1))).mp
  simp only [Preadditive.add_comp, SelfHomotopySweep.cycles_i, Category.assoc, HomologicalComplex.toCycles_i]
  simpa only [Category.assoc] using component_split B H K R hf hg hK hR q

include hK hR in
theorem homology_split (q : ℕ) :
    SelfHomotopySweep.homology (RelativePrismSweep.ordinary B H hf hf) q =
      SelfHomotopySweep.homology (RelativePrismSweep.ordinary B K hf hg) q +
      SelfHomotopySweep.homology (RelativePrismSweep.ordinary B R hg hf) q := by
  apply (cancel_epi ((chains X).homologyπ q)).mp
  rw [Preadditive.comp_add, SelfHomotopySweep.homologyπ_homology,
    SelfHomotopySweep.homologyπ_homology, SelfHomotopySweep.homologyπ_homology, cycles_split B H K R hf hg hK hR]
  simp only [Preadditive.add_comp, Category.assoc, HomologicalComplex.toCycles_comp_homologyπ, comp_zero, add_zero]

include hK hR in
theorem homology_closing (hReturn : ∀ z : _root_.unitInterval × X, R z ∈ B) (q : ℕ) :
    SelfHomotopySweep.homology (RelativePrismSweep.ordinary B K hf hg) q =
      SelfHomotopySweep.homology (RelativePrismSweep.ordinary B H hf hf) q := by
  have he := homology_split B H K R hf hg hK hR q
  rw [carried_homology_zero B R hg hf hReturn q, add_zero] at he
  exact he.symm

theorem full_projection (q : ℕ) :
    SelfHomotopySweep.homology (RelativePrismSweep.ordinary B H hf hf) q =
      SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) q ≫
        HomologicalComplex.homologyMap ((target B).singularChainComplexπ coeff) (q + 1) := by
  have he := SelfHomotopySweepNaturality.homology (H.toSSet.chainComplexMap coeff)
    (RelativePrismSweep.ordinary B H hf hf) (𝟙 (chains X)) ((target B).singularChainComplexπ coeff)
    (fun k => by
      rw [HomologicalComplex.id_f, Category.id_comp]
      exact RelativePrismSweep.ordinary_component B H hf hf k) q
  rw [HomologicalComplex.homologyMap_id, Category.id_comp] at he
  exact he

include hK hR in
theorem closing_projection (hReturn : ∀ z : _root_.unitInterval × X, R z ∈ B) (q : ℕ) :
    SelfHomotopySweep.homology (RelativePrismSweep.ordinary B K hf hg) q =
      SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) q ≫
        HomologicalComplex.homologyMap ((target B).singularChainComplexπ coeff) (q + 1) :=
  (homology_closing B H K R hf hg hK hR hReturn q).trans (full_projection B H hf q)

end
end Finsler.RelativeClosingPrism
