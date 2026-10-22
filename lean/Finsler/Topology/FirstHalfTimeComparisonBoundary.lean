module

public import Finsler.Topology.PrismRefinementHomology
public import Finsler.Topology.FirstHalfBoundedCapDeformation

/-! The sum of the actual relative source-approximation prism and the
actual retained-deformation prism fills the original-to-deformed time
comparison inside the same genuine retained-length target. -/

@[expose] public section
namespace Finsler.FirstHalfTimeComparisonBoundary

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

theorem exists_boundary {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
    {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ)
    (Y : TopCat.{0}) {ι κ : Type*} (U : ι → Set (ClosedInterval × X)) (V : κ → Set Y)
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
    (hV : ∀ j, IsOpen (V j)) (hcV : ⋃ j, V j = Set.univ)
    (f : TopCat.of (ClosedInterval × X) ⟶ Y) (s : ι → κ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (s i))) (d : ℕ)
    (v : ∀ q, (small Y V).X (d + q + 1) ⟶ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).X q)
    (hv : ∀ q, v (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).d (q + 1) q =
      (small Y V).d (d + q + 2) (d + q + 1) ≫ v q)
    (g : DegreeLoweringHomology.Map (chains (TopCat.of X)) (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) d)
    (w : DegreeLoweringHomology.Map (chains (TopCat.of X))
      (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) d)
    (hg : ∀ q, g.component q = AnnularTimeTrim.prism (TopCat.of X) (d + q) ≫
      (push f ≫ TauCeti.smallSingularRetraction (X := Y) coeff V hV hcV).f (d + q + 1) ≫ v q)
    (hw : ∀ q, (w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B))).component q =
      AnnularTimeTrim.prism (TopCat.of X) (d + q) ≫
        (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × (TopCat.of X))) coeff U hU hcU ≫
          SmallRetractionComparison.map (X := TopCat.of (ClosedInterval × (TopCat.of X))) (Y := Y) U V f s hf).f
            (d + q + 1) ≫ v q) (q : ℕ) :
    ∃ W : (small (TopCat.of X) (CommonPrismRefinement.endpointCover (TopCat.of X) U)).cycles (d + q) ⟶
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).X (q + 1),
    (small (TopCat.of X) (CommonPrismRefinement.endpointCover (TopCat.of X) U)).iCycles (d + q) ≫
      (inclusion (TopCat.of X) (CommonPrismRefinement.endpointCover (TopCat.of X) U)).f (d + q) ≫
        (g.component q - (w.post (push (FirstHalfBoundedCapDeformation.endpoint u a ha ha1 hr F B 1))).component q) =
          W ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).d (q + 1) q := by
  let S := CommonPrismRefinement.endpointCover (TopCat.of X) U
  let E := chains (TopCat.of (JoinedFilteredCap.sublevel F B))
  let j := inclusion (TopCat.of X) S
  let W₀ : (small (TopCat.of X) S).cycles (d + q) ⟶ E.X (q + 1) :=
    (small (TopCat.of X) S).iCycles (d + q) ≫ j.f (d + q) ≫ AnnularTimeTrim.prism (TopCat.of X) (d + q) ≫
      (SmallRetractionComparison.comparison (X := TopCat.of (ClosedInterval × (TopCat.of X))) (Y := Y)
        U V hU hcU hV hcV f s hf).hom (d + q + 1) (d + q + 2) ≫ v (q + 1)
  let W₁ : (small (TopCat.of X) S).cycles (d + q) ⟶ E.X (q + 1) :=
    HomologicalComplex.cyclesMap j (d + q) ≫ (chains (TopCat.of X)).iCycles (d + q) ≫ w.component q ≫
      (push (FirstHalfBoundedCapDeformation.toInterior u a ha ha1 hr F B)).f q ≫
        FirstHalfInteriorPrism.prism u a ha ha1 hr F B q
  have he₀ : (small (TopCat.of X) S).iCycles (d + q) ≫ j.f (d + q) ≫
      (g.component q - (w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B))).component q) =
        W₀ ≫ E.d (q + 1) q := by
    have hh := CommonPrismRefinement.filtered_prism_comparison (TopCat.of X) U V hU hcU hV hcV f s hf E d v hv q
    simpa only [hg, hw, Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, W₀, j] using hh
  have he₁ : (small (TopCat.of X) S).iCycles (d + q) ≫ j.f (d + q) ≫
      ((w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B))).component q -
       (w.post (push (FirstHalfBoundedCapDeformation.endpoint u a ha ha1 hr F B 1))).component q) =
        W₁ ≫ E.d (q + 1) q := by
    have hh := congrArg (fun z => HomologicalComplex.cyclesMap j (d + q) ≫ z)
      (FirstHalfBoundedCapDeformation.capped_prism_boundary u a ha ha1 hr F B w q)
    simpa only [Category.assoc, HomologicalComplex.cyclesMap_i_assoc, W₁] using hh
  refine ⟨W₀ + W₁, ?_⟩
  rw [Preadditive.add_comp, ← he₀, ← he₁]
  simp only [Preadditive.comp_sub]
  abel

end
end Finsler.FirstHalfTimeComparisonBoundary
