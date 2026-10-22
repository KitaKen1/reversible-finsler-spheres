module

public import Finsler.Loop.NativeSquareNormalization
public import Finsler.Loop.NativeOrderedSquareInput

/-! Normalize both SAME raw-clock inputs, evaluate their genuine square,
and undo normalization with the actual four-face primitive. The old
normalized clock comparison therefore applies to the unnormalized input. -/
@[expose] public section
namespace Finsler.NativeSquareClockAlignment
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeOriginalClockSquare Finsler.NativeOrderedSquareInput
open Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem prefix_normalized_square :
    cochainPullback (NativeRawTimeSquareBoundary.squareMap (m + 1)) (squareDegree m a b k + 3)
      (SingularNormalization.normalize _ _ (prefixOrdered m hm F a b k E)) =
    cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.leftClock) (squareDegree m a b k + 3)
      (SingularNormalization.normalize _ _ (input m hm F a b k E)) := by
  rw [prefix_input, ← SingularNormalization.normalize_natural, ← pullback_comp, prefix_square]
  rfl

theorem prefix_normalization_values (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.leftClock) (squareDegree m a b k + 3)
        (SingularNormalization.normalize _ _ (input m hm F a b k E)) =
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        prefixOrdered m hm F a b k E := by
  rw [← prefix_normalized_square]
  exact NativeSquareNormalization.cycle_values_eq (m + 1) (squareDegree m a b k)
    (prefixOrdered m hm F a b k E) (prefix_closed m hm F a b k E hE)
    (NativeOrderedSquareInput.prefix_face_zero m hm F a b k E) c hc

theorem suffix_normalized_square :
    cochainPullback (NativeRawTimeSquareBoundary.squareMap (m + 1)) (squareDegree m a b k + 3)
      (SingularNormalization.normalize _ _ (suffixOrdered m hm F a b k E)) =
    cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.rightClock) (squareDegree m a b k + 3)
      (SingularNormalization.normalize _ _ (input m hm F a b k E)) := by
  rw [suffix_input, ← SingularNormalization.normalize_natural, ← pullback_comp, suffix_square]
  rfl

theorem suffix_normalization_values (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.rightClock) (squareDegree m a b k + 3)
        (SingularNormalization.normalize _ _ (input m hm F a b k E)) =
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        suffixOrdered m hm F a b k E := by
  rw [← suffix_normalized_square]
  exact NativeSquareNormalization.cycle_values_eq (m + 1) (squareDegree m a b k)
    (suffixOrdered m hm F a b k E) (suffix_closed m hm F a b k E hE)
    (NativeOrderedSquareInput.suffix_face_zero m hm F a b k E) c hc

theorem ordered_cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        prefixOrdered m hm F a b k E =
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        suffixOrdered m hm F a b k E := by
  rw [← prefix_normalization_values m hm F a b k E hE c hc,
    ← suffix_normalization_values m hm F a b k E hE c hc]
  have hφ : cochainCoboundary (ZMod 2) (Loops (m + 1) ⊗ OrderedDoubleCutTimes.space)
      (squareDegree m a b k + 3) (input m hm F a b k E) = 0 := input_closed m hm F a b k E hE
  exact OrderedClockCycleComparison.cycle_values_equal (Loops (m + 1)) (squareDegree m a b k)
    (input m hm F a b k E) hφ (input_diagonal_map_zero m hm F a b k E) c hc

end
end Finsler.NativeSquareClockAlignment
