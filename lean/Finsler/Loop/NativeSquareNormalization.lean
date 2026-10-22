module

public import Finsler.Loop.NormalizationPrimitiveNaturality
public import Finsler.Loop.NativeRawTimeSquareBoundary

/-! Remove normalization on the actual shuffle square using four
separate carrier restrictions. The source-boundary correction is
retained; the crossed square is not assumed to be an absolute cycle. -/
@[expose] public section
namespace Finsler.NativeSquareNormalization
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages
open Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

variable (n p : ℕ) (φ : singularCochainGroup (ZMod 2) (source n) (p + 3))
  (hφ : cochainCoboundary (ZMod 2) (source n) (p + 3) φ = 0)
  (hface : ∀ i : Fin 4, cochainPullback
    (SupportedCap.subspaceMap (source n) (NativeRawTimeSquareBoundary.face n i)) (p + 3) φ = 0)

include hface in
theorem primitive_face_zero (i : Fin 4) : cochainPullback
    (SupportedCap.subspaceMap (source n) (NativeRawTimeSquareBoundary.face n i)) (p + 2)
    (SingularNormalization.primitive (source n) (p + 2) φ) = 0 :=
  NormalizationPrimitiveNaturality.primitive_supported _ _ φ (hface i)

include hφ hface in
theorem full_comparison :
    OrderedDoubleCutSquareChain.insertion (Loops n) (p + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap n)).f (p + 3) ≫
        (SingularNormalization.normalize (source n) (p + 3) φ - φ) =
    (chains (Loops n)).d (p + 1) p ≫ OrderedDoubleCutSquareChain.insertion (Loops n) p ≫
      (push (NativeRawTimeSquareBoundary.squareMap n)).f (p + 2) ≫
        SingularNormalization.primitive (source n) (p + 2) φ := by
  rw [← SingularNormalization.primitive_boundary (source n) (p + 2) φ hφ]
  exact NativeRawTimeSquareBoundary.full_boundary_evaluation n p _ (primitive_face_zero n p φ hface)

include hφ hface in
theorem cycle_values_eq (c : coeff ⟶ (chains (Loops n)).X (p + 1))
    (hc : c ≫ (chains (Loops n)).d (p + 1) p = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops n) (p + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap n)).f (p + 3) ≫
        SingularNormalization.normalize (source n) (p + 3) φ =
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops n) (p + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap n)).f (p + 3) ≫ φ := by
  have h := congrArg (fun T => c ≫ T) (full_comparison n p φ hφ hface)
  rw [← Category.assoc c ((chains (Loops n)).d (p + 1) p), hc, zero_comp] at h
  simp only [Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h

end
end Finsler.NativeSquareNormalization
