module

public import Finsler.Topology.ShuffleBlockDegeneracy
public import Finsler.Topology.SingularNormalization
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-! Connect the dimension argument to the actual AW subintervals and
the existing Dold-Kan normalization. Degenerate cut blocks are killed
by the normalized cochain; degenerate output blocks by the actual
chain projector. This is a simplex-level statement, before the genuine
supported three-cap and factorwise-small-chain integration. -/

@[expose] public section
namespace Finsler.ShuffleBlockNormalization

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.ShuffleBlockDegeneracy
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem block_eq_subinterval {N : ℕ} (a b : ℕ) (h : a + b ≤ N) :
    block a b h = SimplexCategory.subinterval a b h := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  apply Fin.ext
  change a + i.val = i.val + a
  omega

theorem subinterval_cut_or_output_degenerate (j k a b c d : ℕ)
    (htotal : j + k = a + b + c + d) (hdegree : a + c < j)
    (z : (Δ[k] : SSet.{0}) _⦋a + b + c + d⦌) :
    (Δ[k] : SSet.{0}).map (SimplexCategory.subinterval a b (by omega)).op z ∈
        (Δ[k] : SSet.{0}).degenerate b ∨
      (Δ[k] : SSet.{0}).map (SimplexCategory.subinterval (a + b + c) d (by omega)).op z ∈
        (Δ[k] : SSet.{0}).degenerate d := by
  simpa only [face, block_eq_subinterval] using
    cut_or_output_degenerate j k a b c d htotal hdegree z

theorem map_degenerate {K L : SSet.{0}} (f : K ⟶ L) {q : ℕ}
    (z : K _⦋q⦌) (hz : z ∈ K.degenerate q) : f.app _ z ∈ L.degenerate q := by
  obtain ⟨m, hm, θ, τ, hτ⟩ := hz
  refine ⟨m, hm, θ, f.app _ τ, ?_⟩
  rw [← hτ]
  exact (NatTrans.naturality_apply f θ.op τ).symm

theorem degenerate_projector_zero (K : SSet.{0}) {q : ℕ}
    (z : K _⦋q⦌) (hz : z ∈ K.degenerate q) :
    K.ιChainComplex (R := coeff) z ≫
      (DoldKan.PInfty (X := K ⋙ sigmaConst.obj coeff)).f q = 0 := by
  have h := congrArg (fun f => f ≫ (K.fromNormalizedChainComplex coeff).f q)
    (K.ιNormalizedChainComplex_eq_zero (R := coeff) z hz)
  simpa only [SSet.ιNormalizedChainComplex_fromNormalizedChainComplex_f, zero_comp] using h

theorem normalize_simplex_zero (Y : TopCat.{0}) (q : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y q)
    (z : TopCat.toSSet.obj Y _⦋q⦌) (hz : z ∈ (TopCat.toSSet.obj Y).degenerate q) :
    (TopCat.toSSet.obj Y).ιChainComplex z ≫ SingularNormalization.normalize Y q φ = 0 := by
  change (TopCat.toSSet.obj Y).ιChainComplex z ≫
    ((DoldKan.PInfty (X := TopCat.toSSet.obj Y ⋙ sigmaConst.obj coeff)).f q ≫ φ) = 0
  rw [← Category.assoc, degenerate_projector_zero _ z hz, zero_comp]

theorem normalized_cut_or_output_zero (j k a b c d : ℕ)
    (htotal : j + k = a + b + c + d) (hdegree : a + c < j)
    (Y Z : TopCat.{0}) (φ : singularCochainGroup (ZMod 2) Y b)
    (g : (Δ[k] : SSet.{0}) ⟶ TopCat.toSSet.obj Y)
    (f : (Δ[k] : SSet.{0}) ⟶ TopCat.toSSet.obj Z)
    (z : (Δ[k] : SSet.{0}) _⦋a + b + c + d⦌) :
    (TopCat.toSSet.obj Y).ιChainComplex (g.app _
        ((Δ[k] : SSet.{0}).map (SimplexCategory.subinterval a b (by omega)).op z)) ≫
        SingularNormalization.normalize Y b φ = 0 ∨
      (TopCat.toSSet.obj Z).ιChainComplex (f.app _
        ((Δ[k] : SSet.{0}).map
          (SimplexCategory.subinterval (a + b + c) d (by omega)).op z)) ≫
        (SingularNormalization.projector Z).f d = 0 := by
  obtain h | h := subinterval_cut_or_output_degenerate j k a b c d htotal hdegree z
  · exact Or.inl (normalize_simplex_zero Y b φ _ (map_degenerate g _ h))
  · exact Or.inr (degenerate_projector_zero (TopCat.toSSet.obj Z) _ (map_degenerate f _ h))

end
end Finsler.ShuffleBlockNormalization
