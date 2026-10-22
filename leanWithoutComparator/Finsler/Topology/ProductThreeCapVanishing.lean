module

public import Finsler.Topology.ThreeCapBlockVanishing
public import TauCeti.AlgebraicTopology.SimplexCategory.Subinterval

/-! For a genuine map from a product of standard simplices into the cut
domain, factorization of cut evaluation and retained output through the
second factor kills the actual normalized three-cap on every top-degree
chain. In particular it kills Tau Ceti's actual recursive shuffle chain;
no path enumeration or shuffle-support induction is required. Constructing
these product-domain maps for the original supported operation is separate. -/

@[expose] public section
namespace Finsler.ProductThreeCapVanishing

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.ThreeCapBlockVanishing
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem segment_segment (K : SSet.{0}) {N M : ℕ} (i l j : ℕ)
    (h : i + l ≤ M) (h' : j + M ≤ N) (z : K _⦋N⦌) :
    Finsler.ThreeCapBlockVanishing.segment K i l h (Finsler.ThreeCapBlockVanishing.segment K j M h' z) = Finsler.ThreeCapBlockVanishing.segment K (j + i) l (by omega) z := by
  unfold Finsler.ThreeCapBlockVanishing.segment
  rw [← Functor.map_comp_apply, ← op_comp,
    TauCeti.SimplexCategory.subinterval_comp_subinterval i l j (j + i) h h' rfl]

theorem component_zero (X Y Z : TopCat.{0}) (e : X ⟶ Y) (r : X ⟶ Z)
    (j k a b c d : ℕ) (htotal : j + k = a + b + c + d) (hdegree : a + c < j)
    (A : singularCochainGroup (ZMod 2) X a)
    (φ : singularCochainGroup (ZMod 2) Y b)
    (C : singularCochainGroup (ZMod 2) X c)
    (G : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ TopCat.toSSet.obj X)
    (g : (Δ[k] : SSet.{0}) ⟶ TopCat.toSSet.obj Y)
    (f : (Δ[k] : SSet.{0}) ⟶ TopCat.toSSet.obj Z)
    (he : G ≫ TopCat.toSSet.map e = CartesianMonoidalCategory.snd _ _ ≫ g)
    (hr : G ≫ TopCat.toSSet.map r = CartesianMonoidalCategory.snd _ _ ≫ f) :
    (SSet.chainComplexMap G coeff).f (a + b + c + d) ≫
      threeCap X a b c d A (cochainPullback e b (SingularNormalization.normalize Y b φ)) C ≫
        (push r).f d ≫ (SingularNormalization.projector Z).f d = 0 := by
  apply SSet.chainComplex_hom_ext (X := ((Δ[j] : SSet.{0}) ⊗ Δ[k])) (R := coeff)
  intro σ
  rw [SSet.ι_chainComplexMap_f_assoc, comp_zero]
  apply three_cap_zero_of_degree X Y Z e r j k a b c d htotal hdegree A φ C g f σ.2
  · have hface : Finsler.ThreeCapBlockVanishing.segment _ 0 b (by omega)
        (Finsler.ThreeCapBlockVanishing.segment _ a (b + (c + d)) (by omega) (G.app _ σ)) =
        G.app _ (Finsler.ThreeCapBlockVanishing.segment _ a b (by omega) σ) := by
      simp only [segment_segment, Nat.add_zero]
      exact (NatTrans.naturality_apply G
        (SimplexCategory.subinterval a b (by omega)).op σ).symm
    rw [hface]
    have hh := congrArg (fun H => H.app (Opposite.op ⦋b⦌) (Finsler.ThreeCapBlockVanishing.segment _ a b (by omega) σ)) he
    exact hh
  · have hface : Finsler.ThreeCapBlockVanishing.segment _ c d (by omega)
        (Finsler.ThreeCapBlockVanishing.segment _ b (c + d) (by omega)
          (Finsler.ThreeCapBlockVanishing.segment _ a (b + (c + d)) (by omega) (G.app _ σ))) =
        G.app _ (Finsler.ThreeCapBlockVanishing.segment _ (a + b + c) d (by omega) σ) := by
      simp only [segment_segment, Nat.add_assoc]
      exact (NatTrans.naturality_apply G
        (SimplexCategory.subinterval (a + (b + c)) d (by omega)).op σ).symm
    rw [hface]
    have hh := congrArg (fun H => H.app (Opposite.op ⦋d⦌)
      (Finsler.ThreeCapBlockVanishing.segment _ (a + b + c) d (by omega) σ)) hr
    exact hh

theorem shuffle_zero (X Y Z : TopCat.{0}) (e : X ⟶ Y) (r : X ⟶ Z)
    (j k a b c d : ℕ) (htotal : j + k = a + b + c + d) (hdegree : a + c < j)
    (A : singularCochainGroup (ZMod 2) X a)
    (φ : singularCochainGroup (ZMod 2) Y b)
    (C : singularCochainGroup (ZMod 2) X c)
    (G : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ TopCat.toSSet.obj X)
    (g : (Δ[k] : SSet.{0}) ⟶ TopCat.toSSet.obj Y)
    (f : (Δ[k] : SSet.{0}) ⟶ TopCat.toSSet.obj Z)
    (he : G ≫ TopCat.toSSet.map e = CartesianMonoidalCategory.snd _ _ ≫ g)
    (hr : G ≫ TopCat.toSSet.map r = CartesianMonoidalCategory.snd _ _ ≫ f) :
    SSet.shuffleChain coeff j k (a + b + c + d) htotal ≫
      (SSet.chainComplexMap G coeff).f (a + b + c + d) ≫
      threeCap X a b c d A (cochainPullback e b (SingularNormalization.normalize Y b φ)) C ≫
        (push r).f d ≫ (SingularNormalization.projector Z).f d = 0 := by
  rw [component_zero X Y Z e r j k a b c d htotal hdegree A φ C G g f he hr, comp_zero]

end
end Finsler.ProductThreeCapVanishing
