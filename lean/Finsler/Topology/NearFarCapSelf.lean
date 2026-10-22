module

public import Finsler.Topology.NearFarCapComparison

/-! The concrete near/far comparison inside the source product itself. -/

@[expose] public section
namespace Finsler.NearFarCapSelf

open CategoryTheory AlgebraicTopology HomologicalComplex SphereOddDegree MonoidalCategory
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity Finsler.PairDistanceCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem cap_factor {X Y : TopCat.{0}} {E : Type*} [PseudoMetricSpace E]
    (b : X → E) (hb : Continuous b) (c : Y → E) (hc : Continuous c)
    (r : ℝ) (hr : 0 < r) (B : Set (X ⊗ Y : TopCat.{0}))
    (hnear : ∀ x y, dist (b x) (c y) < 2 * r → (x, y) ∈ B)
    (i j k t : ℕ) (h : k + t = i + j + 1)
    (σ : (X.smallSingularSubcomplex (cover b (r / 4)) : SSet) _⦋i⦌)
    (τ : (Y.smallSingularSubcomplex (cover c (r / 4)) : SSet) _⦋j⦌)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ Y) k)
    (hφ : cochainPullback (SupportedCap.subspaceMap (X ⊗ Y) (NearFarCapComparison.far b c r)) k φ = 0) :
    ∃ d : coeff ⟶ (chains (TopCat.of B)).X t,
      d ≫ (push (SupportedCap.subspaceMap (X ⊗ Y) B)).f t =
        NearFarCapComparison.prism b hb c hc r hr i j σ.val τ.val ≫
          absoluteChain (X ⊗ Y) k t (i + j + 1) h φ := by
  obtain ⟨d, hd⟩ := NearFarCapComparison.cap_factor b hb c hc r hr i j k t h σ τ φ hφ
    (𝟙 (X ⊗ Y)) B (fun x _ y _ hxy => hnear x y hxy)
  have hid : push (𝟙 (X ⊗ Y)) = 𝟙 (chains (X ⊗ Y)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.{0}.map (𝟙 (X ⊗ Y))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, HomologicalComplex.id_f] at hd
  refine ⟨d, hd.trans ?_⟩
  exact congrArg (fun z => NearFarCapComparison.prism b hb c hc r hr i j σ.val τ.val ≫ z)
    (Category.comp_id (absoluteChain (X ⊗ Y) k t (i + j + 1) h φ))

end
end Finsler.NearFarCapSelf
