module

public import Finsler.Topology.PairDistanceCover
public import Finsler.Topology.RectangleCarrierFactor

/-! Concrete factorwise distance covers make one supported cap adequate
on the whole actual rectangle comparison prism. Far rectangles give zero;
otherwise every parent point lies in the enlarged near tube. -/

@[expose] public section
namespace Finsler.NearFarCapComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology HomologicalComplex SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.PairDistanceCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable {X Y Z : TopCat.{0}} {E : Type*} [PseudoMetricSpace E]
  (b : X → E) (hb : Continuous b) (c : Y → E) (hc : Continuous c) (r : ℝ) (hr : 0 < r)

def far : Set (X ⊗ Y : TopCat.{0}) := {z | r ≤ dist (b z.1) (c z.2)}

def prism (i j : ℕ) (σ : TopCat.toSSet.obj X _⦋i⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌) :
    coeff ⟶ (chains (X ⊗ Y)).X (i + j + 1) :=
  RectangleCarrierFactor.prism (cover b (r / 4)) (cover c (r / 4))
    (cover_open b hb (r / 4)) (cover_univ b (div_pos hr (by norm_num)))
    (cover_open c hc (r / 4)) (cover_univ c (div_pos hr (by norm_num))) i j σ τ

private theorem push_identity (P : TopCat.{0}) : push (𝟙 P) = 𝟙 (chains P) := by
  change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
    (TopCat.toSSet.{0}.map (𝟙 P)) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

theorem cap_factor (i j k t : ℕ) (h : k + t = i + j + 1)
    (σ : (X.smallSingularSubcomplex (cover b (r / 4)) : SSet) _⦋i⦌)
    (τ : (Y.smallSingularSubcomplex (cover c (r / 4)) : SSet) _⦋j⦌)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ Y) k)
    (hφ : cochainPullback (SupportedCap.subspaceMap (X ⊗ Y) (far b c r)) k φ = 0)
    (f : X ⊗ Y ⟶ Z) (B : Set Z)
    (hnear : ∀ x ∈ Set.range (X.toSSetObjEquiv _ σ.val),
      ∀ y ∈ Set.range (Y.toSSetObjEquiv _ τ.val), dist (b x) (c y) < 2 * r → f (x, y) ∈ B) :
    ∃ d : coeff ⟶ (chains (TopCat.of B)).X t,
      d ≫ (push (SupportedCap.subspaceMap Z B)).f t =
        prism b hb c hc r hr i j σ.val τ.val ≫ absoluteChain (X ⊗ Y) k t (i + j + 1) h φ ≫
          (push f).f t := by
  obtain ⟨cx, hx⟩ := (TopCat.mem_smallSingularSubcomplex_iff X (cover b (r / 4)) σ.val).mp σ.property
  obtain ⟨cy, hy⟩ := (TopCat.mem_smallSingularSubcomplex_iff Y (cover c (r / 4)) τ.val).mp τ.property
  rcases near_far_rectangle b c r cx cy with hfar | hclose
  · have hf : ∀ x ∈ Set.range (X.toSSetObjEquiv _ σ.val),
        ∀ y ∈ Set.range (Y.toSSetObjEquiv _ τ.val), (𝟙 (X ⊗ Y)) (x, y) ∈ far b c r := by
      intro x hxs y hys
      exact hfar x (hx hxs) y (hy hys)
    obtain ⟨e, he⟩ := RectangleCarrierFactor.push_factor (cover b (r / 4)) (cover c (r / 4))
      (cover_open b hb (r / 4)) (cover_univ b (div_pos hr (by norm_num)))
      (cover_open c hc (r / 4)) (cover_univ c (div_pos hr (by norm_num)))
      i j σ.val τ.val (𝟙 (X ⊗ Y)) (far b c r) hf
    rw [push_identity, HomologicalComplex.id_f, Category.comp_id] at he
    have hz : prism b hb c hc r hr i j σ.val τ.val ≫ absoluteChain (X ⊗ Y) k t (i + j + 1) h φ = 0 := by
      change RectangleCarrierFactor.prism _ _ _ _ _ _ _ _ _ _ ≫ _ = 0
      have hzero : (push (SupportedCap.subspaceMap (X ⊗ Y) (far b c r))).f (i + j + 1) ≫
          absoluteChain (X ⊗ Y) k t (i + j + 1) h φ = 0 :=
        SupportedCap.cap_zero_on_map (SupportedCap.subspaceMap (X ⊗ Y) (far b c r))
          k t (i + j + 1) h φ hφ
      rw [← he, Category.assoc, hzero, comp_zero]
    refine ⟨0, ?_⟩
    rw [zero_comp, ← Category.assoc, hz, zero_comp]
  · exact RectangleCarrierFactor.cap_push_factor (cover b (r / 4)) (cover c (r / 4))
      (cover_open b hb (r / 4)) (cover_univ b (div_pos hr (by norm_num)))
      (cover_open c hc (r / 4)) (cover_univ c (div_pos hr (by norm_num))) i j σ.val τ.val f B
      (fun x hxs y hys => hnear x hxs y hys (hclose x (hx hxs) y (hy hys))) k t h φ

end
end Finsler.NearFarCapComparison
