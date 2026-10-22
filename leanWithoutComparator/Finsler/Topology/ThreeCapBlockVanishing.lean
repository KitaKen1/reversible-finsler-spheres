module

public import Finsler.Topology.ShuffleBlockNormalization
public import Finsler.Topology.SequentialCapWitness

/-! The actual three successive AW caps vanish after output normalization
when the middle cut block or final retained block is killed. The degree
argument supplies this alternative from literal second-factor face
identities. These identities still have to be provided on the genuine
supported partial-cut domain of the factorwise-small product. -/

@[expose] public section
namespace Finsler.ThreeCapBlockVanishing

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SmallCapCarrier CategoryTheory.Preadditive
open Finsler.RelativeCapAssociativity Finsler.ShuffleBlockNormalization
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

def segment (K : SSet.{0}) {N : ℕ} (a b : ℕ) (h : a + b ≤ N) (z : K _⦋N⦌) :
    K _⦋b⦌ := K.map (SimplexCategory.subinterval a b h).op z

def threeCap (X : TopCat.{0}) (a b c d : ℕ)
    (A : singularCochainGroup (ZMod 2) X a)
    (B : singularCochainGroup (ZMod 2) X b)
    (C : singularCochainGroup (ZMod 2) X c) :
    (chains X).X (a + b + c + d) ⟶ (chains X).X d :=
  absoluteChain X a (b + (c + d)) (a + b + c + d) (by omega) A ≫
    absoluteChain X b (c + d) (b + (c + d)) rfl B ≫
      absoluteChain X c d (c + d) rfl C

private theorem cap_post_simplex (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (φ : singularCochainGroup (ZMod 2) X p) (σ : TopCat.toSSet.obj X _⦋N⦌)
    {V : ModuleCat.{0} (ZMod 2)} (f : (chains X).X q ⟶ V) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (absoluteChain X p q N h φ ≫ f) =
      weight X p q N h φ σ ≫
        ((TopCat.toSSet.obj X).ιChainComplex (segment _ p q (by omega) σ) ≫ f) := by
  rw [← Category.assoc, cap_simplex, Category.assoc]
  rfl

theorem three_cap_zero_of_faces (X Z : TopCat.{0}) (r : X ⟶ Z) (a b c d : ℕ)
    (A : singularCochainGroup (ZMod 2) X a)
    (B : singularCochainGroup (ZMod 2) X b)
    (C : singularCochainGroup (ZMod 2) X c)
    (σ : TopCat.toSSet.obj X _⦋a + b + c + d⦌)
    (hzero :
      (TopCat.toSSet.obj X).ιChainComplex
        (segment _ 0 b (by omega) (segment _ a (b + (c + d)) (by omega) σ)) ≫ B = 0 ∨
      (TopCat.toSSet.obj X).ιChainComplex
        (segment _ c d (by omega) (segment _ b (c + d) (by omega)
          (segment _ a (b + (c + d)) (by omega) σ))) ≫
          (push r).f d ≫ (SingularNormalization.projector Z).f d = 0) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ threeCap X a b c d A B C ≫
      (push r).f d ≫ (SingularNormalization.projector Z).f d = 0 := by
  let σ₁ := segment (TopCat.toSSet.obj X) a (b + (c + d)) (by omega) σ
  let σ₂ := segment (TopCat.toSSet.obj X) b (c + d) (by omega) σ₁
  let σ₃ := segment (TopCat.toSSet.obj X) c d (by omega) σ₂
  change (TopCat.toSSet.obj X).ιChainComplex σ ≫
    (absoluteChain X a (b + (c + d)) (a + b + c + d) (by omega) A ≫
      absoluteChain X b (c + d) (b + (c + d)) rfl B ≫
      absoluteChain X c d (c + d) rfl C ≫
      (push r).f d ≫ (SingularNormalization.projector Z).f d) = 0
  rw [cap_post_simplex, cap_post_simplex]
  rcases hzero with hB | hout
  · have hw : weight X b (c + d) (b + (c + d)) rfl B σ₁ = 0 := by
      unfold weight
      change (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv ≫
        (((TopCat.toSSet.obj X).ιChainComplex (segment _ 0 b (by omega) σ₁) ≫ B) ▷
          (𝟙_ (ModuleCat (ZMod 2)))) ≫ (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom = 0
      rw [hB, MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]
    rw [hw, zero_comp, comp_zero]
  · rw [cap_post_simplex]
    change weight X a (b + (c + d)) (a + b + c + d) (by omega) A σ ≫
      (weight X b (c + d) (b + (c + d)) rfl B σ₁ ≫
        (weight X c d (c + d) rfl C σ₂ ≫
          ((TopCat.toSSet.obj X).ιChainComplex σ₃ ≫
            (push r).f d ≫ (SingularNormalization.projector Z).f d))) = 0
    rw [hout, comp_zero, comp_zero, comp_zero]

theorem three_cap_zero_of_degree (X Y Z : TopCat.{0}) (e : X ⟶ Y) (r : X ⟶ Z)
    (j k a b c d : ℕ) (htotal : j + k = a + b + c + d) (hdegree : a + c < j)
    (A : singularCochainGroup (ZMod 2) X a)
    (φ : singularCochainGroup (ZMod 2) Y b)
    (C : singularCochainGroup (ZMod 2) X c)
    (g : (Δ[k] : SSet.{0}) ⟶ TopCat.toSSet.obj Y)
    (f : (Δ[k] : SSet.{0}) ⟶ TopCat.toSSet.obj Z)
    (z : (Δ[k] : SSet.{0}) _⦋a + b + c + d⦌)
    (σ : TopCat.toSSet.obj X _⦋a + b + c + d⦌)
    (hcut : (TopCat.toSSet.map e).app _
      (segment _ 0 b (by omega) (segment _ a (b + (c + d)) (by omega) σ)) =
        g.app _ (segment _ a b (by omega) z))
    (hout : (TopCat.toSSet.map r).app _
      (segment _ c d (by omega) (segment _ b (c + d) (by omega)
        (segment _ a (b + (c + d)) (by omega) σ))) =
        f.app _ (segment _ (a + b + c) d (by omega) z)) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫
      threeCap X a b c d A (cochainPullback e b (SingularNormalization.normalize Y b φ)) C ≫
        (push r).f d ≫ (SingularNormalization.projector Z).f d = 0 := by
  apply three_cap_zero_of_faces
  obtain h | h := normalized_cut_or_output_zero j k a b c d htotal hdegree Y Z φ g f z
  · left
    change (TopCat.toSSet.obj X).ιChainComplex _ ≫
      ((push e).f b ≫ SingularNormalization.normalize Y b φ) = 0
    rw [← Category.assoc, push, SSet.ι_chainComplexMap_f, hcut]
    exact h
  · right
    rw [← Category.assoc, push, SSet.ι_chainComplexMap_f, hout]
    exact h

end
end Finsler.ThreeCapBlockVanishing
