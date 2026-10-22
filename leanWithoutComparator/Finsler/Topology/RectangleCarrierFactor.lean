module

public import Finsler.Topology.CarrierSubspaceFactor
public import Finsler.Topology.TensorPrismCarrier
public import Finsler.Topology.SmallCapCarrier

/-! The actual rectangle comparison prism, also after any actual cap,
factors into a specified target subspace whenever the whole original
parent rectangle maps there. The geometric bound remains explicit. -/

@[expose] public section
namespace Finsler.RectangleCarrierFactor

open CategoryTheory MonoidalCategory AlgebraicTopology HomologicalComplex SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SmallRectangleShuffle Finsler.SmallRectangleCross
open Finsler.RelativeCapAssociativity Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {X Y Z : TopCat.{0}} {ι κ : Type*}
  (U : ι → Set X) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ)
  (p q : ℕ) (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋q⦌)

def prism : coeff ⟶ (chains (X ⊗ Y)).X (p + q + 1) :=
  (λ_ coeff).inv ≫ ((TopCat.toSSet.obj X).ιChainComplex σ ⊗ₘ
    (TopCat.toSSet.obj Y).ιChainComplex τ) ≫ ιTensorObj (chains X) (chains Y) p q (p + q) rfl ≫
    (FactorwiseSubdivisionComparison.comparison U V hU hcoverU hV hcoverV).hom (p + q) (p + q + 1) ≫
    (inclusion (X ⊗ Y) (rectangles U V)).f (p + q + 1)

theorem prism_supported : prism U V hU hcoverU hV hcoverV p q σ τ ∈
    supported (X ⊗ Y) (rectangles (parentFamily.{1} σ) (parentFamily.{1} τ)) (p + q + 1) :=
  TensorPrismCarrier.comparison_parent U V hU hcoverU hV hcoverV p q σ τ

variable (f : X ⊗ Y ⟶ Z) (B : Set Z)
  (hf : ∀ x ∈ Set.range (X.toSSetObjEquiv _ σ),
    ∀ y ∈ Set.range (Y.toSSetObjEquiv _ τ), f (x, y) ∈ B)

include hf

private theorem parent_maps : ∀ ij : PUnit.{1} × PUnit.{1},
    Set.MapsTo f (rectangles (parentFamily.{1} σ) (parentFamily.{1} τ) ij) B := by
  intro ij z hz
  exact hf z.1 hz.1 z.2 hz.2

theorem push_factor : ∃ d : coeff ⟶ (chains (TopCat.of B)).X (p + q + 1),
    d ≫ (push (SupportedCap.subspaceMap Z B)).f (p + q + 1) =
      prism U V hU hcoverU hV hcoverV p q σ τ ≫ (push f).f (p + q + 1) :=
  CarrierSubspaceFactor.push_factor (rectangles (parentFamily.{1} σ) (parentFamily.{1} τ)) f B
    (parent_maps p q σ τ f B hf) (prism_supported U V hU hcoverU hV hcoverV p q σ τ)

theorem cap_push_factor (k r : ℕ) (h : k + r = p + q + 1)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ Y) k) :
    ∃ d : coeff ⟶ (chains (TopCat.of B)).X r,
      d ≫ (push (SupportedCap.subspaceMap Z B)).f r =
        prism U V hU hcoverU hV hcoverV p q σ τ ≫
          absoluteChain (X ⊗ Y) k r (p + q + 1) h φ ≫ (push f).f r :=
  CarrierSubspaceFactor.push_factor (rectangles (parentFamily.{1} σ) (parentFamily.{1} τ)) f B
    (parent_maps p q σ τ f B hf)
    (SmallCapCarrier.cap_preserves (rectangles (parentFamily.{1} σ) (parentFamily.{1} τ)) k r (p + q + 1)
      h φ (prism_supported U V hU hcoverU hV hcoverV p q σ τ))

end
end Finsler.RectangleCarrierFactor
