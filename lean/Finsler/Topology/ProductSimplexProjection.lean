module

public import Finsler.Topology.ProductSimplexCarrier

/-! The actual universal product map has the prescribed original second
singular simplex as its second projection, as a simplicial-map identity. -/

@[expose] public section
namespace Finsler.ProductSimplexProjection

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem model_snd (P Q : TopCat.{0}) {j k : ℕ}
    (σ : TopCat.toSSet.obj P _⦋j⦌) (τ : TopCat.toSSet.obj Q _⦋k⦌) :
    ProductSimplexCarrier.model P Q σ τ ≫
      TopCat.toSSet.map (CartesianMonoidalCategory.snd P Q) =
        CartesianMonoidalCategory.snd (Δ[j] : SSet.{0}) Δ[k] ≫ SSet.yonedaEquiv.symm τ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  apply (Q.toSSetObjEquiv n).injective
  apply ContinuousMap.ext
  intro t
  change Q.toSSetObjEquiv n
    ((TopCat.toSSet.map (CartesianMonoidalCategory.snd P Q)).app n
      ((ProductSimplexCarrier.model P Q σ τ).app n z)) t =
        Q.toSSetObjEquiv n ((SSet.yonedaEquiv.symm τ).app n z.2) t
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  exact ProductSimplexCarrier.model_snd P Q σ τ z t

end
end Finsler.ProductSimplexProjection
