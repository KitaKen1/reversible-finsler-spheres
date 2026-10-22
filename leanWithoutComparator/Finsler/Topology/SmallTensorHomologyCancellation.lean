module

public import Finsler.Topology.SmallInclusionHomologyCancellation
public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross

/-! Remove both actual small input refinements on a homology cross
product. The explicit small-chain homology sections suffice; no Kunneth
surjectivity or injectivity of the target inclusion is assumed. -/

@[expose] public section
namespace Finsler.SmallTensorHomologyCancellation

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ v, IsOpen (V v)) (hcV : ⋃ v, V v = Set.univ)

theorem tensor_section (j k : ℕ) :
    (homologyMap (smallSingularRetraction (X := X) coeff U hU hcU) j ⊗ₘ
      homologyMap (smallSingularRetraction (X := Y) coeff V hV hcV) k) ≫
    (homologyMap (inclusion X U) j ⊗ₘ homologyMap (inclusion Y V) k) =
      𝟙 ((chains X).homology j ⊗ (chains Y).homology k) := by
  rw [tensorHom_comp_tensorHom,
    SmallInclusionHomologyCancellation.homology_section X U hU hcU j,
    SmallInclusionHomologyCancellation.homology_section Y V hV hcV k, id_tensorHom_id]

include hU hcU hV hcV

theorem eq_of_pre_inclusions (j k : ℕ) {M : ModuleCat.{0} (ZMod 2)}
    (f g : (chains X).homology j ⊗ (chains Y).homology k ⟶ M)
    (he : (homologyMap (inclusion X U) j ⊗ₘ homologyMap (inclusion Y V) k) ≫ f =
      (homologyMap (inclusion X U) j ⊗ₘ homologyMap (inclusion Y V) k) ≫ g) : f = g := by
  have hh := congrArg (fun h =>
    (homologyMap (smallSingularRetraction (X := X) coeff U hU hcU) j ⊗ₘ
      homologyMap (smallSingularRetraction (X := Y) coeff V hV hcV) k) ≫ h) he
  simpa only [← Category.assoc, tensor_section U V hU hcU hV hcV j k, Category.id_comp] using hh

theorem zero_of_small {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (d : ℕ)
    (f : DegreeLoweringHomology.Map (chains X ⊗ chains Y) E d)
    (g : DegreeLoweringHomology.Map (small X U ⊗ small Y V) E d)
    (j k q : ℕ) (htotal : j + k = d + q)
    (hrestrict : g.homology q = homologyMap (inclusion X U ⊗ₘ inclusion Y V) (d + q) ≫ f.homology q)
    (hsmall : homologyCross (small X U) (small Y V) j k (d + q) htotal ≫ g.homology q = 0) :
    homologyCross (chains X) (chains Y) j k (d + q) htotal ≫ f.homology q = 0 := by
  apply eq_of_pre_inclusions U V hU hcU hV hcV j k _ 0
  rw [comp_zero]
  have hn : (homologyMap (inclusion X U) j ⊗ₘ homologyMap (inclusion Y V) k) ≫
      homologyCross (chains X) (chains Y) j k (d + q) htotal =
      homologyCross (small X U) (small Y V) j k (d + q) htotal ≫
        homologyMap (inclusion X U ⊗ₘ inclusion Y V) (d + q) :=
    HomologicalComplex.homologyCross_naturality (inclusion X U) (inclusion Y V) j k (d + q) htotal
  rw [← Category.assoc, hn, Category.assoc, ← hrestrict, hsmall]

end
end Finsler.SmallTensorHomologyCancellation
