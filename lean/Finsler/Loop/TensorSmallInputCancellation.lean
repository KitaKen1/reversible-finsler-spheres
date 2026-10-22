module

public import Finsler.Topology.TensorApproximationHomotopy
public import Finsler.Topology.SmallInclusionHomologyCancellation

/-! The tensor of the genuine small inclusions has a homology section
on the entire tensor complex. No Kunneth decomposition is required. -/

@[expose] public section
namespace Finsler.TensorSmallInputCancellation

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology TauCeti
open Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ i, IsOpen (V i)) (hcV : ⋃ i, V i = Set.univ)

theorem homology_section (n : ℕ) :
    homologyMap (smallSingularRetraction (X := X) coeff U hU hcU ⊗ₘ
      smallSingularRetraction (X := Y) coeff V hV hcV) n ≫
      homologyMap (inclusion X U ⊗ₘ inclusion Y V) n = 𝟙 ((chains X ⊗ chains Y).homology n) := by
  rw [← homologyMap_comp, tensorHom_comp_tensorHom,
    smallSingularRetraction_comp_ι, smallSingularRetraction_comp_ι]
  have hh := (TensorApproximationHomotopy.approximation U V).homologyMap_eq n
  simpa only [homologyMap_id] using hh.symm

theorem small_section :
    (inclusion X U ⊗ₘ inclusion Y V) ≫
      (smallSingularRetraction (X := X) coeff U hU hcU ⊗ₘ
        smallSingularRetraction (X := Y) coeff V hV hcV) = 𝟙 (small X U ⊗ small Y V) := by
  rw [tensorHom_comp_tensorHom, ι_comp_smallSingularRetraction,
    ι_comp_smallSingularRetraction, id_tensorHom_id]

include hU hcU hV hcV in
theorem eq_of_pre_inclusion (n : ℕ) {M : ModuleCat.{0} (ZMod 2)}
    (a b : (chains X ⊗ chains Y).homology n ⟶ M)
    (he : homologyMap (inclusion X U ⊗ₘ inclusion Y V) n ≫ a =
      homologyMap (inclusion X U ⊗ₘ inclusion Y V) n ≫ b) : a = b := by
  have hh := congrArg (fun f => homologyMap
    (smallSingularRetraction (X := X) coeff U hU hcU ⊗ₘ
      smallSingularRetraction (X := Y) coeff V hV hcV) n ≫ f) he
  simpa only [← Category.assoc, homology_section U V hU hcU hV hcV n, Category.id_comp] using hh

include hU hcU hV hcV in
theorem homology_eq {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (d : ℕ)
    (a b : DegreeLoweringHomology.Map (chains X ⊗ chains Y) E d) (q : ℕ)
    (he : (a.pre (inclusion X U ⊗ₘ inclusion Y V)).homology q =
      (b.pre (inclusion X U ⊗ₘ inclusion Y V)).homology q) : a.homology q = b.homology q := by
  apply eq_of_pre_inclusion U V hU hcU hV hcV (d + q) _ _
  simpa only [DegreeLoweringHomology.Map.pre_homology] using he

end
end Finsler.TensorSmallInputCancellation
