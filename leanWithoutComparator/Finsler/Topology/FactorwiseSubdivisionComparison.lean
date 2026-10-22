module

public import Finsler.Topology.SmallRectangleCross
public import Finsler.Topology.TensorApproximationHomotopy

/-! Compare actual factorwise subdivision followed by small shuffle cross
with cross followed by actual subdivision of the product. The comparison
is an actual chain homotopy in the product small-chain complex. Further
carrier estimates on its tensor-homotopy components are separate. -/

@[expose] public section
namespace Finsler.FactorwiseSubdivisionComparison

open CategoryTheory MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier TauCeti
open Finsler.SmallRectangleShuffle Finsler.SmallRectangleCross

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ)

include hU hV in
theorem rectangles_open (ij : ι × κ) :
    @IsOpen (X ⊗ Y : TopCat.{0}) (X ⊗ Y : TopCat.{0}).str (rectangles U V ij) := by
  change IsOpen (U ij.1 ×ˢ V ij.2)
  exact (hU ij.1).prod (hV ij.2)

include hcoverU hcoverV in
theorem rectangles_cover : ⋃ ij, rectangles U V ij = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcoverU.symm ▸ Set.mem_univ z.1)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcoverV.symm ▸ Set.mem_univ z.2)
  exact Set.mem_iUnion.mpr ⟨(i, j), hi, hj⟩

def productRetraction : chains (X ⊗ Y) ⟶ small (X ⊗ Y) (rectangles U V) :=
  smallSingularRetraction (X := X ⊗ Y) coeff (rectangles U V) (rectangles_open U V hU hV)
    (rectangles_cover U V hcoverU hcoverV)

def factorwise : chains X ⊗ chains Y ⟶ small (X ⊗ Y) (rectangles U V) :=
  (smallSingularRetraction coeff U hU hcoverU ⊗ₘ
    smallSingularRetraction coeff V hV hcoverV) ≫ cross U V

theorem factorization : factorwise U V hU hcoverU hV hcoverV =
    (singularSmallApprox coeff U ⊗ₘ singularSmallApprox coeff V) ≫
      ambient X Y ≫ productRetraction U V hU hcoverU hV hcoverV := by
  let rx := smallSingularRetraction coeff U hU hcoverU
  let ry := smallSingularRetraction coeff V hV hcoverV
  let rp := productRetraction U V hU hcoverU hV hcoverV
  have hp : inclusion (X ⊗ Y) (rectangles U V) ≫ rp = 𝟙 _ :=
    ι_comp_smallSingularRetraction (X := X ⊗ Y) coeff (rectangles U V)
      (rectangles_open U V hU hV) (rectangles_cover U V hcoverU hcoverV)
  change (rx ⊗ₘ ry) ≫ cross U V = _
  calc
    _ = ((rx ⊗ₘ ry) ≫ cross U V) ≫ (inclusion (X ⊗ Y) (rectangles U V) ≫ rp) := by
      rw [hp, Category.comp_id]
    _ = ((rx ⊗ₘ ry) ≫ (cross U V ≫ inclusion (X ⊗ Y) (rectangles U V))) ≫ rp := by
      simp only [Category.assoc]
    _ = (((rx ⊗ₘ ry) ≫ (inclusion X U ⊗ₘ inclusion Y V)) ≫ ambient X Y) ≫ rp := by
      rw [cross_inclusion]
      simp only [Category.assoc]
    _ = _ := by
      rw [tensorHom_comp_tensorHom]
      change (((smallSingularRetraction coeff U hU hcoverU ≫ inclusion X U) ⊗ₘ
        (smallSingularRetraction coeff V hV hcoverV ≫ inclusion Y V)) ≫ ambient X Y) ≫ rp = _
      rw [smallSingularRetraction_comp_ι, smallSingularRetraction_comp_ι]
      simp only [Category.assoc]
      rfl

def comparison : Homotopy
    (ambient X Y ≫ productRetraction U V hU hcoverU hV hcoverV)
    (factorwise U V hU hcoverU hV hcoverV) :=
  (Homotopy.ofEq (Category.id_comp (ambient X Y ≫ productRetraction U V hU hcoverU hV hcoverV)).symm).trans
    (((TensorApproximationHomotopy.approximation U V).compRight
      (ambient X Y ≫ productRetraction U V hU hcoverU hV hcoverV)).trans
      (Homotopy.ofEq (factorization U V hU hcoverU hV hcoverV).symm))

theorem homology_comparison (n : ℕ) :
    homologyMap (ambient X Y ≫ productRetraction U V hU hcoverU hV hcoverV) n =
      homologyMap (factorwise U V hU hcoverU hV hcoverV) n :=
  (comparison U V hU hcoverU hV hcoverV).homologyMap_eq n

end
end Finsler.FactorwiseSubdivisionComparison
