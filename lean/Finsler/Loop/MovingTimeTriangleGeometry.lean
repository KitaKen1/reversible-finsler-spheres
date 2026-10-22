module

public import Finsler.Loop.UniversalTimeTriangle

/-! A genuine singular triangle with THREE continuous clock functions
on the source. Its three edges are the actual affine clock segments,
including a SOURCE-DEPENDENT intermediate time. The source point is
preserved exactly, so its boundary carrier is retained for later gluing. -/
@[expose] public section
namespace Finsler.MovingTimeTriangleGeometry
open CategoryTheory MonoidalCategory AlgebraicTopology Convexity
open Finsler.CochainComparison Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {X : TopCat.{0}}

def mixClock (a : Fin 3 → (X ⟶ TopCat.I.{0})) : X ⊗ UniversalTimeTriangle.space ⟶ TopCat.I :=
  TopCat.ofHom ⟨fun z => ULift.up ⟨∑ i : Fin 3, z.2.weights i * ((a i z.1).down : ℝ), by
    constructor
    · exact Finset.sum_nonneg (fun i _ => mul_nonneg (z.2.nonneg i) (a i z.1).down.property.1)
    · calc
        _ ≤ ∑ i : Fin 3, z.2.weights i := Finset.sum_le_sum (fun i _ =>
          mul_le_of_le_one_right (z.2.nonneg i) (a i z.1).down.property.2)
        _ = 1 := z.2.total_of_fintype⟩, by
    have ha (i : Fin 3) : Continuous (fun z : X × UniversalTimeTriangle.space => ((a i z.1).down : ℝ)) := by fun_prop
    have hw (i : Fin 3) : Continuous (fun z : X × UniversalTimeTriangle.space => z.2.weights i) :=
      (StdSimplex.continuous_weights_apply ℝ i).comp continuous_snd
    have hc : Continuous (fun z : X × UniversalTimeTriangle.space =>
        ∑ i : Fin 3, z.2.weights i * ((a i z.1).down : ℝ)) :=
      continuous_finsetSum _ (fun i _ => (hw i).mul (ha i))
    fun_prop⟩

def triangleMap (a : Fin 3 → (X ⟶ TopCat.I.{0})) : X ⊗ UniversalTimeTriangle.space ⟶ X ⊗ TopCat.I :=
  TopCat.ofHom ⟨fun z => (z.1, mixClock a z), continuous_fst.prodMk (mixClock a).hom.continuous⟩

def segment (a b : X ⟶ TopCat.I.{0}) : X ⊗ TopCat.I ⟶ X ⊗ TopCat.I :=
  TopCat.ofHom ⟨fun z => (z.1, ULift.up ⟨(1 - (z.2.down : ℝ)) * (a z.1).down + (z.2.down : ℝ) * (b z.1).down, by
    have ht : 0 ≤ 1 - (z.2.down : ℝ) := sub_nonneg.mpr z.2.down.property.2
    constructor
    · exact add_nonneg (mul_nonneg ht (a z.1).down.property.1) (mul_nonneg z.2.down.property.1 (b z.1).down.property.1)
    · have h₀ := mul_le_of_le_one_right ht (a z.1).down.property.2
      have h₁ := mul_le_of_le_one_right z.2.down.property.1 (b z.1).down.property.2
      linarith⟩), by fun_prop⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
theorem edge (a : Fin 3 → (X ⟶ TopCat.I.{0})) (i : Fin 3) :
    (X ◁ UniversalTimeTriangle.edgeMap i) ≫ triangleMap a = segment (a (i.succAbove 0)) (a (i.succAbove 1)) := by
  apply TopCat.ext
  intro z
  apply Prod.ext
  · rfl
  · apply ULift.ext
    apply Subtype.ext
    change (∑ j : Fin 3, (UniversalTimeTriangle.edgeMap i z.2).weights j * ((a j z.1).down : ℝ)) =
      (1 - (z.2.down : ℝ)) * (a (i.succAbove 0) z.1).down + (z.2.down : ℝ) * (a (i.succAbove 1) z.1).down
    have heval : UniversalTimeTriangle.edgeMap i z.2 =
        (StdSimplex.continuousAffineMapMk (fun k : Fin 2 => StdSimplex.single (R := ℝ) (i.succAbove k)))
          (TopCat.stdSimplexHomeomorphI.symm z.2) := rfl
    rw [heval]
    simp only [StdSimplex.continuousAffineMapMk_apply]
    have hv : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide
    fin_cases i <;> norm_num [hv, StdSimplex.weights_affineMapMk_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      Finsupp.single_apply, UniversalTimeTriangle.interval_inverse_weight_zero, UniversalTimeTriangle.interval_inverse_weight_one]

def constantClock (X : TopCat.{0}) (t : TopCat.I.{0}) : X ⟶ TopCat.I := TopCat.ofHom ⟨fun _ => t, continuous_const⟩

theorem full_segment (X : TopCat.{0}) : segment (constantClock X 0) (constantClock X 1) = 𝟙 (X ⊗ TopCat.I) := by
  apply TopCat.ext
  intro z
  apply Prod.ext
  · rfl
  · apply ULift.ext
    apply Subtype.ext
    change (1 - (z.2.down : ℝ)) * 0 + (z.2.down : ℝ) * 1 = (z.2.down : ℝ)
    ring

end
end Finsler.MovingTimeTriangleGeometry
