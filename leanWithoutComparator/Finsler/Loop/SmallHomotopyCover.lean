module

public import Finsler.Topology.SingularTimeCylinderMaps

/-! A homotopy over a fixed spatial projection preserves the pullback
of every spatial cover for the entire time interval. Construct its
actual simplicial small homotopy and identify its genuine chain prism. -/

@[expose] public section
namespace Finsler.SmallHomotopyCover

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology Convexity
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable {X Y : TopCat.{0}} {f₀ f₁ : X ⟶ Y} (H : TopCat.Homotopy f₀ f₁)
  (j : Y ⟶ X) (hj : H.h ≫ j = CartesianMonoidalCategory.fst X TopCat.I)
  {ι : Type*} (U : ι → Set X)

def cover : ι → Set Y := fun i => j ⁻¹' U i

theorem cover_open (hU : ∀ i, IsOpen (U i)) (i : ι) : IsOpen (cover j U i) :=
  (hU i).preimage j.hom.continuous

theorem cover_univ (hU : ⋃ i, U i = Set.univ) : ⋃ i, cover j U i = Set.univ := by
  simp only [cover, ← Set.preimage_iUnion, hU, Set.preimage_univ]

def rawMap : (X.smallSingularSubcomplex U : SSet) ⊗ (Δ[1] : SSet.{0}) ⟶ TopCat.toSSet.obj Y :=
  ((X.smallSingularSubcomplex U).ι ▷ (Δ[1] : SSet.{0})) ≫ H.toSSet.h

include hj in
theorem spatial_eval (n : SimplexCategoryᵒᵖ)
    (z : ((X.smallSingularSubcomplex U : SSet) ⊗ (Δ[1] : SSet.{0})).obj n)
    (t : StdSimplex ℝ (Fin (n.unop.len + 1))) :
    j (Y.toSSetObjEquiv n ((rawMap H U).app n z) t) = X.toSSetObjEquiv n z.1.val t := by
  rcases z with ⟨σ, s⟩
  change j (Y.toSSetObjEquiv n ((TopCat.toSSet.map H.h).app n
    ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I).app n
      (σ.val, SSet.stdSimplex.toSSetObjI.app n s))) t) = _
  erw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  simp only [ContinuousMap.comp_apply]
  erw [SingularTimeCylinderMaps.mu_eval X TopCat.I n σ.val (SSet.stdSimplex.toSSetObjI.app n s) t]
  exact ConcreteCategory.congr_hom hj
    (X.toSSetObjEquiv n σ.val t, TopCat.I.toSSetObjEquiv n (SSet.stdSimplex.toSSetObjI.app n s) t)

def liftMap : (X.smallSingularSubcomplex U : SSet) ⊗ (Δ[1] : SSet.{0}) ⟶
    (Y.smallSingularSubcomplex (cover j U) : SSet) :=
  SSet.Subcomplex.lift (rawMap H U) (by
    rintro n _ ⟨z, rfl⟩
    apply (TopCat.mem_smallSingularSubcomplex_iff Y (cover j U) _).mpr
    obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X U z.1.val).mp z.1.property
    refine ⟨i, ?_⟩
    rintro _ ⟨t, rfl⟩
    change j (Y.toSSetObjEquiv n ((rawMap H U).app n z) t) ∈ U i
    rw [spatial_eval H j hj U]
    exact hi ⟨t, rfl⟩)

theorem liftMap_inclusion : liftMap H j hj U ≫ (Y.smallSingularSubcomplex (cover j U)).ι = rawMap H U :=
  SSet.Subcomplex.lift_ι _ _

def homotopy : SSet.Homotopy (SSet.ι₀ ≫ liftMap H j hj U) (SSet.ι₁ ≫ liftMap H j hj U) :=
  SimplicialTimeCylinder.cylinderOfMap (liftMap H j hj U)

def prism (q : ℕ) : (small X U).X q ⟶ (small Y (cover j U)).X (q + 1) :=
  ((homotopy H j hj U).chainComplexMap coeff).hom q (q + 1)

theorem prism_inclusion (q : ℕ) :
    (inclusion X U).f q ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1) =
      prism H j hj U q ≫ (inclusion Y (cover j U)).f (q + 1) := by
  exact SSet.Homotopy.chainComplexMap_hom_comm (homotopy H j hj U) H.toSSet
    (liftMap_inclusion H j hj U).symm coeff q (q + 1)

end
end Finsler.SmallHomotopyCover
