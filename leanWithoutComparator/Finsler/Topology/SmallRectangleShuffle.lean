module

public import Finsler.Topology.SingularChainCross

/-! Factorwise small rectangles have an actual small singular shuffle.
The whole rectangle, and hence all of its shuffle simplices and faces,
is carried by one product-cover member. -/

@[expose] public section
namespace Finsler.SmallRectangleShuffle

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology Convexity
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)

def rectangles : (ι × κ) → Set (X ⊗ Y : TopCat.{0}) := fun ij => U ij.1 ×ˢ V ij.2

def productMap : (X.smallSingularSubcomplex U : SSet) ⊗
    (Y.smallSingularSubcomplex V : SSet) ⟶ TopCat.toSSet.obj (X ⊗ Y) :=
  ((X.smallSingularSubcomplex U).ι ⊗ₘ (Y.smallSingularSubcomplex V).ι) ≫
    Functor.LaxMonoidal.μ TopCat.toSSet X Y

theorem productMap_fst {n : SimplexCategoryᵒᵖ}
    (z : ((X.smallSingularSubcomplex U : SSet) ⊗ (Y.smallSingularSubcomplex V : SSet)).obj n)
    (t : StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (((X ⊗ Y).toSSetObjEquiv n ((productMap U V).app n z)) t).1 =
      (X.toSSetObjEquiv n z.1.val) t := by
  have he := congrArg (fun f : (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) ⟶ TopCat.toSSet.obj X =>
      (X.toSSetObjEquiv n (f.app n (z.1.val, z.2.val))) t)
    (Functor.Monoidal.μ_fst TopCat.toSSet X Y)
  change (X.toSSetObjEquiv n
    ((TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)).app n
      ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n (z.1.val, z.2.val)))) t = _ at he
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at he
  exact he

theorem productMap_snd {n : SimplexCategoryᵒᵖ}
    (z : ((X.smallSingularSubcomplex U : SSet) ⊗ (Y.smallSingularSubcomplex V : SSet)).obj n)
    (t : StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (((X ⊗ Y).toSSetObjEquiv n ((productMap U V).app n z)) t).2 =
      (Y.toSSetObjEquiv n z.2.val) t := by
  have he := congrArg (fun f : (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) ⟶ TopCat.toSSet.obj Y =>
      (Y.toSSetObjEquiv n (f.app n (z.1.val, z.2.val))) t)
    (Functor.Monoidal.μ_snd TopCat.toSSet X Y)
  change (Y.toSSetObjEquiv n
    ((TopCat.toSSet.map (CartesianMonoidalCategory.snd X Y)).app n
      ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n (z.1.val, z.2.val)))) t = _ at he
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at he
  exact he

def productLift : (X.smallSingularSubcomplex U : SSet) ⊗
    (Y.smallSingularSubcomplex V : SSet) ⟶
      ((X ⊗ Y).smallSingularSubcomplex (rectangles U V) : SSet) :=
  SSet.Subcomplex.lift (productMap U V) (by
    rintro n _ ⟨z, rfl⟩
    rw [TopCat.mem_smallSingularSubcomplex_iff]
    obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X U z.1.val).mp z.1.property
    obtain ⟨j, hj⟩ := (TopCat.mem_smallSingularSubcomplex_iff Y V z.2.val).mp z.2.property
    refine ⟨(i, j), ?_⟩
    rintro _ ⟨t, rfl⟩
    exact ⟨hi ⟨t, (productMap_fst U V z t).symm⟩, hj ⟨t, (productMap_snd U V z t).symm⟩⟩)

theorem productLift_inclusion :
    productLift U V ≫ ((X ⊗ Y).smallSingularSubcomplex (rectangles U V)).ι =
      productMap U V :=
  SSet.Subcomplex.lift_ι _ _

def shuffle : small X U ⊗ small Y V ⟶
    ((X ⊗ Y).smallSingularSubcomplex (rectangles U V) : SSet).chainComplex (coeff ⊗ coeff) :=
  SSet.shuffle (X.smallSingularSubcomplex U : SSet) (Y.smallSingularSubcomplex V : SSet)
    coeff coeff ≫ SSet.chainComplexMap (productLift U V) (coeff ⊗ coeff)

theorem shuffle_inclusion :
    shuffle U V ≫ SSet.chainComplexMap
        ((X ⊗ Y).smallSingularSubcomplex (rectangles U V)).ι (coeff ⊗ coeff) =
      (inclusion X U ⊗ₘ inclusion Y V) ≫ TopCat.shuffle X Y coeff coeff := by
  rw [TopCat.shuffle_def]
  unfold shuffle
  rw [Category.assoc, ← Functor.map_comp, productLift_inclusion]
  unfold productMap
  rw [Functor.map_comp, ← Category.assoc]
  simpa only [inclusion, Category.assoc] using (congrArg (fun f => f ≫ SSet.chainComplexMap
      (Functor.LaxMonoidal.μ TopCat.toSSet X Y) (coeff ⊗ coeff))
    (SSet.shuffle_naturality coeff coeff (X.smallSingularSubcomplex U).ι
      (Y.smallSingularSubcomplex V).ι)).symm

end
end Finsler.SmallRectangleShuffle
