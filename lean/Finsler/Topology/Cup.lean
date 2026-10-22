module

public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.CohomologyCupProduct

/-! Verified reuse of Lean Pool's actual F₂ singular cohomology and cup product.
The relative and equivariant module structures used by the Finsler proof are
separate comparisons; this file deals with absolute singular cohomology. -/

@[expose] public section

namespace Finsler.Cup

open CategoryTheory SphereOddDegree

noncomputable section

theorem naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (a : cohomologyZMod2 Y p) (b : cohomologyZMod2 Y q) :
    (cohPullback f (p + q)).hom (cupZMod2 a b) =
      cupZMod2 ((cohPullback f p).hom a) ((cohPullback f q).hom b) :=
  cohPullback_cupZMod2 f p q a b

theorem pullback_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℕ)
    (a : cohomologyZMod2 Z q) :
    (cohPullback (f ≫ g) q).hom a = (cohPullback f q).hom ((cohPullback g q).hom a) := by
  change ((singularCohomologyZMod2 q).map (f ≫ g).op).hom a = _
  rw [op_comp, Functor.map_comp]
  rfl

theorem zero_cup {X : TopCat.{0}} (p q : ℕ) (b : cohomologyZMod2 X q) :
    cupZMod2 (0 : cohomologyZMod2 X p) b = 0 := by
  change (cupHomologyLeft X p q (classRepr X q b) (classRepr_isCocycle X q b)).hom 0 = 0
  exact map_zero _

theorem cup_zero {X : TopCat.{0}} (p q : ℕ) (a : cohomologyZMod2 X p) :
    cupZMod2 a (0 : cohomologyZMod2 X q) = 0 := by
  have h := cupZMod2_mk (classRepr X p a) (classRepr_isCocycle X p a)
    (classRepr X q 0) (classRepr_isCocycle X q 0)
  rw [cocycleClass_classRepr, cocycleClass_classRepr] at h
  have hr := cupHomologyRight_apply X p q (classRepr X p a)
    (classRepr_isCocycle X p a) (classRepr X q 0) (classRepr_isCocycle X q 0)
  rw [cocycleClass_classRepr] at hr
  exact h.trans (hr.symm.trans (map_zero _))

/-- Factoring evaluation through a space where the sphere class pulls back to
zero kills its cup action. The punctured-sphere comparison is still a separate input. -/
theorem evaluation_cup_zero_of_factorization {X P Y : TopCat.{0}}
    (f : X ⟶ P) (g : P ⟶ Y) (p q : ℕ)
    (e : cohomologyZMod2 Y p) (b : cohomologyZMod2 X q)
    (he : (cohPullback g p).hom e = 0) :
    cupZMod2 ((cohPullback (f ≫ g) p).hom e) b = 0 := by
  rw [pullback_comp, he, map_zero, zero_cup]

theorem powers_natural {X Y : TopCat.{0}} (f : X ⟶ Y)
    (a : cohomologyZMod2 Y 1) (n : ℕ) :
    (cohPullback f n).hom (cupPowZMod2 a n) =
      cupPowZMod2 ((cohPullback f 1).hom a) n :=
  cohPullback_cupPowZMod2 f a n

end

end Finsler.Cup
