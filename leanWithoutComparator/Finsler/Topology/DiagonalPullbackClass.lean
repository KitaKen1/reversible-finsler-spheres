module

public import Finsler.Topology.DiagonalPullbackCut

/-! Identify the actual pulled-back diagonal cocycle in the project's
pre-existing cohomology model: its class is f*top + g*top. -/

@[expose] public section

namespace Finsler.DiagonalPullbackClass

open CategoryTheory SphereOddDegree
open Finsler.CochainComparison Finsler.BorelEvaluation Finsler.SphereTopClass
open Finsler.DiagonalCohomology Finsler.DiagonalCocycle Finsler.DiagonalPullbackCut

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem pair_first {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    pairEvaluation f g ≫ prFirst n = f := by
  ext x : 1
  rfl

theorem pair_second {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    pairEvaluation f g ≫ prSecond n = g := by
  ext x : 1
  rfl

theorem cocycle_class {n : ℕ} (hn : 1 ≤ n) {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    CochainClass.classOf (cochainCxZMod2 X) n (cocycle hn f g) (cocycle_closed hn f g) =
      (cohPullback f n).hom (topClass n hn) + (cohPullback g n).hom (topClass n hn) := by
  let m := singularCochainComplexZMod2.map (pairEvaluation f g).op
  have hc := CochainClass.closed_map (cochainCxZMod2 (product n)) m n
    (ambientCocycle n hn) (ambient_closed n hn)
  calc
    _ = CochainClass.classOf (cochainCxZMod2 X) n
        (cochainPullback (pairEvaluation f g) n (ambientCocycle n hn)) hc :=
      CochainClass.classOf_congr (cochainCxZMod2 X) n (cocycle_comparison hn f g)
        (cocycle_closed hn f g) hc
    _ = (cohPullback (pairEvaluation f g) n).hom
        (CochainClass.classOf (cochainCxZMod2 (product n)) n
          (ambientCocycle n hn) (ambient_closed n hn)) :=
      (CochainClass.classOf_map (cochainCxZMod2 (product n)) m n
        (ambientCocycle n hn) (ambient_closed n hn) hc).symm
    _ = (cohPullback (pairEvaluation f g) n).hom (ambientClass n hn) :=
      congrArg _ (ambient_cocycle_class n hn)
    _ = _ := by
      unfold ambientClass
      rw [map_add, ← Cup.pullback_comp, ← Cup.pullback_comp, pair_first, pair_second]

end
end Finsler.DiagonalPullbackClass
