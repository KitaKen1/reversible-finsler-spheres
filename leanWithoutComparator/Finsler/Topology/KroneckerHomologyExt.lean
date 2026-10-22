module

public import Finsler.Topology.Kronecker
public import Finsler.Topology.PoolCap
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Actual F₂ cohomology separates actual homology, with no finiteness premise. -/

@[expose] public section

namespace Finsler.KroneckerHomologyExt

open SphereOddDegree

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem homology_ext (X : TopCat.{0}) (k : ℕ) (x y : homologyZMod2 X k)
    (h : ∀ a : cohomologyZMod2 X k, (kroneckerMap X k).hom a x = (kroneckerMap X k).hom a y) :
    x = y := by
  apply Module.eval_apply_injective (ZMod 2)
  apply LinearMap.ext
  intro φ
  change φ x = φ y
  obtain ⟨a, ha⟩ := kroneckerMap_surjective X k φ
  simpa only [ha] using h a

theorem homology_zero (X : TopCat.{0}) (k : ℕ) (x : homologyZMod2 X k)
    (h : ∀ a : cohomologyZMod2 X k, (kroneckerMap X k).hom a x = 0) : x = 0 := by
  apply homology_ext X k x 0
  intro a
  exact (h a).trans (map_zero _).symm


end
end Finsler.KroneckerHomologyExt
