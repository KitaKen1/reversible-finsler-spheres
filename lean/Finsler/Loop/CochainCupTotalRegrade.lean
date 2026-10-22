module

public import Finsler.Loop.CochainInputRegrade
public import Finsler.Loop.CupCapOrder

/-! An explicit native total-degree transport of the actual cup. -/

@[expose] public section
namespace Finsler.CochainCupTotalRegrade

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison

noncomputable section
set_option autoImplicit false

theorem cup (X : TopCat.{0}) (p q d e : ℕ) (hd : p + q = d) (he : p + q = e) (hde : d = e)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    CochainInputRegrade.regrade X d e hde (CupOne.cup X p q e he φ ψ) = CupOne.cup X p q d hd φ ψ := by
  cases hde
  exact CochainInputRegrade.regrade_refl X d _

end
end Finsler.CochainCupTotalRegrade
