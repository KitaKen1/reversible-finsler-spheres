module

public import Finsler.Loop.CupAtDegree

/-! Reorder three actual F2 cohomology factors with explicit degree
transports. This reorders CUP products only; it makes no assertion
about associativity of the singular homology cross product. -/
@[expose] public section
namespace Finsler.CupTripleReorder
open CategoryTheory SphereOddDegree Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem swap_last (X : TopCat.{0}) (p q r upr uqr upq N : ℕ)
    (hpr : p + r = upr) (hqr : q + r = uqr) (hpq : p + q = upq)
    (hL : upr + q = N) (hR : upq + r = N)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) (c : cohomologyZMod2 X r) :
    CupAtDegree.cup X upr q N hL (CupAtDegree.cup X p r upr hpr a c) b =
      CupAtDegree.cup X upq r N hR (CupAtDegree.cup X p q upq hpq a b) c := by
  calc
    _ = CupAtDegree.cup X p uqr N (by omega) a (CupAtDegree.cup X r q uqr (by omega) c b) :=
      CupAtDegree.assoc X p r q upr uqr N hpr (by omega) hL (by omega) a c b
    _ = CupAtDegree.cup X p uqr N (by omega) a (CupAtDegree.cup X q r uqr hqr b c) :=
      congrArg (CupAtDegree.cup X p uqr N (by omega) a) (CupAtDegree.comm X r q uqr (by omega) c b)
    _ = _ := (CupAtDegree.assoc X p q r upq uqr N hpq hqr hR (by omega) a b c).symm

theorem rotate_last (X : TopCat.{0}) (p q r uqr upq N : ℕ)
    (hqr : q + r = uqr) (hpq : p + q = upq) (hL : uqr + p = N) (hR : upq + r = N)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) (c : cohomologyZMod2 X r) :
    CupAtDegree.cup X uqr p N hL (CupAtDegree.cup X q r uqr hqr b c) a =
      CupAtDegree.cup X upq r N hR (CupAtDegree.cup X p q upq hpq a b) c :=
  (CupAtDegree.comm X uqr p N hL (CupAtDegree.cup X q r uqr hqr b c) a).trans
    (CupAtDegree.assoc X p q r upq uqr N hpq hqr hR (by omega) a b c).symm

end
end Finsler.CupTripleReorder
