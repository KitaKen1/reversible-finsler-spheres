module

public import Finsler.Loop.NormalizedCapRightInterval
public import Finsler.Loop.SupportedRightTestLocal
public import Finsler.Loop.SupportedCapIntervalLocal

/-! Exact projection formula for a NORMALIZED spatial left cup factor
and the actual canonical right interval. This reuses the already proved
simplex-by-simplex cap/interval equality; no homology or cycle premise. -/
@[expose] public section
namespace Finsler.IntervalCupLeftProjection
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem interval_cup (X : TopCat.{0}) (p q : ℕ)
    (A : singularCochainGroup (ZMod 2) X p)
    (hA : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) A)
    (T : singularCochainGroup (ZMod 2) (X ⊗ TopCat.I) (q + 1)) :
    TimeTriangleSplit.interval X (p + q) ≫
      CupOne.cup (X ⊗ TopCat.I) p (q + 1) (p + q + 1) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X TopCat.I) p A) T =
      CupOne.cup X p q (p + q) rfl A (TimeTriangleSplit.interval X q ≫ T) := by
  rw [← SupportedRightTestLocal.dual_at_degree, ← Category.assoc, NormalizedCapRightInterval.interval_cap X p q A hA,
    Category.assoc, SupportedRightTestLocal.dual_at_degree]

theorem at_degree (X : TopCat.{0}) (p q N : ℕ) (hN : p + q = N)
    (A : singularCochainGroup (ZMod 2) X p)
    (hA : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) A)
    (T : singularCochainGroup (ZMod 2) (X ⊗ TopCat.I) (q + 1)) :
    TimeTriangleSplit.interval X N ≫
      CupOne.cup (X ⊗ TopCat.I) p (q + 1) (N + 1) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X TopCat.I) p A) T =
      CupOne.cup X p q N hN A (TimeTriangleSplit.interval X q ≫ T) := by
  subst N
  exact interval_cup X p q A hA T

end
end Finsler.IntervalCupLeftProjection
