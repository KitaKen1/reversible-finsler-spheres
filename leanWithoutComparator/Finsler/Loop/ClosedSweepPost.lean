module

public import Finsler.Loop.SelfHomotopySweepNaturality
public import Finsler.Topology.SupportedCapNaturality

/-! Postcomposition of an actual closed topological homotopy is
compatible with its genuine degree-one homology sweep. -/
@[expose] public section
namespace Finsler.ClosedSweepPost
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

theorem homology {X Y Z : TopCat.{0}} {f : X ⟶ Y} (H : TopCat.Homotopy f f) (g : Y ⟶ Z) (q : ℕ) :
    SelfHomotopySweep.homology ((TopCat.Homotopy.comp (TopCat.Homotopy.refl g) H).toSSet.chainComplexMap coeff) q =
      SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) q ≫ homologyPushZMod2 g (q + 1) := by
  have he := SelfHomotopySweepNaturality.homology (H.toSSet.chainComplexMap coeff)
    ((TopCat.Homotopy.comp (TopCat.Homotopy.refl g) H).toSSet.chainComplexMap coeff)
    (𝟙 (chains X)) (push g) (fun k => by
      rw [HomologicalComplex.id_f, Category.id_comp]
      exact (TimePrismNaturality.prism_post H g k).symm) q
  rw [HomologicalComplex.homologyMap_id, Category.id_comp] at he
  exact he

end
end Finsler.ClosedSweepPost
