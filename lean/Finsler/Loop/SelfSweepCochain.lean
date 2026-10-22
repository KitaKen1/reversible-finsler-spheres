module

public import Finsler.Loop.NativeThetaCoefficientSixQuarters
public import Finsler.Topology.CochainClassExact

/-! The dual of an actual self-homotopy sweep, with explicit source
coboundaries for changes of test. No compatibility with a cut is assumed. -/
@[expose] public section
namespace Finsler.SelfSweepCochain
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable {X Y : TopCat.{0}} {f : X ⟶ Y}
  (H : _root_.Homotopy (SupportedCapNaturality.push f) (SupportedCapNaturality.push f))

def cochain (q : ℕ) (T : singularCochainGroup (ZMod 2) Y (q + 1)) :
    singularCochainGroup (ZMod 2) X q := SelfHomotopySweep.component H q ≫ T

theorem coboundary (q : ℕ) (T : singularCochainGroup (ZMod 2) Y (q + 1)) :
    cochainCoboundary (ZMod 2) X q (cochain H q T) =
      cochain H (q + 1) (cochainCoboundary (ZMod 2) Y (q + 1) T) := by
  change (chains X).d (q + 1) q ≫ (SelfHomotopySweep.component H q ≫ T) =
    SelfHomotopySweep.component H (q + 1) ≫ ((chains Y).d (q + 2) (q + 1) ≫ T)
  rw [← Category.assoc, ← SelfHomotopySweep.boundary_succ, Category.assoc]

theorem closed (q : ℕ) (T : singularCochainGroup (ZMod 2) Y (q + 1))
    (hT : cochainCoboundary (ZMod 2) Y (q + 1) T = 0) :
    cochainCoboundary (ZMod 2) X q (cochain H q T) = 0 := by
  rw [coboundary, hT]
  exact comp_zero

theorem comparison_boundary (q : ℕ) (η : singularCochainGroup (ZMod 2) Y (q + 1))
    (T U : singularCochainGroup (ZMod 2) Y (q + 2))
    (hη : cochainCoboundary (ZMod 2) Y (q + 1) η = T - U) :
    cochainCoboundary (ZMod 2) X q (cochain H q η) = cochain H (q + 1) T - cochain H (q + 1) U := by
  rw [coboundary, hη]
  exact Preadditive.comp_sub _ _ _

theorem comparison_cycle_values (q : ℕ) (η : singularCochainGroup (ZMod 2) Y (q + 1))
    (T U : singularCochainGroup (ZMod 2) Y (q + 2))
    (hη : cochainCoboundary (ZMod 2) Y (q + 1) η = T - U) :
    (chains X).iCycles (q + 1) ≫ cochain H (q + 1) T =
      (chains X).iCycles (q + 1) ≫ cochain H (q + 1) U := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← comparison_boundary H q η T U hη]
  change (chains X).iCycles (q + 1) ≫ ((chains X).d (q + 1) q ≫ cochain H q η) = 0
  rw [← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]

theorem pairing (q : ℕ) (T : singularCochainGroup (ZMod 2) Y (q + 1))
    (hT : cochainCoboundary (ZMod 2) Y (q + 1) T = 0)
    (c : (chains X).cycles q) :
    (kroneckerMap Y (q + 1)).hom (cocycleClass Y (q + 1) T hT)
      ((SelfHomotopySweep.homology H q).hom (((chains X).homologyπ q).hom c)) =
      ((chains X).iCycles q ≫ cochain H q T).hom c := by
  simpa only [cochain, Category.assoc] using NativeThetaCoefficientSixQuarters.sweep_pairing H q T hT c

theorem cohomologous_cycle_values (q : ℕ) (T U : singularCochainGroup (ZMod 2) Y (q + 1))
    (hT : cochainCoboundary (ZMod 2) Y (q + 1) T = 0)
    (hU : cochainCoboundary (ZMod 2) Y (q + 1) U = 0)
    (h : cocycleClass Y (q + 1) T hT = cocycleClass Y (q + 1) U hU) :
    (chains X).iCycles q ≫ cochain H q T = (chains X).iCycles q ≫ cochain H q U := by
  ext c
  rw [← pairing H q T hT c, ← pairing H q U hU c, h]

end
end Finsler.SelfSweepCochain
