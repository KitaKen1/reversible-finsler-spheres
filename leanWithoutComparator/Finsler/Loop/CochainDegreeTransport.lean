module

public import Finsler.Topology.CupUnit
public import Finsler.Topology.SmallChainCarrier

/-! Literal chain-degree equality transports induce the existing
cohomology degree transport, with actual cocycle classes preserved. -/

@[expose] public section
namespace Finsler.CochainDegreeTransport
open CategoryTheory AlgebraicTopology SphereOddDegree
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

def pre (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) X j) : singularCochainGroup (ZMod 2) X i :=
  eqToHom (congrArg (chainCxZMod2 X).X h) ≫ φ

theorem closed (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) X j) (hφ : cochainCoboundary (ZMod 2) X j φ = 0) :
    cochainCoboundary (ZMod 2) X i (pre X h φ) = 0 := by
  subst j
  simpa only [pre, eqToHom_refl, Category.id_comp] using hφ

theorem class_cast (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) X j) (hφ : cochainCoboundary (ZMod 2) X j φ = 0) :
    cocycleClass X i (pre X h φ) (closed X h φ hφ) =
      CupUnit.absoluteCast X h.symm (cocycleClass X j φ hφ) := by
  subst j
  simp only [pre, eqToHom_refl, Category.id_comp, CupUnit.absoluteCast]

end
end Finsler.CochainDegreeTransport
