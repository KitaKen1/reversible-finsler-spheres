module

public import Finsler.Loop.OrthogonalSphereEscape
public import Finsler.Topology.SupportedSelfCut

/-! Compare the actual original self-cut distance with its two-point
coordinate map, before specializing to a strong-H1 native family.
Opaque family maps prevent unnecessary expansion of H1 representatives. -/
@[expose] public section
namespace Finsler.SelfCutDistanceCoordinates
open CategoryTheory Finsler.SphereGeometry Finsler.BorelEvaluation
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 200000

theorem selfEvaluation_distance {n : ℕ} (z : SelfCutThomCocycle.parameters n) :
    ‖((SelfCutThomCocycle.selfEvaluation n z).2 : Ambient n) -
      ((SelfCutThomCocycle.selfEvaluation n z).1 : Ambient n)‖ = SupportedSelfCut.distance n z := rfl

theorem map_distance {n : ℕ} {X Y : TopCat.{0}} (a b : Y ⟶ sphere n)
    (f : X ⟶ Y) (g : X ⟶ SelfCutThomCocycle.parameters n)
    (he : f ≫ OrthogonalSphereEscape.pair a b = g ≫ SelfCutThomCocycle.selfEvaluation n) (z : X) :
    ‖(b (f z) : Ambient n) - (a (f z) : Ambient n)‖ = SupportedSelfCut.distance n (g z) := by
  have hz := ConcreteCategory.congr_hom he z
  change (a (f z), b (f z)) = (H1FiberBase.point (g z).2, H1SelfCutNeighborhood.endpoint (g z)) at hz
  have ha := congrArg Prod.fst hz
  have hb := congrArg Prod.snd hz
  change a (f z) = H1FiberBase.point (g z).2 at ha
  change b (f z) = H1SelfCutNeighborhood.endpoint (g z) at hb
  change ‖(b (f z) : Ambient n) - (a (f z) : Ambient n)‖ =
    ‖(H1SelfCutNeighborhood.endpoint (g z) : Ambient n) - (H1FiberBase.point (g z).2 : Ambient n)‖
  exact congrArg₂ (fun x y : Sphere n => ‖(x : Ambient n) - (y : Ambient n)‖) hb ha

end
end Finsler.SelfCutDistanceCoordinates
