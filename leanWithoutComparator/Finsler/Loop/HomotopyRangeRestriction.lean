module

public import Finsler.Topology.TimePrismNaturality

/-! Restrict a genuine homotopy whose WHOLE image lies in a carrier.
Its actual singular prism followed by the carrier inclusion is exactly
the original prism, including both endpoints and source degree zero. -/

@[expose] public section
namespace Finsler.HomotopyRangeRestriction
open CategoryTheory AlgebraicTopology
open Finsler.CochainComparison Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1000000

variable {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
  (U : Set Y) (hU : ∀ z : _root_.unitInterval × X, H z ∈ U)

def start : X ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun x => ⟨f x, (H.apply_zero x) ▸ hU (0, x)⟩,
    f.hom.continuous.subtype_mk _⟩

def finish : X ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun x => ⟨g x, (H.apply_one x) ▸ hU (1, x)⟩,
    g.hom.continuous.subtype_mk _⟩

def restriction : TopCat.Homotopy (start H U hU) (finish H U hU) where
  toFun z := ⟨H z, hU z⟩
  continuous_toFun := H.continuous.subtype_mk _
  map_zero_left x := Subtype.ext (H.apply_zero x)
  map_one_left x := Subtype.ext (H.apply_one x)

theorem include_map : (restriction H U hU).h ≫ SupportedCap.subspaceMap Y U = H.h := by
  ext z : 1
  rfl

theorem include_prism (q : ℕ) :
    ((restriction H U hU).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      (push (SupportedCap.subspaceMap Y U)).f (q + 1) =
        (H.toSSet.chainComplexMap coeff).hom q (q + 1) := by
  rw [TimePrismNaturality.prism_post]
  apply TimePrismNaturality.prism_congr
  exact include_map H U hU

end
end Finsler.HomotopyRangeRestriction
