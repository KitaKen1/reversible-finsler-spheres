module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Tactic.Abel

/-! Verification of the proposed cut–join filling witness.
The construction and support of the chains are separate, still unproved inputs. -/

@[expose] public section

namespace Finsler.Filling

variable {C : Type*} [AddCommGroup C]

/-- Once the four boundary formulas are established, their prescribed sum fills x.
The letters a, b, c denote the three product terms that cancel in characteristic two. -/
theorem boundary_witness (d : C →+ C) (h2 : ∀ z : C, z + z = 0)
    (W V H U x a b c : C)
    (hW : d W = a) (hV : d V = b + c)
    (hH : d H = a + b) (hU : d U = c + x) :
    d (W + V + H + U) = x := by
  rw [map_add, map_add, map_add, hW, hV, hH, hU]
  calc
    a + (b + c) + (a + b) + (c + x) =
        (a + a) + (b + b) + (c + c) + x := by abel
    _ = x := by simp [h2]

/-- The relative projection kills the distinguished subcomplex. -/
theorem projection_kills {D : Type*} [AddCommGroup D]
    (i : D →+ C) (ev : C →+ D) (h : ∀ y, ev (i y) = y) (y : D) :
    i y - i (ev (i y)) = 0 := by rw [h, sub_self]

end Finsler.Filling
