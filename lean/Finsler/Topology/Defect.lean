module

public import Finsler.Topology.RegularInterval
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.BigOperators.Finprod

/-! The defect of a cut. For a level a and a degree j, the cokernel of the restriction of global
reflection Borel classes to (t_a, M) measures the classes at the cut which do not come from the
whole loop space. The defect T(a) is the sum over all degrees of the dimensions of these
cokernels. If the restriction from a larger cut b to a is an isomorphism in a degree, the two
cokernels in that degree have the same dimension; hence the defect is the same at the two ends
of an interval carrying a level deformation. This is the statement "T is constant between
critical levels" of the final section, relative to the existence of level deformations, which
is not proved here. -/

@[expose] public section

namespace Finsler.Defect

open Finsler.BorelCochain Finsler.BorelLoop Finsler.Geometry Finsler.RegularInterval

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- The cokernel of the restriction of global reflection Borel classes to the cut a in
degree j. -/
abbrev coker (a : ℝ) (j : ℕ) : Type :=
  HR (levComplex F a) j ⧸ LinearMap.range (HRmap (resHom F a) j)

/-- The defect of the cut a: the sum over all degrees of the dimensions of the cokernels of
global restriction. -/
def defect (a : ℝ) : ℕ := ∑ᶠ j : ℕ, Module.finrank (ZMod 2) (coker F a j)

/-- Restriction to a smaller cut factors through a larger one. -/
theorem cut_res {a b : ℝ} (hab : a ≤ b) (q : ℕ) (y : HR (fullComplex n) q) :
    HRmap (cutHom F hab) q (HRmap (resHom F b) q y) = HRmap (resHom F a) q y := by
  rw [← HRmap_comp]
  exact HRmap_congr (cut_res_f F hab) q y

/-- If restriction from the cut b to the cut a is an isomorphism in degree j, the cokernels of
global restriction at the two cuts have the same dimension in that degree. -/
theorem finrank_coker_eq {a b : ℝ} (hab : a ≤ b) (j : ℕ)
    (hbij : Function.Bijective (HRmap (cutHom F hab) j)) :
    Module.finrank (ZMod 2) (coker F b j) = Module.finrank (ZMod 2) (coker F a j) := by
  let e : HR (levComplex F b) j ≃ₗ[ZMod 2] HR (levComplex F a) j :=
    LinearEquiv.ofBijective (HRmap (cutHom F hab) j) hbij
  have hmap : (LinearMap.range (HRmap (resHom F b) j)).map
      (e : HR (levComplex F b) j →ₗ[ZMod 2] HR (levComplex F a) j) =
      LinearMap.range (HRmap (resHom F a) j) := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, (cut_res F hab j y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨HRmap (resHom F b) j y, ⟨y, rfl⟩, cut_res F hab j y⟩
  exact (Submodule.Quotient.equiv _ _ e hmap).finrank_eq

/-- If restriction from the cut b to the cut a is an isomorphism in all degrees, the two cuts
have the same defect. -/
theorem defect_eq_of_bijective {a b : ℝ} (hab : a ≤ b)
    (hbij : ∀ j, Function.Bijective (HRmap (cutHom F hab) j)) : defect F a = defect F b :=
  finsum_congr fun j => (finrank_coker_eq F hab j (hbij j)).symm

/-- The defect is the same at the two ends of an interval carrying a level deformation. -/
theorem defect_eq_of_levelDeformation {a b : ℝ} (hab : a ≤ b) (D : LevelDeformation F a b b) :
    defect F a = defect F b :=
  defect_eq_of_bijective F hab fun j => cut_bijective_of_levelDeformation F hab D j

end

end Finsler.Defect
