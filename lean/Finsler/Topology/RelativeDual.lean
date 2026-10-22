module

public import Finsler.Topology.Relative
public import Finsler.Topology.DualImage
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Dualize Tau Ceti's actual homology sequence over a field.
This uses the dual-of-homology model. RelativeKronecker separately supplies
its natural comparison with actual relative cochain cohomology and transports
the cup pairing. No finite-dimensionality hypothesis is required. -/

@[expose] public section

namespace Finsler.RelativeDual

open CategoryTheory

variable (K : Type) [Field K]

noncomputable section

abbrev relative (P : TopPair.{0}) (n : ℕ) :=
  Module.Dual K ((P.singularHomology (ModuleCat.of K K) n : ModuleCat K) : Type)

abbrev ambient (P : TopPair.{0}) (n : ℕ) :=
  Module.Dual K (((TopPair.toSSetPair.obj P).right.homology
    (ModuleCat.of K K) n : ModuleCat K) : Type)

abbrev fromRelative (P : TopPair.{0}) (n : ℕ) :=
  (P.singularHomologyπ (ModuleCat.of K K) n).hom.dualMap

abbrev restrict (P : TopPair.{0}) (n : ℕ) :=
  (SSet.homologyMap (TopCat.toSSet.map P.map) (ModuleCat.of K K) n).hom.dualMap

/-- Exactness for every actual topological pair in the dual homology model. -/
theorem range_fromRelative (P : TopPair.{0}) (n : ℕ) :
    LinearMap.range (fromRelative K P n) = LinearMap.ker (restrict K P n) := by
  exact Finsler.DualImage.exact_duals _ _
    (P.singularHomology_exact_space (ModuleCat.of K K) n).moduleCat_range_eq_ker

theorem lift_of_restriction_zero (P : TopPair.{0}) (n : ℕ) (φ : ambient K P n)
    (hφ : restrict K P n φ = 0) : ∃ ψ : relative K P n, fromRelative K P n ψ = φ := by
  have hm : φ ∈ LinearMap.range (fromRelative K P n) := by
    rw [range_fromRelative K P n]
    exact hφ
  exact hm

end

end Finsler.RelativeDual
