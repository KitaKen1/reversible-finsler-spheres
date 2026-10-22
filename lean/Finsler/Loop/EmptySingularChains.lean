module

public import Finsler.Topology.DegreeLoweringHomology
public import Finsler.Topology.SupportedCapNaturality

/-! Empty actual parameter spaces have zero singular chains and zero
small singular chains in every degree. This supplies real zero branches
for bounded geometric operators, including degree zero. -/

@[expose] public section
namespace Finsler.EmptySingularChains

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

variable (X : TopCat.{0}) [IsEmpty X]

theorem simplex_empty (q : ℕ) : IsEmpty (TopCat.toSSet.obj X _⦋q⦌) := by
  have : IsEmpty (TopCat.toSSet.obj X _⦋0⦌) := ⟨fun σ => isEmptyElim (TopCat.toSSetObj₀Equiv σ)⟩
  exact Function.isEmpty ((TopCat.toSSet.obj X).map (⦋0⦌.const ⦋q⦌ 0).op)

theorem chains_zero (q : ℕ) : IsZero ((chains X).X q) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  have := simplex_empty X q
  exact isEmptyElim σ

theorem small_zero {ι : Type*} (U : ι → Set X) (q : ℕ) : IsZero ((small X U).X q) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex U : SSet)) (R := coeff)
  intro σ
  have := simplex_empty X q
  exact isEmptyElim σ.val

end
end Finsler.EmptySingularChains
