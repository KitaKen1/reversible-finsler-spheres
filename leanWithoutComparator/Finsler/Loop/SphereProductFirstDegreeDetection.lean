module

public import Finsler.Loop.SphereProductHomologyDetection

/-! A low-degree piece needed for the remaining path-space MV gap:
the actual H1 of S^d times a path-connected Y is jointly detected by
its projections for d>=1, and by the second alone for d>=2. -/
@[expose] public section
namespace Finsler.SphereProductFirstDegreeDetection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Metric Module
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductMayerVietorisDetection
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem detects_one (d : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = d + 2) (Y : TopCat.{0}) [PathConnectedSpace Y] :
    Detects (TopCat.of (sphere (0 : E) 1)) Y 1 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  have : Fact (finrank ℝ E = (d + 1) + 1) := ⟨hE⟩
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (d + 1)
  obtain ⟨p⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
  have : PathConnectedSpace (sphere (0 : E) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, hE]
      exact_mod_cast (by omega : 1 < d + 2)) 0 zero_le_one)
  have : ContractibleSpace ({p}ᶜ : Set (sphere (0 : E) 1)) :=
    TauCeti.contractibleSpace_sphere_compl_singleton p
  have : ContractibleSpace ({-p}ᶜ : Set (sphere (0 : E) 1)) :=
    TauCeti.contractibleSpace_sphere_compl_singleton (-p)
  exact detects_of_open_cover Y isOpen_compl_singleton isOpen_compl_singleton
    (TauCeti.compl_singleton_union_compl_singleton_neg p) 0 (detects_zero _ Y)

theorem second_one_injective (d : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = d + 3) (Y : TopCat.{0}) [PathConnectedSpace Y] :
    Function.Injective (homologyPushZMod2 (second (TopCat.of (sphere (0 : E) 1)) Y) 1).hom := by
  have hz : IsZero (homologyZMod2 (TopCat.of (sphere (0 : E) 1)) 1) :=
    (TauCeti.isZero_reducedSingularHomologyFunctor_sphere_of_ne coeff
      (n := d + 2) hE (by omega : 1 ≠ d + 2)).of_iso
        ((TauCeti.reducedSingularHomologySuccIso coeff 0).app (TopCat.of (sphere (0 : E) 1))).symm
  have hs := ModuleCat.subsingleton_of_isZero hz
  intro a b hab
  apply sub_eq_zero.mp
  apply detects_one (d + 1) hE Y (a - b)
  · exact hs.elim _ _
  · rw [map_sub, hab, sub_self]

end
end Finsler.SphereProductFirstDegreeDetection
