module

public import Finsler.Loop.ProductMayerVietorisDetection
public import TauCeti.AlgebraicTopology.Singular.Sphere

/-! In the sphere dimension, the TWO ACTUAL projections on S^n times
a path-connected space jointly detect homology. Induct on the sphere
dimension using actual punctured opens and the actual equator homotopy
equivalence; do not assume any Kunneth decomposition. -/
@[expose] public section
namespace Finsler.SphereProductHomologyDetection
open CategoryTheory AlgebraicTopology SphereOddDegree Metric Module
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductHomologyDetectionTransport Finsler.ProductMayerVietorisDetection
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem detects_sphere (n : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = n + 1) (Y : TopCat.{0}) [PathConnectedSpace Y] :
    Detects (TopCat.of (sphere (0 : E) 1)) Y n := by
  induction n generalizing E with
  | zero => exact detects_zero _ Y
  | succ n ih =>
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    obtain ⟨p⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
    have : Fact (finrank ℝ E = (n + 1) + 1) := ⟨hE⟩
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (n + 1)
    have : PathConnectedSpace (sphere (0 : E) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere (by
        rw [← Module.finrank_eq_rank, hE]
        exact_mod_cast (by omega : 1 < n + 1 + 1)) 0 zero_le_one)
    have : ContractibleSpace ({p}ᶜ : Set (sphere (0 : E) 1)) :=
      TauCeti.contractibleSpace_sphere_compl_singleton p
    have : ContractibleSpace ({-p}ᶜ : Set (sphere (0 : E) 1)) :=
      TauCeti.contractibleSpace_sphere_compl_singleton (-p)
    have hd : Detects (TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) Y n :=
      detects_of_equiv (TauCeti.equatorHomotopyEquiv p) Y n
        (ih (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)))
    exact detects_of_open_cover Y isOpen_compl_singleton isOpen_compl_singleton
      (TauCeti.compl_singleton_union_compl_singleton_neg p) n hd

end
end Finsler.SphereProductHomologyDetection
