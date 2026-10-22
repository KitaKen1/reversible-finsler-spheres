module

public import Finsler.Loop.ProductReducedKernelBase

/-! Iterated actual Mayer-Vietoris boundaries give an injection
ker(H_(n+q)(S^n x Y) -> H_(n+q)(Y)) -> H_q(Y), including q=0. -/
@[expose] public section
namespace Finsler.SphereProductReducedKernel
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Metric Module
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductReducedKernelStep
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem embedding (n q : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = n + 1) (Y : TopCat.{0}) :
    ∃ f : kernel (TopCat.of (sphere (0 : E) 1)) Y (n + q) →ₗ[ZMod 2] homologyZMod2 Y q,
      Function.Injective f := by
  induction n generalizing E with
  | zero =>
    rw [Nat.zero_add]
    exact ProductReducedKernelBase.zeroSphere q hE Y
  | succ n ih =>
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    obtain ⟨p⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
    have : Fact (finrank ℝ E = (n + 1) + 1) := ⟨hE⟩
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (n + 1)
    have : PathConnectedSpace (sphere (0 : E) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere (by
        rw [← Module.finrank_eq_rank, hE]
        exact_mod_cast (by omega : 1 < n + 1 + 1)) 0 zero_le_one)
    have : ContractibleSpace ({p}ᶜ : Set (sphere (0 : E) 1)) := TauCeti.contractibleSpace_sphere_compl_singleton p
    have : ContractibleSpace ({-p}ᶜ : Set (sphere (0 : E) 1)) := TauCeti.contractibleSpace_sphere_compl_singleton (-p)
    obtain ⟨f, hf⟩ := step (X := TopCat.of (sphere (0 : E) 1)) (U := {p}ᶜ) (V := {-p}ᶜ)
      Y isOpen_compl_singleton isOpen_compl_singleton
      (TauCeti.compl_singleton_union_compl_singleton_neg p) (n + q)
    obtain ⟨g, hg⟩ := transport
      (X := TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)))
      (X' := TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))
      (TauCeti.equatorHomotopyEquiv p) Y (n + q)
    obtain ⟨h, hh⟩ := ih (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p))
    rw [show n + 1 + q = (n + q) + 1 by omega]
    exact ⟨h.comp (g.comp f), hh.comp (hg.comp hf)⟩

theorem embedding_of_equiv {X : TopCat.{0}} (n q : ℕ) {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (hE : finrank ℝ E = n + 1)
    (e : ContinuousMap.HomotopyEquiv X (sphere (0 : E) 1)) (Y : TopCat.{0}) :
    ∃ f : kernel X Y (n + q) →ₗ[ZMod 2] homologyZMod2 Y q, Function.Injective f := by
  obtain ⟨f, hf⟩ := transport (X := X) (X' := TopCat.of (sphere (0 : E) 1)) e Y (n + q)
  obtain ⟨g, hg⟩ := embedding n q hE Y
  exact ⟨g.comp f, hg.comp hf⟩

end
end Finsler.SphereProductReducedKernel
