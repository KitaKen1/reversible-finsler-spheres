module

public import Finsler.Loop.SphereProductReducedKernel

/-! The actual second projection is injective strictly below sphere
dimension, with no connectedness assumption on the other factor. -/
@[expose] public section
namespace Finsler.SphereProductBelowDetection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Metric Module
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductReducedKernelStep
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem second_zero_injective (X Y : TopCat.{0}) [PathConnectedSpace X] :
    Function.Injective (homologyPushZMod2 (second X Y) 0).hom := by
  let e := (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) 0).obj coeff).mapIso
    (TopCat.isoOfHomeo (X := product X Y) (Y := product Y X) (Homeomorph.prodComm X Y))).toLinearEquiv
  have he : (TopCat.isoOfHomeo (X := product X Y) (Y := product Y X)
      (Homeomorph.prodComm X Y)).hom ≫ first Y X = second X Y := by ext p : 1; rfl
  intro a b hab
  apply e.injective
  apply first_zero_injective Y X
  change (homologyPushZMod2 (first Y X) 0).hom
    ((homologyPushZMod2 (TopCat.isoOfHomeo (Homeomorph.prodComm X Y)).hom 0).hom a) =
    (homologyPushZMod2 (first Y X) 0).hom
    ((homologyPushZMod2 (TopCat.isoOfHomeo (Homeomorph.prodComm X Y)).hom 0).hom b)
  rw [SplitPairHomologyKernel.push_comp_apply, SplitPairHomologyKernel.push_comp_apply, he]
  exact hab

theorem second_below_injective (n q : ℕ) (hq : q < n) {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (hE : finrank ℝ E = n + 1) (Y : TopCat.{0}) :
    Function.Injective (homologyPushZMod2 (second (TopCat.of (sphere (0 : E) 1)) Y) q).hom := by
  induction q generalizing n E with
  | zero =>
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    have : Fact (finrank ℝ E = n + 1) := ⟨hE⟩
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    have : PathConnectedSpace (sphere (0 : E) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere (by
        rw [← Module.finrank_eq_rank, hE]
        exact_mod_cast (by omega : 1 < n + 1)) 0 zero_le_one)
    exact second_zero_injective _ Y
  | succ q ih =>
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    have : Fact (finrank ℝ E = n + 1) := ⟨hE⟩
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    obtain ⟨p⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
    have : PathConnectedSpace (sphere (0 : E) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere (by
        rw [← Module.finrank_eq_rank, hE]
        exact_mod_cast (by omega : 1 < n + 1)) 0 zero_le_one)
    have : ContractibleSpace ({p}ᶜ : Set (sphere (0 : E) 1)) := TauCeti.contractibleSpace_sphere_compl_singleton p
    have : ContractibleSpace ({-p}ᶜ : Set (sphere (0 : E) 1)) := TauCeti.contractibleSpace_sphere_compl_singleton (-p)
    obtain ⟨f, hf⟩ := step (X := TopCat.of (sphere (0 : E) 1)) (U := {p}ᶜ) (V := {-p}ᶜ)
      Y isOpen_compl_singleton isOpen_compl_singleton (TauCeti.compl_singleton_union_compl_singleton_neg p) q
    obtain ⟨g, hg⟩ := transport (X := TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)))
      (X' := TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)) (TauCeti.equatorHomotopyEquiv p) Y q
    have hO : finrank ℝ (ℝ ∙ (p : E))ᗮ = (n - 1) + 1 := by
      have h : finrank ℝ (ℝ ∙ (p : E))ᗮ = n :=
        Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)
      omega
    have hi := ih (n - 1) (by omega) hO
    intro a b hab
    let z : kernel (TopCat.of (sphere (0 : E) 1)) Y (q + 1) :=
      ⟨a - b, by change _ = 0; rw [map_sub, hab, sub_self]⟩
    have hz : g (f z) = 0 := Subtype.ext (hi ((g (f z)).property.trans (map_zero _).symm))
    have he : z = 0 := hf (hg (hz.trans (by rw [map_zero, map_zero])))
    exact sub_eq_zero.mp (congrArg Subtype.val he)

end
end Finsler.SphereProductBelowDetection
