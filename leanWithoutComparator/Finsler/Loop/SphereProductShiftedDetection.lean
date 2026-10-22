module

public import Finsler.Loop.ProductMayerVietorisVanishing

/-! The actual sphere-product projection detector one degree ABOVE
the sphere dimension, assuming only actual H1(Y)=0. The zero-sphere
case is treated by genuine vanishing, with no connectedness fiction. -/
@[expose] public section
namespace Finsler.SphereProductShiftedDetection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Metric Module
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductHomologyDetectionTransport Finsler.ProductMayerVietorisDetection
open Finsler.ProductMayerVietorisCover Finsler.ProductMayerVietorisVanishing
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem zeroSphere_one_zero {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = 1) (Y : TopCat.{0}) (hY : IsZero (homologyZMod2 Y 1)) :
    IsZero (homologyZMod2 (product (TopCat.of (sphere (0 : E) 1)) Y) 1) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨p⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
  have : Fact (finrank ℝ E = 0 + 1) := ⟨hE⟩
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 0
  have hO : finrank ℝ (ℝ ∙ (p : E))ᗮ = 0 :=
    Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)
  have : Subsingleton (ℝ ∙ (p : E))ᗮ := Module.finrank_zero_iff.mp hO
  have : IsEmpty (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :=
    Set.isEmpty_coe_sort.mpr (sphere_eq_empty_of_subsingleton one_ne_zero)
  have : IsEmpty ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) :=
    ⟨fun u => isEmptyElim (TauCeti.equatorHomotopyEquiv p u)⟩
  have : IsEmpty (overlap (X := TopCat.of (sphere (0 : E) 1)) {p}ᶜ {-p}ᶜ Y) :=
    ⟨fun u => isEmptyElim ((overlapHomeomorph (X := TopCat.of (sphere (0 : E) 1)) {p}ᶜ {-p}ᶜ Y u).1)⟩
  have : ContractibleSpace ({p}ᶜ : Set (sphere (0 : E) 1)) :=
    TauCeti.contractibleSpace_sphere_compl_singleton p
  have : ContractibleSpace ({-p}ᶜ : Set (sphere (0 : E) 1)) :=
    TauCeti.contractibleSpace_sphere_compl_singleton (-p)
  exact zero_of_patch_and_overlap Y isOpen_compl_singleton isOpen_compl_singleton
    (TauCeti.compl_singleton_union_compl_singleton_neg p) 0
    (patch_zero _ Y 1 hY) (patch_zero _ Y 1 hY) (empty_zero _)

theorem detects_shifted (n : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = n + 1) (Y : TopCat.{0}) (hY : IsZero (homologyZMod2 Y 1)) :
    Detects (TopCat.of (sphere (0 : E) 1)) Y (n + 1) := by
  induction n generalizing E with
  | zero =>
    have hs := ModuleCat.subsingleton_of_isZero (zeroSphere_one_zero hE Y hY)
    exact fun _ _ _ => hs.elim _ _
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
    have hd : Detects (TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) Y (n + 1) :=
      detects_of_equiv (TauCeti.equatorHomotopyEquiv p) Y (n + 1)
        (ih (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)))
    exact detects_of_open_cover Y isOpen_compl_singleton isOpen_compl_singleton
      (TauCeti.compl_singleton_union_compl_singleton_neg p) (n + 1) hd

theorem second_shifted_injective (n : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = n + 1) (Y : TopCat.{0}) (hY : IsZero (homologyZMod2 Y 1)) :
    Function.Injective (homologyPushZMod2 (second (TopCat.of (sphere (0 : E) 1)) Y) (n + 1)).hom := by
  have hz : IsZero (homologyZMod2 (TopCat.of (sphere (0 : E) 1)) (n + 1)) :=
    (TauCeti.isZero_reducedSingularHomologyFunctor_sphere_of_ne coeff hE (by omega : n + 1 ≠ n)).of_iso
      ((TauCeti.reducedSingularHomologySuccIso coeff n).app (TopCat.of (sphere (0 : E) 1))).symm
  have hs := ModuleCat.subsingleton_of_isZero hz
  intro a b hab
  apply sub_eq_zero.mp
  apply detects_shifted n hE Y hY (a - b)
  · exact hs.elim _ _
  · rw [map_sub, hab, sub_self]

theorem fiber_section_surjective (n : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = n + 1) (Y : TopCat.{0}) (hY : IsZero (homologyZMod2 Y 1))
    (p : sphere (0 : E) 1) :
    Function.Surjective (homologyPushZMod2
      (ProductHomologyDetectionTransport.fiberSection (TopCat.of (sphere (0 : E) 1)) Y p) (n + 1)).hom := by
  intro z
  refine ⟨(homologyPushZMod2 (second _ Y) (n + 1)).hom z, ?_⟩
  apply second_shifted_injective n hE Y hY
  rw [SplitPairHomologyKernel.push_comp_apply, fiberSection_second, SplitPairHomologyKernel.push_id_apply]

end
end Finsler.SphereProductShiftedDetection
