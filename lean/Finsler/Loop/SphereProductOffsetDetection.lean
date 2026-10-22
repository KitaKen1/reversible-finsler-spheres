module

public import Finsler.Loop.ProductMayerVietorisVanishing

/-! In EVERY positive offset q+1 above the sphere dimension, an
actual H_(q+1)(Y)=0 hypothesis makes the second projection injective.
Reuse the actual punctured-open Mayer-Vietoris induction and TauCeti
sphere calculations, including the disconnected zero-sphere base. -/
@[expose] public section
namespace Finsler.SphereProductOffsetDetection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Metric Module
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductHomologyDetectionTransport Finsler.ProductMayerVietorisDetection
open Finsler.ProductMayerVietorisCover Finsler.ProductMayerVietorisVanishing
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem zeroSphere_offset_zero (q : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = 1) (Y : TopCat.{0}) (hY : IsZero (homologyZMod2 Y (q + 1))) :
    IsZero (homologyZMod2 (product (TopCat.of (sphere (0 : E) 1)) Y) (q + 1)) := by
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
    (TauCeti.compl_singleton_union_compl_singleton_neg p) q
    (patch_zero _ Y (q + 1) hY) (patch_zero _ Y (q + 1) hY) (by
      cases q with
      | zero => exact empty_zero _
      | succ q => exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ (q + 1) coeff _ q.succ_ne_zero)

theorem detects_offset (n q : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = n + 1) (Y : TopCat.{0}) (hY : IsZero (homologyZMod2 Y (q + 1))) :
    Detects (TopCat.of (sphere (0 : E) 1)) Y (n + (q + 1)) := by
  induction n generalizing E with
  | zero =>
    rw [Nat.zero_add]
    have hs := ModuleCat.subsingleton_of_isZero (zeroSphere_offset_zero q hE Y hY)
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
    have hd : Detects (TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) Y (n + (q + 1)) :=
      detects_of_equiv (TauCeti.equatorHomotopyEquiv p) Y (n + (q + 1))
        (ih (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)))
    rw [show n + 1 + (q + 1) = (n + (q + 1)) + 1 by omega]
    exact detects_of_open_cover Y isOpen_compl_singleton isOpen_compl_singleton
      (TauCeti.compl_singleton_union_compl_singleton_neg p) (n + (q + 1)) hd

theorem second_offset_injective (n q : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = n + 1) (Y : TopCat.{0}) (hY : IsZero (homologyZMod2 Y (q + 1))) :
    Function.Injective (homologyPushZMod2 (second (TopCat.of (sphere (0 : E) 1)) Y) (n + (q + 1))).hom := by
  have hz : IsZero (homologyZMod2 (TopCat.of (sphere (0 : E) 1)) (n + (q + 1))) :=
    by
      have h : IsZero (homologyZMod2 (TopCat.of (sphere (0 : E) 1)) ((n + q) + 1)) :=
        (TauCeti.isZero_reducedSingularHomologyFunctor_sphere_of_ne coeff hE
        (by omega : (n + q) + 1 ≠ n)).of_iso
          ((TauCeti.reducedSingularHomologySuccIso coeff (n + q)).app (TopCat.of (sphere (0 : E) 1))).symm
      simpa only [Nat.add_assoc] using h
  have hs := ModuleCat.subsingleton_of_isZero hz
  intro a b hab
  apply sub_eq_zero.mp
  apply detects_offset n q hE Y hY (a - b)
  · exact hs.elim _ _
  · rw [map_sub, hab, sub_self]

end
end Finsler.SphereProductOffsetDetection
