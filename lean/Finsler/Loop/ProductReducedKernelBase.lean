module

public import Finsler.Loop.ProductReducedKernelStep
public import Finsler.Loop.SphereProductOffsetDetection

/-! The disconnected zero-sphere case: its second-projection kernel
injects into one copy of the fiber homology, also in degree zero. -/
@[expose] public section
namespace Finsler.ProductReducedKernelBase
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Metric Module
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductHomologyDetectionTransport Finsler.ProductMayerVietorisCover
open Finsler.ProductReducedKernelStep
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem patch_second_injective {X : TopCat.{0}} (U : Set X) [ContractibleSpace U]
    (Y : TopCat.{0}) (k : ℕ) : Function.Injective (homologyPushZMod2 (patchSecond U Y) k).hom := by
  let e := (patchHomeomorph U Y).toHomotopyEquiv.trans (contractibleProductEquiv (TopCat.of U) Y)
  have hh : (e.singularHomologyIso coeff k).hom = homologyPushZMod2 (patchSecond U Y) k := by
    rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom]
    rfl
  rw [← hh]
  exact (e.singularHomologyIso coeff k).toLinearEquiv.injective

theorem fromPatches_surjective_of_empty {X : TopCat.{0}} {U V : Set X} (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    [IsEmpty (overlap U V Y)] (k : ℕ) : Function.Surjective (fromPatches U V Y k).hom := by
  cases k with
  | zero =>
    have he : Epi (fromPatches U V Y 0) := TopCat.epi_mayerVietorisFromBiprod_zero
      (X := product X Y) coeff (domain_open Y hU) (domain_open Y hV) (domain_cover Y hUV)
    exact (ModuleCat.epi_iff_surjective _).mp he
  | succ k =>
    have hz : IsZero (homologyZMod2 (overlap U V Y) k) := by
      cases k with
      | zero => exact ProductMayerVietorisVanishing.empty_zero _
      | succ k => exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ (k + 1) coeff _ k.succ_ne_zero
    have hs := ModuleCat.subsingleton_of_isZero hz
    intro z
    exact (ShortComplex.moduleCat_exact_iff _).mp (exact_full Y hU hV hUV k) z (hs.elim _ _)

theorem kernel_embeds_of_surjective {X : TopCat.{0}} (U V : Set X)
    [ContractibleSpace U] [ContractibleSpace V] (Y : TopCat.{0}) (k : ℕ)
    (hs : Function.Surjective (fromPatches U V Y k).hom) :
    ∃ f : kernel X Y k →ₗ[ZMod 2] homologyZMod2 Y k, Function.Injective f := by
  let A := homologyZMod2 (patch U Y) k
  let B := homologyZMod2 (patch V Y) k
  let p := (homologyPushZMod2 (second X Y) k).hom
  let a := (homologyPushZMod2 (patchSecond U Y) k).hom
  let b := (homologyPushZMod2 (patchSecond V Y) k).hom
  obtain ⟨g, hg⟩ := (fromPatches U V Y k).hom.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hs)
  have hN : (biprod.inl : A ⟶ patches U V Y k) ≫ fromPatches U V Y k = homologyPushZMod2 (inclusion U Y) k :=
    SSet.inl_mayerVietorisFromBiprod coeff _ _ k
  have hS : (biprod.inr : B ⟶ patches U V Y k) ≫ fromPatches U V Y k = homologyPushZMod2 (inclusion V Y) k :=
    SSet.inr_mayerVietorisFromBiprod coeff _ _ k
  have hf : fromPatches U V Y k ≫ homologyPushZMod2 (second X Y) k =
      biprod.fst ≫ homologyPushZMod2 (patchSecond U Y) k +
      biprod.snd ≫ homologyPushZMod2 (patchSecond V Y) k := by
    apply biprod.hom_ext'
    · simp only [← Category.assoc, Preadditive.comp_add, biprod.inl_fst,
        biprod.inl_snd, Category.id_comp, zero_comp, add_zero]
      rw [hN, ProductHomologyContractiblePatch.push_comp, inclusion_second]
    · simp only [← Category.assoc, Preadditive.comp_add, biprod.inr_fst,
        biprod.inr_snd, Category.id_comp, zero_comp, zero_add]
      rw [hS, ProductHomologyContractiblePatch.push_comp, inclusion_second]
  let f : kernel X Y k →ₗ[ZMod 2] homologyZMod2 Y k :=
    a.comp ((biprod.fst : A ⊞ B ⟶ A).hom.comp (g.comp (kernel X Y k).subtype))
  refine ⟨f, (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_))⟩
  intro z hz
  let c := g z.val
  have hgc : (fromPatches U V Y k).hom c = z.val := LinearMap.congr_fun hg z.val
  have hn : (biprod.fst : A ⊞ B ⟶ A).hom c = 0 :=
    patch_second_injective U Y k (hz.trans (map_zero a).symm)
  have he := ConcreteCategory.congr_hom hf c
  change p ((fromPatches U V Y k).hom c) =
    a ((biprod.fst : A ⊞ B ⟶ A).hom c) + b ((biprod.snd : A ⊞ B ⟶ B).hom c) at he
  rw [hgc, z.property, hn, map_zero, zero_add] at he
  have hs' : (biprod.snd : A ⊞ B ⟶ B).hom c = 0 :=
    patch_second_injective V Y k (he.symm.trans (map_zero b).symm)
  have hc := ConcreteCategory.congr_hom (biprod.total (X := A) (Y := B)) c
  change (biprod.inl : A ⟶ A ⊞ B).hom ((biprod.fst : A ⊞ B ⟶ A).hom c) +
    (biprod.inr : B ⟶ A ⊞ B).hom ((biprod.snd : A ⊞ B ⟶ B).hom c) = c at hc
  rw [hn, hs', map_zero, map_zero, zero_add] at hc
  apply Subtype.ext
  change z.val = 0
  rw [← hgc, ← hc, map_zero]

theorem zeroSphere (q : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = 1) (Y : TopCat.{0}) :
    ∃ f : kernel (TopCat.of (sphere (0 : E) 1)) Y q →ₗ[ZMod 2] homologyZMod2 Y q,
      Function.Injective f := by
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
  have : ContractibleSpace ({p}ᶜ : Set (sphere (0 : E) 1)) := TauCeti.contractibleSpace_sphere_compl_singleton p
  have : ContractibleSpace ({-p}ᶜ : Set (sphere (0 : E) 1)) := TauCeti.contractibleSpace_sphere_compl_singleton (-p)
  exact kernel_embeds_of_surjective (X := TopCat.of (sphere (0 : E) 1)) {p}ᶜ {-p}ᶜ Y q
    (fromPatches_surjective_of_empty Y isOpen_compl_singleton isOpen_compl_singleton
      (TauCeti.compl_singleton_union_compl_singleton_neg p) q)

end
end Finsler.ProductReducedKernelBase
