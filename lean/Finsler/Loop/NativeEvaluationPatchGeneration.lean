module

public import Finsler.Loop.NativeThetaRankOne

/-! Actual overlap homology surjects onto either punctured patch.
An elementary biproduct elimination then reduces a full-cover surjection
to one patch, without computing any transition function. -/
@[expose] public section
namespace Finsler.NativeEvaluationPatchGeneration
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.MeridianLoopFamily
open Finsler.NativeEvaluationMayerVietoris Finsler.NativeEvaluationOverlapProduct
open Finsler.H1PuncturedRelativeChart
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem alignment_homology {n : ℕ} (P : Sphere n) (k : ℕ) :
    (H1PuncturedPatchHomology.fullDomainHomologyIso P k).hom =
      homologyPushZMod2 (northAlignment P) k := by
  simp only [H1PuncturedPatchHomology.fullDomainHomologyIso,
    H1PuncturedPatchHomology.patchHomologyIso, Iso.trans_hom,
    ContinuousMap.HomotopyEquiv.singularHomologyIso_hom]
  change homologyPushZMod2 _ k ≫ homologyPushZMod2 _ k = homologyPushZMod2 (_ ≫ _) k
  exact ProductHomologyContractiblePatch.push_comp _ _ k

theorem north_surjective {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : ℕ) :
    Function.Surjective (homologyPushZMod2 (northInclusion P) k).hom := by
  let e := NativeEvaluationProductDetection.homology P k
  let a := (H1PuncturedPatchHomology.fullDomainHomologyIso P k).toLinearEquiv
  let p : baseOverlap P := ⟨v₀.val, PathSphereHomologyGap.equator_in_overlap P v₀⟩
  let s := ProductHomologyDetectionTransport.fiberSection (baseOverlap P) (TopCat.of (H1LocalFiber.based P)) p
  intro z
  refine ⟨e.symm ((homologyPushZMod2 s k).hom (a z)), ?_⟩
  apply a.injective
  change (H1PuncturedPatchHomology.fullDomainHomologyIso P k).hom.hom _ = _
  rw [alignment_homology, SplitPairHomologyKernel.push_comp_apply, ← alignment_factor,
    ← SplitPairHomologyKernel.push_comp_apply]
  change (homologyPushZMod2 (fiberProjection P) k).hom
    (e (e.symm ((homologyPushZMod2 s k).hom (a z)))) = a z
  rw [LinearEquiv.apply_symm_apply]
  change (homologyPushZMod2 (ProductHomologyZeroDetection.second _ _) k).hom
    ((homologyPushZMod2 s k).hom (a z)) = a z
  rw [SplitPairHomologyKernel.push_comp_apply, ProductHomologyDetectionTransport.fiberSection_second,
    SplitPairHomologyKernel.push_id_apply]

theorem right_surjective {A B O H : ModuleCat.{0} (ZMod 2)}
    (g : O ⟶ A ⊞ B) (f : A ⊞ B ⟶ H) (hgf : g ≫ f = 0)
    (hf : Function.Surjective f.hom) (hg : Function.Surjective (g ≫ biprod.fst).hom) :
    Function.Surjective (biprod.inr ≫ f).hom := by
  intro z
  obtain ⟨w, hw⟩ := hf z
  obtain ⟨o, ho⟩ := hg ((biprod.fst : A ⊞ B ⟶ A).hom w)
  let u := w - g.hom o
  have hu : (biprod.fst : A ⊞ B ⟶ A).hom u = 0 := by
    change (biprod.fst : A ⊞ B ⟶ A).hom (w - g.hom o) = 0
    rw [map_sub, show (biprod.fst : A ⊞ B ⟶ A).hom (g.hom o) = _ from ho, sub_self]
  have he := ConcreteCategory.congr_hom (biprod.total (X := A) (Y := B)) u
  change (biprod.inl : A ⟶ A ⊞ B).hom ((biprod.fst : A ⊞ B ⟶ A).hom u) +
    (biprod.inr : B ⟶ A ⊞ B).hom ((biprod.snd : A ⊞ B ⟶ B).hom u) = u at he
  rw [hu, map_zero, zero_add] at he
  refine ⟨(biprod.snd : A ⊞ B ⟶ B).hom u, ?_⟩
  change f.hom ((biprod.inr : B ⟶ A ⊞ B).hom _) = z
  rw [he]
  change f.hom (w - g.hom o) = z
  rw [map_sub, hw]
  have hz : f.hom (g.hom o) = 0 := (ConcreteCategory.congr_hom hgf o).trans rfl
  rw [hz, sub_zero]

theorem south_generates {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : ℕ)
    (hf : Function.Surjective (fromPatches P k).hom) :
    Function.Surjective (homologyPushZMod2
      (TopCat.ofHom (ContinuousMap.subtypeVal (fullDomain (antipode P)))) k).hom := by
  have hgf : toPatches P k ≫ fromPatches P k = 0 :=
    SSet.mayerVietorisToBiprod_fromBiprod coeff
      ((TopCat.commSq_ofHom_inter (fullDomain P) (fullDomain (antipode P))).map TopCat.toSSet) k
  have hg : Function.Surjective (toPatches P k ≫ biprod.fst).hom := by
    rw [NativeEvaluationProductDetection.toPatches_fst]
    exact north_surjective P v₀ k
  have h := right_surjective (toPatches P k) (fromPatches P k) hgf hf hg
  have he : (biprod.inr : homologyZMod2 (TopCat.of (fullDomain (antipode P))) k ⟶ patches P k) ≫
      fromPatches P k = homologyPushZMod2 (TopCat.ofHom (ContinuousMap.subtypeVal (fullDomain (antipode P)))) k :=
    SSet.inr_mayerVietorisFromBiprod coeff _ _ k
  rw [he] at h
  exact h

end
end Finsler.NativeEvaluationPatchGeneration
