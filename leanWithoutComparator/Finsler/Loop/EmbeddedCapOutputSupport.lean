module

public import Finsler.Loop.SmallCapSubspaceLift

/-! Actual cap lifts through an embedded proper space into a specified
subspace of that proper space. A bound on the entire nonzero parent is
used; neither cochain closure nor homology monicity is assumed. -/

@[expose] public section
namespace Finsler.EmbeddedCapOutputSupport

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (X Y : TopCat.{0}) (B : Set X) (e : Y ≅ TopCat.of B)

theorem exists_parent (S : Set Y) (k : ℕ) (σ : TopCat.toSSet.obj X _⦋k⦌)
    (hi : Set.range (X.toSSetObjEquiv _ σ) ⊆ SmallCapSubspaceLift.source X Y B e '' S) :
    ∃ τ : TopCat.toSSet.obj Y _⦋k⦌,
      (TopCat.toSSet.map (SmallCapSubspaceLift.source X Y B e)).app (Opposite.op ⦋k⦌) τ = σ ∧
      Set.range (Y.toSSetObjEquiv _ τ) ⊆ S := by
  have hB : Set.range (X.toSSetObjEquiv _ σ) ⊆ B := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hi hz
    exact (e.hom y).property
  let τB := SupportedCap.simplexLift X B σ hB
  let τ := (TopCat.toSSet.map e.inv).app (Opposite.op ⦋k⦌) τB
  have hj : e.inv ≫ SmallCapSubspaceLift.source X Y B e = SupportedCap.subspaceMap X B := by
    dsimp only [SmallCapSubspaceLift.source]
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hτ : (TopCat.toSSet.map (SmallCapSubspaceLift.source X Y B e)).app (Opposite.op ⦋k⦌) τ = σ := by
    change ((TopCat.toSSet.map e.inv ≫ TopCat.toSSet.map (SmallCapSubspaceLift.source X Y B e)).app _ τB) = σ
    rw [← Functor.map_comp, hj]
    exact SupportedCap.simplexLift_image X B σ hB
  have hinj : Function.Injective (SmallCapSubspaceLift.source X Y B e) := by
    intro y z h
    apply (TopCat.mono_iff_injective e.hom).mp inferInstance
    exact Subtype.ext h
  refine ⟨τ, hτ, ?_⟩
  rintro _ ⟨t, rfl⟩
  have he : SmallCapSubspaceLift.source X Y B e (Y.toSSetObjEquiv _ τ t) = X.toSSetObjEquiv _ σ t := by
    have hh := congrArg (fun s => X.toSSetObjEquiv _ s t) hτ
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at hh
    exact hh
  obtain ⟨y, hy, heq⟩ := hi ⟨t, rfl⟩
  rw [hinj (he.trans heq.symm)]
  exact hy

variable (W : Set Y)

def source : TopCat.of W ⟶ X :=
  SupportedCap.subspaceMap Y W ≫ SmallCapSubspaceLift.source X Y B e

theorem source_mono (q : ℕ) : Mono ((push (source X Y B e W)).f q) := by
  haveI : Mono (SupportedCap.subspaceMap X B) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  haveI : Mono (SmallCapSubspaceLift.source X Y B e) := by
    dsimp only [SmallCapSubspaceLift.source]
    infer_instance
  haveI : Mono (SupportedCap.subspaceMap Y W) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  haveI : Mono (source X Y B e W) := by dsimp only [source]; infer_instance
  exact inferInstanceAs (Mono ((sigmaConst.obj coeff).map
    ((TopCat.toSSet.map (source X Y B e W)).app (Opposite.op ⦋q⦌))))

theorem exists_simplex (a q : ℕ) (φ : singularCochainGroup (ZMod 2) X a)
    (σ : TopCat.toSSet.obj X _⦋a + q⦌)
    (hgood : (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a q (a + q) rfl φ ≠ 0 →
      Set.range (X.toSSetObjEquiv _ σ) ⊆ SmallCapSubspaceLift.source X Y B e '' W) :
    ∃ g : coeff ⟶ (chains (TopCat.of W)).X q,
      g ≫ (push (source X Y B e W)).f q =
        (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a q (a + q) rfl φ := by
  classical
  by_cases hz : (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a q (a + q) rfl φ = 0
  · exact ⟨0, by rw [zero_comp, hz]⟩
  obtain ⟨τ, hτ, hW⟩ := exists_parent X Y B e W (a + q) σ (hgood hz)
  obtain ⟨g, hg⟩ := CapOutputSupport.exists_simplex_factor (𝟙 Y) W a q
    (cochainPullback (SmallCapSubspaceLift.source X Y B e) a φ) τ (fun _ => hW)
  have hid : push (𝟙 Y) = 𝟙 (chains Y) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 Y)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [hid, HomologicalComplex.id_f, Category.comp_id] at hg
  refine ⟨g, ?_⟩
  rw [source, push_comp, HomologicalComplex.comp_f, ← Category.assoc, hg]
  have hn := CapOutputSupport.cap_push_simplex (SmallCapSubspaceLift.source X Y B e) a q φ τ
  rw [hτ] at hn
  exact hn

variable {ι : Type*} (V : ι → Set X) (a : ℕ) (φ : singularCochainGroup (ZMod 2) X a)
  (hgood : ∀ q (σ : (X.smallSingularSubcomplex V : SSet) _⦋a + q⦌),
    (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ absoluteChain X a q (a + q) rfl φ ≠ 0 →
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ SmallCapSubspaceLift.source X Y B e '' W)

def component (q : ℕ) : (small X V).X (a + q) ⟶ (chains (TopCat.of W)).X q :=
  Cofan.IsColimit.desc ((X.smallSingularSubcomplex V : SSet).isColimitChainComplexXCofan coeff (a + q))
    fun σ => (exists_simplex X Y B e W a q φ σ.val (hgood q σ)).choose

theorem component_source (q : ℕ) :
    component X Y B e W V a φ hgood q ≫ (push (source X Y B e W)).f q =
      (inclusion X V).f (a + q) ≫ absoluteChain X a q (a + q) rfl φ := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex V : SSet)) (R := coeff)
  intro σ
  have hc : (X.smallSingularSubcomplex V : SSet).ιChainComplex σ ≫
      component X Y B e W V a φ hgood q =
        (exists_simplex X Y B e W a q φ σ.val (hgood q σ)).choose :=
    Cofan.IsColimit.fac _ _ σ
  rw [← Category.assoc, hc]
  simpa only [inclusion, SSet.ι_chainComplexMap_f_assoc, Subfunctor.ι_app,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply] using
    (exists_simplex X Y B e W a q φ σ.val (hgood q σ)).choose_spec

end
end Finsler.EmbeddedCapOutputSupport
