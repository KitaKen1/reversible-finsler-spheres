module

public import Finsler.Topology.CapOutputSupport

/-! Lift an actual cap directly into a small-chain complex on a
homeomorphic subspace. Every nonzero whole parent must lie in the image
of one target carrier. Only degreewise chain monicity is cancelled. -/

@[expose] public section
namespace Finsler.SmallCapSubspaceLift

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable (X Y : TopCat.{0}) (B : Set X) (e : Y ≅ TopCat.of B)

def source : Y ⟶ X := e.hom ≫ SupportedCap.subspaceMap X B

def target {κ : Type*} (U : κ → Set Y) : small Y U ⟶ chains X :=
  inclusion Y U ≫ push (source X Y B e)

theorem target_mono {κ : Type*} (U : κ → Set Y) (q : ℕ) :
    Mono ((target X Y B e U).f q) := by
  haveI : Mono (SupportedCap.subspaceMap X B) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  haveI : Mono (source X Y B e) := by dsimp only [source]; infer_instance
  haveI : Mono ((push (source X Y B e)).f q) :=
    inferInstanceAs (Mono ((sigmaConst.obj coeff).map
      ((TopCat.toSSet.map (source X Y B e)).app (Opposite.op ⦋q⦌))))
  haveI : Mono ((inclusion Y U).f q) :=
    inferInstanceAs (Mono ((sigmaConst.obj coeff).map
      ((Y.smallSingularSubcomplex U).ι.app (Opposite.op ⦋q⦌))))
  rw [target, HomologicalComplex.comp_f]
  infer_instance

theorem exists_simplex {κ : Type*} (U : κ → Set Y) (a q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X a) (σ : TopCat.toSSet.obj X _⦋a + q⦌)
    (hgood : (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a q (a + q) rfl φ ≠ 0 →
      ∃ i, Set.range (X.toSSetObjEquiv _ σ) ⊆ source X Y B e '' U i) :
    ∃ g : coeff ⟶ (small Y U).X q,
      g ≫ (target X Y B e U).f q =
        (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a q (a + q) rfl φ := by
  classical
  by_cases hz : (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a q (a + q) rfl φ = 0
  · exact ⟨0, by rw [zero_comp, hz]⟩
  obtain ⟨i, hi⟩ := hgood hz
  have hB : Set.range (X.toSSetObjEquiv _ σ) ⊆ B := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hi hz
    exact (e.hom y).property
  let τB := SupportedCap.simplexLift X B σ hB
  let τ := (TopCat.toSSet.map e.inv).app (Opposite.op ⦋a + q⦌) τB
  have hj : e.inv ≫ source X Y B e = SupportedCap.subspaceMap X B := by
    dsimp only [source]
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hτ : (TopCat.toSSet.map (source X Y B e)).app (Opposite.op ⦋a + q⦌) τ = σ := by
    change ((TopCat.toSSet.map e.inv ≫ TopCat.toSSet.map (source X Y B e)).app _ τB) = σ
    rw [← Functor.map_comp, hj]
    exact SupportedCap.simplexLift_image X B σ hB
  have hjinj : Function.Injective (source X Y B e) := by
    intro y z h
    apply (TopCat.mono_iff_injective e.hom).mp inferInstance
    exact Subtype.ext h
  have hsmall : τ ∈ (Y.smallSingularSubcomplex U).obj (Opposite.op ⦋a + q⦌) := by
    apply (TopCat.mem_smallSingularSubcomplex_iff Y U τ).mpr
    refine ⟨i, ?_⟩
    rintro _ ⟨t, rfl⟩
    have he : source X Y B e (Y.toSSetObjEquiv _ τ t) = X.toSSetObjEquiv _ σ t := by
      have hh := congrArg (fun s => X.toSSetObjEquiv _ s t) hτ
      rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at hh
      exact hh
    obtain ⟨y, hy, heq⟩ := hi ⟨t, rfl⟩
    rw [hjinj (he.trans heq.symm)]
    exact hy
  let τs : (Y.smallSingularSubcomplex U : SSet) _⦋a + q⦌ := ⟨τ, hsmall⟩
  refine ⟨(Y.smallSingularSubcomplex U : SSet).ιChainComplex τs ≫
    SmallCapCarrier.smallCap Y U a q (a + q) rfl (cochainPullback (source X Y B e) a φ), ?_⟩
  have hc : ((Y.smallSingularSubcomplex U : SSet).ιChainComplex τs ≫
      SmallCapCarrier.smallCap Y U a q (a + q) rfl (cochainPullback (source X Y B e) a φ)) ≫
        (inclusion Y U).f q =
      (TopCat.toSSet.obj Y).ιChainComplex τ ≫
        absoluteChain Y a q (a + q) rfl (cochainPullback (source X Y B e) a φ) := by
    rw [Category.assoc, SmallCapCarrier.smallCap_inclusion, ← Category.assoc,
      inclusion, SSet.ι_chainComplexMap_f]
    rfl
  have hn := CapOutputSupport.cap_push_simplex (source X Y B e) a q φ τ
  rw [hτ] at hn
  calc
    _ = ((TopCat.toSSet.obj Y).ιChainComplex τ ≫
        absoluteChain Y a q (a + q) rfl (cochainPullback (source X Y B e) a φ)) ≫
          (push (source X Y B e)).f q := by
      change _ ≫ ((inclusion Y U).f q ≫ (push (source X Y B e)).f q) = _
      rw [← Category.assoc, hc]
    _ = _ := hn

variable {ι κ : Type*} (V : ι → Set X) (U : κ → Set Y) (a : ℕ)
  (φ : singularCochainGroup (ZMod 2) X a)
  (hgood : ∀ q (σ : (X.smallSingularSubcomplex V : SSet) _⦋a + q⦌),
    (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ absoluteChain X a q (a + q) rfl φ ≠ 0 →
      ∃ i, Set.range (X.toSSetObjEquiv _ σ.val) ⊆ source X Y B e '' U i)

def component (q : ℕ) : (small X V).X (a + q) ⟶ (small Y U).X q :=
  Cofan.IsColimit.desc ((X.smallSingularSubcomplex V : SSet).isColimitChainComplexXCofan coeff (a + q))
    fun σ => (exists_simplex X Y B e U a q φ σ.val (hgood q σ)).choose

theorem component_inclusion (q : ℕ) :
    component X Y B e V U a φ hgood q ≫ (target X Y B e U).f q =
      (inclusion X V).f (a + q) ≫ absoluteChain X a q (a + q) rfl φ := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex V : SSet)) (R := coeff)
  intro σ
  have hc : (X.smallSingularSubcomplex V : SSet).ιChainComplex σ ≫
      component X Y B e V U a φ hgood q =
        (exists_simplex X Y B e U a q φ σ.val (hgood q σ)).choose :=
    Cofan.IsColimit.fac _ _ σ
  rw [← Category.assoc, hc]
  simpa only [inclusion, SSet.ι_chainComplexMap_f_assoc, Subfunctor.ι_app,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply] using
    (exists_simplex X Y B e U a q φ σ.val (hgood q σ)).choose_spec

theorem component_boundary (hφ : cochainCoboundary (ZMod 2) X a φ = 0) (q : ℕ) :
    component X Y B e V U a φ hgood (q + 1) ≫ (small Y U).d (q + 1) q =
      (small X V).d (a + (q + 1)) (a + q) ≫ component X Y B e V U a φ hgood q := by
  haveI := target_mono X Y B e U q
  apply (cancel_mono ((target X Y B e U).f q)).mp
  rw [Category.assoc, ← (target X Y B e U).comm, ← Category.assoc, component_inclusion]
  have hb := (SupportedCapHomology.absoluteOperation X a φ hφ).comm q
  change absoluteChain X a (q + 1) (a + (q + 1)) rfl φ ≫ (chains X).d (q + 1) q =
    (chains X).d (a + (q + 1)) (a + q) ≫ absoluteChain X a q (a + q) rfl φ at hb
  rw [Category.assoc, hb]
  rw [← Category.assoc, (inclusion X V).comm]
  simp only [Category.assoc]
  rw [component_inclusion]

def operation (hφ : cochainCoboundary (ZMod 2) X a φ = 0) :
    DegreeLoweringHomology.Map (small X V) (small Y U) a where
  component := component X Y B e V U a φ hgood
  comm := component_boundary X Y B e V U a φ hgood hφ

end
end Finsler.SmallCapSubspaceLift
