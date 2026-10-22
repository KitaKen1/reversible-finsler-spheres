module

public import Finsler.Topology.SupportedCap
public import Finsler.Topology.SupportedCapNaturality
public import Finsler.Topology.SupportedCapHomology

/-! Factor an actual cap followed by a continuous map into a target subspace,
when every nonzero parent lies there. The construction stays on small chains
and commutes with boundary; no homology inclusion is cancelled. -/

@[expose] public section
namespace Finsler.CapOutputSupport

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem cap_push_simplex {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y p)
    (σ : TopCat.toSSet.obj X _⦋p + q⦌) :
    ((TopCat.toSSet.obj X).ιChainComplex σ ≫
      absoluteChain X p q (p + q) rfl (cochainPullback f p φ)) ≫
        (SupportedCapNaturality.push f).f q =
      (TopCat.toSSet.obj Y).ιChainComplex
        ((TopCat.toSSet.map f).app (Opposite.op ⦋p + q⦌) σ) ≫
          absoluteChain Y p q (p + q) rfl φ := by
  have hn := RelativeCapBoundary.absolute_chain_natural f p q (p + q) rfl φ
  calc
    _ = ((TopCat.toSSet.obj X).ιChainComplex σ ≫
        (SupportedCapNaturality.push f).f (p + q)) ≫
          absoluteChain Y p q (p + q) rfl φ := by
      simpa only [SupportedCapNaturality.push, Category.assoc] using
        congrArg (fun h => (TopCat.toSSet.obj X).ιChainComplex σ ≫ h) hn
    _ = _ := by rw [SupportedCapNaturality.push, SSet.ι_chainComplexMap_f]

theorem exists_simplex_factor {X Y : TopCat.{0}} (f : X ⟶ Y) (B : Set Y) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (σ : TopCat.toSSet.obj X _⦋p + q⦌)
    (hgood : (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X p q (p + q) rfl φ ≠ 0 →
      ∀ z ∈ Set.range (X.toSSetObjEquiv _ σ), f z ∈ B) :
    ∃ g : coeff ⟶ (chains (TopCat.of B)).X q,
      g ≫ (SupportedCapNaturality.push (SupportedCap.subspaceMap Y B)).f q =
        (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X p q (p + q) rfl φ ≫
          (SupportedCapNaturality.push f).f q := by
  classical
  by_cases hzero : (TopCat.toSSet.obj X).ιChainComplex σ ≫
      absoluteChain X p q (p + q) rfl φ = 0
  · exact ⟨0, by rw [zero_comp, ← Category.assoc, hzero, zero_comp]⟩
  let A : Set X := f ⁻¹' B
  let i := SupportedCap.subspaceMap X A
  let g : TopCat.of A ⟶ TopCat.of B :=
    TopCat.ofHom ⟨fun z => ⟨f z.val, z.property⟩, (f.hom.continuous.comp
      continuous_subtype_val).subtype_mk _⟩
  have he : g ≫ SupportedCap.subspaceMap Y B = i ≫ f := by
    ext z : 1
    rfl
  have hσ : Set.range (X.toSSetObjEquiv _ σ) ⊆ A := hgood hzero
  let τ := SupportedCap.simplexLift X A σ hσ
  refine ⟨(TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
    absoluteChain (TopCat.of A) p q (p + q) rfl (cochainPullback i p φ) ≫
      (SupportedCapNaturality.push g).f q, ?_⟩
  have hm : SupportedCapNaturality.push g ≫
      SupportedCapNaturality.push (SupportedCap.subspaceMap Y B) =
    SupportedCapNaturality.push i ≫ SupportedCapNaturality.push f := by
    simp only [SupportedCapNaturality.push, ← Functor.map_comp, ← TopCat.toSSet.map_comp, he]
  have hn : absoluteChain (TopCat.of A) p q (p + q) rfl (cochainPullback i p φ) ≫
      (SupportedCapNaturality.push i).f q =
    (SupportedCapNaturality.push i).f (p + q) ≫ absoluteChain X p q (p + q) rfl φ := by
    simpa only [SupportedCapNaturality.push] using
      RelativeCapBoundary.absolute_chain_natural i p q (p + q) rfl φ
  calc
    _ = (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
        absoluteChain (TopCat.of A) p q (p + q) rfl (cochainPullback i p φ) ≫
          (SupportedCapNaturality.push i).f q ≫ (SupportedCapNaturality.push f).f q := by
      rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f, hm,
        HomologicalComplex.comp_f]
    _ = (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
        ((SupportedCapNaturality.push i).f (p + q) ≫ absoluteChain X p q (p + q) rfl φ) ≫
          (SupportedCapNaturality.push f).f q := by
      simpa only [Category.assoc] using congrArg
        (fun h => (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫ h ≫
          (SupportedCapNaturality.push f).f q) hn
    _ = _ := by
      simp only [← Category.assoc, SupportedCapNaturality.push, SSet.ι_chainComplexMap_f]
      rw [SupportedCap.simplexLift_image]

variable {X Y : TopCat.{0}} {ι : Type*} (V : ι → Set X) (f : X ⟶ Y) (B : Set Y) (p : ℕ)
  (φ : singularCochainGroup (ZMod 2) X p)
  (hgood : ∀ q (σ : (X.smallSingularSubcomplex V : SSet) _⦋p + q⦌),
    (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ absoluteChain X p q (p + q) rfl φ ≠ 0 →
      ∀ z ∈ Set.range (X.toSSetObjEquiv _ σ.val), f z ∈ B)

def component (q : ℕ) : (small X V).X (p + q) ⟶ (chains (TopCat.of B)).X q :=
  Cofan.IsColimit.desc ((X.smallSingularSubcomplex V : SSet).isColimitChainComplexXCofan coeff (p + q))
    fun σ => (exists_simplex_factor f B p q φ σ.val (hgood q σ)).choose

theorem component_inclusion (q : ℕ) :
    component V f B p φ hgood q ≫
        (SupportedCapNaturality.push (SupportedCap.subspaceMap Y B)).f q =
      (inclusion X V).f (p + q) ≫ absoluteChain X p q (p + q) rfl φ ≫
        (SupportedCapNaturality.push f).f q := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex V : SSet)) (R := coeff)
  intro σ
  have hc : (X.smallSingularSubcomplex V : SSet).ιChainComplex σ ≫
      component V f B p φ hgood q = (exists_simplex_factor f B p q φ σ.val (hgood q σ)).choose :=
    Cofan.IsColimit.fac _ _ σ
  rw [← Category.assoc, hc]
  simpa only [← Category.assoc, inclusion, SSet.ι_chainComplexMap_f,
    Subfunctor.ι_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply] using
    (exists_simplex_factor f B p q φ σ.val (hgood q σ)).choose_spec

theorem component_boundary (hφ : cochainCoboundary (ZMod 2) X p φ = 0) (q : ℕ) :
    component V f B p φ hgood (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
      (small X V).d (p + (q + 1)) (p + q) ≫ component V f B p φ hgood q := by
  let j := SupportedCapNaturality.push (SupportedCap.subspaceMap Y B)
  haveI : Mono (j.f q) := SupportedCap.subspacePush_mono Y B q
  apply (cancel_mono (j.f q)).mp
  rw [Category.assoc, ← j.comm, ← Category.assoc, component_inclusion]
  simp only [Category.assoc]
  rw [(SupportedCapNaturality.push f).comm]
  have hu := (SupportedCapHomology.absoluteOperation X p φ hφ).comm q
  change absoluteChain X p (q + 1) (p + (q + 1)) rfl φ ≫
      (chains X).d (q + 1) q =
    (chains X).d (p + (q + 1)) (p + q) ≫ absoluteChain X p q (p + q) rfl φ at hu
  rw [← Category.assoc (absoluteChain X p (q + 1) (p + (q + 1)) rfl φ), hu]
  simp only [Category.assoc]
  rw [← Category.assoc ((inclusion X V).f (p + (q + 1)))
    ((chains X).d (p + (q + 1)) (p + q)), HomologicalComplex.Hom.comm]
  simp only [Category.assoc]
  rw [component_inclusion]

def operation (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    DegreeLoweringHomology.Map (small X V) (chains (TopCat.of B)) p where
  component := component V f B p φ hgood
  comm := component_boundary V f B p φ hgood hφ

end
end Finsler.CapOutputSupport
