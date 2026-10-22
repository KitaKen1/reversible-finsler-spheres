module

public import Finsler.Topology.ThreeCapFunctoriality
public import Finsler.Topology.PartialDoubleCapDomainFiltered
public import Finsler.Topology.DegreeLoweringHomology

/-! Construct a global linear three-cap lift into the actual bounded
partial domain. Its boundary equation is inherited by singular-chain
monicity from the literal ambient three-cap equation. No homology
injectivity or pre-existing bounded lift is assumed. -/

@[expose] public section
namespace Finsler.ThreeCapDomainFiltered

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.ThreeCapBlockVanishing
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable (X Y : TopCat.{0}) (D : Set X) (f : TopCat.of D ⟶ Y) (B : Set Y)

def source : TopCat.of (PartialDoubleCapDomainFiltered.boundedDomain X Y D f B) ⟶ X :=
  SupportedCap.subspaceMap (TopCat.of D) (PartialDoubleCapDomainFiltered.boundedDomain X Y D f B) ≫
    SupportedCap.subspaceMap X D

theorem source_mono (q : ℕ) : Mono ((push (source X Y D f B)).f q) := by
  haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of D)
      (PartialDoubleCapDomainFiltered.boundedDomain X Y D f B))).f q) :=
    SupportedCap.subspacePush_mono (TopCat.of D)
      (PartialDoubleCapDomainFiltered.boundedDomain X Y D f B) q
  haveI : Mono ((push (SupportedCap.subspaceMap X D)).f q) :=
    SupportedCap.subspacePush_mono X D q
  rw [source, push_comp, HomologicalComplex.comp_f]
  infer_instance

theorem exists_bounded_simplex (a b c q : ℕ)
    (J : singularCochainGroup (ZMod 2) X a)
    (φ : singularCochainGroup (ZMod 2) X b) (ψ : singularCochainGroup (ZMod 2) X c)
    (σ : TopCat.toSSet.obj X _⦋a + b + c + q⦌)
    (hgood : (TopCat.toSSet.obj X).ιChainComplex σ ≫ threeCap X a b c q J φ ψ ≠ 0 →
      ∀ z ∈ Set.range (X.toSSetObjEquiv _ σ), ∃ hz : z ∈ D, f ⟨z, hz⟩ ∈ B) :
    ∃ C : coeff ⟶ (chains (TopCat.of (PartialDoubleCapDomainFiltered.boundedDomain X Y D f B))).X q,
      C ≫ (push (source X Y D f B)).f q =
        (TopCat.toSSet.obj X).ιChainComplex σ ≫ threeCap X a b c q J φ ψ := by
  classical
  by_cases hz : (TopCat.toSSet.obj X).ιChainComplex σ ≫ threeCap X a b c q J φ ψ = 0
  · exact ⟨0, by rw [zero_comp, hz]⟩
  have hD : Set.range (X.toSSetObjEquiv _ σ) ⊆ D := fun z h => (hgood hz z h).choose
  let τ := SupportedCap.simplexLift X D σ hD
  have hE : Set.range ((TopCat.of D).toSSetObjEquiv _ τ) ⊆
      PartialDoubleCapDomainFiltered.boundedDomain X Y D f B := by
    intro z h
    exact (hgood hz z.val (PartialDoubleCap.lifted_parent X D σ hD z h)).choose_spec
  let ζ := SupportedCap.simplexLift (TopCat.of D)
    (PartialDoubleCapDomainFiltered.boundedDomain X Y D f B) τ hE
  have hζ : (TopCat.toSSet.map (source X Y D f B)).app _ ζ = σ := by
    simp only [source, Functor.map_comp, NatTrans.comp_app, types_comp_apply]
    rw [SupportedCap.simplexLift_image, SupportedCap.simplexLift_image]
  refine ⟨(TopCat.toSSet.obj (TopCat.of (PartialDoubleCapDomainFiltered.boundedDomain X Y D f B))).ιChainComplex ζ ≫
    threeCap (TopCat.of (PartialDoubleCapDomainFiltered.boundedDomain X Y D f B)) a b c q
      (cochainPullback (source X Y D f B) a J)
      (cochainPullback (source X Y D f B) b φ)
      (cochainPullback (source X Y D f B) c ψ), ?_⟩
  rw [Category.assoc, ThreeCapFunctoriality.natural, ← Category.assoc, push,
    SSet.ι_chainComplexMap_f, hζ]

variable {ι : Type*} (W : ι → Set X) (a b c : ℕ)
  (J : singularCochainGroup (ZMod 2) X a)
  (φ : singularCochainGroup (ZMod 2) X b) (ψ : singularCochainGroup (ZMod 2) X c)
  (hgood : ∀ q (σ : (X.smallSingularSubcomplex W : SSet) _⦋a + b + c + q⦌),
    (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ threeCap X a b c q J φ ψ ≠ 0 →
      ∀ z ∈ Set.range (X.toSSetObjEquiv _ σ.val), ∃ hz : z ∈ D, f ⟨z, hz⟩ ∈ B)

def component (q : ℕ) : (small X W).X (a + b + c + q) ⟶
    (chains (TopCat.of (PartialDoubleCapDomainFiltered.boundedDomain X Y D f B))).X q :=
  Cofan.IsColimit.desc
    ((X.smallSingularSubcomplex W : SSet).isColimitChainComplexXCofan coeff (a + b + c + q))
    fun σ => (exists_bounded_simplex X Y D f B a b c q J φ ψ σ.val (hgood q σ)).choose

theorem source_inclusion (q : ℕ) :
    component X Y D f B W a b c J φ ψ hgood q ≫ (push (source X Y D f B)).f q =
      (inclusion X W).f (a + b + c + q) ≫ threeCap X a b c q J φ ψ := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex W : SSet)) (R := coeff)
  intro σ
  have he : (X.smallSingularSubcomplex W : SSet).ιChainComplex σ ≫
      component X Y D f B W a b c J φ ψ hgood q =
        (exists_bounded_simplex X Y D f B a b c q J φ ψ σ.val (hgood q σ)).choose :=
    Cofan.IsColimit.fac _ _ σ
  rw [← Category.assoc, he]
  simpa only [inclusion, push, SSet.ι_chainComplexMap_f_assoc,
    Subfunctor.ι_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply] using
      (exists_bounded_simplex X Y D f B a b c q J φ ψ σ.val (hgood q σ)).choose_spec

variable (hcomm : ∀ q,
  ((inclusion X W).f (a + b + c + (q + 1)) ≫ threeCap X a b c (q + 1) J φ ψ) ≫
    (chains X).d (q + 1) q =
      (small X W).d (a + b + c + (q + 1)) (a + b + c + q) ≫
        ((inclusion X W).f (a + b + c + q) ≫ threeCap X a b c q J φ ψ))

include hcomm in
theorem component_boundary (q : ℕ) :
    component X Y D f B W a b c J φ ψ hgood (q + 1) ≫
      (chains (TopCat.of (PartialDoubleCapDomainFiltered.boundedDomain X Y D f B))).d (q + 1) q =
    (small X W).d (a + b + c + (q + 1)) (a + b + c + q) ≫
      component X Y D f B W a b c J φ ψ hgood q := by
  haveI := source_mono X Y D f B q
  apply (cancel_mono ((push (source X Y D f B)).f q)).mp
  rw [Category.assoc, ← (push (source X Y D f B)).comm, ← Category.assoc, source_inclusion]
  simp only [Category.assoc]
  rw [source_inclusion]
  simpa only [Category.assoc] using hcomm q

def operation : DegreeLoweringHomology.Map (small X W)
    (chains (TopCat.of (PartialDoubleCapDomainFiltered.boundedDomain X Y D f B))) (a + b + c) where
  component := component X Y D f B W a b c J φ ψ hgood
  comm := component_boundary X Y D f B W a b c J φ ψ hgood hcomm

def output : DegreeLoweringHomology.Map (small X W) (chains (TopCat.of B)) (a + b + c) :=
  (operation X Y D f B W a b c J φ ψ hgood hcomm).post
    (push (PartialDoubleCapDomainFiltered.retained X Y D f B))

end
end Finsler.ThreeCapDomainFiltered
