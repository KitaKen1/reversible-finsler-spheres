module

public import Finsler.Topology.CapOutputSupport
public import Finsler.Topology.SmallRetractionComparison

/-! The actual whole-parent support of a single cap pulls back along
an embedding which is monic on singular chains. Arbitrary actual
mapped covers are allowed, so their centers need not belong to the
smaller parameter space. -/

@[expose] public section
namespace Finsler.SingleCapEmbeddingPullback

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {Z X : TopCat.{0}} {ι κ : Type*} (V : ι → Set Z) (W : κ → Set X)
  (h : Z ⟶ X) (r : ι → κ) (hf : ∀ i, Set.MapsTo h (V i) (W (r i)))
  (D : Set X) (d : ℕ) (φ : singularCochainGroup (ZMod 2) X d)
  (hmono : ∀ q, Mono ((push h).f q))
  (hgood : ∀ q (σ : (X.smallSingularSubcomplex W : SSet) _⦋d + q⦌),
    (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ absoluteChain X d q (d + q) rfl φ ≠ 0 →
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ D)

include r hf hmono hgood in
theorem good (q : ℕ) (σ : (Z.smallSingularSubcomplex V : SSet) _⦋d + q⦌)
    (hcap : (TopCat.toSSet.obj Z).ιChainComplex σ.val ≫
      absoluteChain Z d q (d + q) rfl (cochainPullback h d φ) ≠ 0) :
    Set.range (Z.toSSetObjEquiv _ σ.val) ⊆ h ⁻¹' D := by
  let τ : (X.smallSingularSubcomplex W : SSet) _⦋d + q⦌ :=
    ⟨(TopCat.toSSet.map h).app _ σ.val, by
      apply (TopCat.mem_smallSingularSubcomplex_iff X W _).mpr
      obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff Z V σ.val).mp σ.property
      refine ⟨r i, ?_⟩
      rintro y ⟨t, rfl⟩
      rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
      exact hf i (hi ⟨t, rfl⟩)⟩
  have he := CapOutputSupport.cap_push_simplex h d q φ σ.val
  have : Mono ((push h).f q) := hmono q
  have hn : (TopCat.toSSet.obj X).ιChainComplex τ.val ≫ absoluteChain X d q (d + q) rfl φ ≠ 0 := by
    intro hz
    apply hcap
    apply (cancel_mono ((push h).f q)).mp
    rw [zero_comp]
    exact he.trans hz
  intro z hz
  have hzr : h z ∈ Set.range (X.toSSetObjEquiv _ τ.val) := by
    obtain ⟨t, ht⟩ := hz
    refine ⟨t, ?_⟩
    change X.toSSetObjEquiv _ ((TopCat.toSSet.map h).app _ σ.val) t = h z
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
    exact congrArg h ht
  exact hgood q τ hn hzr

def operation (hc : cochainCoboundary (ZMod 2) X d φ = 0) := CapOutputSupport.operation V (𝟙 Z) (h ⁻¹' D) d
  (cochainPullback h d φ) (fun q σ hn => good V W h r hf D d φ hmono hgood q σ hn)
  (pullback_closed h d φ hc)

theorem source (hc : cochainCoboundary (ZMod 2) X d φ = 0) (q : ℕ) :
    (operation V W h r hf D d φ hmono hgood hc).component q ≫
      (push (SupportedCap.subspaceMap Z (h ⁻¹' D))).f q =
    (inclusion Z V).f (d + q) ≫ absoluteChain Z d q (d + q) rfl (cochainPullback h d φ) := by
  have hi := CapOutputSupport.component_inclusion V (𝟙 Z) (h ⁻¹' D) d
    (cochainPullback h d φ) (fun q σ hn => good V W h r hf D d φ hmono hgood q σ hn) q
  have hid : push (𝟙 Z) = 𝟙 (chains Z) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.{0}.map (𝟙 Z)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, HomologicalComplex.id_f] at hi
  exact hi.trans (congrArg (fun z => (inclusion Z V).f (d + q) ≫ z)
    (Category.comp_id (absoluteChain Z d q (d + q) rfl (cochainPullback h d φ))))

end
end Finsler.SingleCapEmbeddingPullback
