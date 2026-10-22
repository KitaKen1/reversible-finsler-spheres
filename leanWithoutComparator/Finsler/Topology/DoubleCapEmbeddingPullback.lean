module

public import Finsler.Topology.PartialDoubleCapDomainFiltered
public import Finsler.Topology.SmallRetractionComparison

/-! Whole-parent length bounds for the actual successive caps pull back
along a chain-monic parameter embedding. In particular, a face inclusion
with a continuous left inverse preserves the nonzero-cap witness. -/

@[expose] public section
namespace Finsler.DoubleCapEmbeddingPullback

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

variable {Z X Y : TopCat.{0}} {ι : Type*}
  (h : Z ⟶ X) (W : ι → Set X) (D : Set X) (f : TopCat.of D ⟶ Y) (B : Set Y)

def cover : ι → Set Z := fun i => h ⁻¹' W i

def domainMap : TopCat.of (h ⁻¹' D) ⟶ TopCat.of D :=
  restriction h (h ⁻¹' D) D (fun _ hz => hz)

def retained : TopCat.of (h ⁻¹' D) ⟶ Y := domainMap h D ≫ f

variable (k p : ℕ)
  (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
  (hmono : ∀ q, Mono ((push h).f q))
  (hgood : ∀ q (σ : (X.smallSingularSubcomplex W : SSet) _⦋k + (p + q)⦌),
    (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ PartialDoubleCap.cap X k p q φ ψ ≠ 0 →
      ∀ z ∈ Set.range (X.toSSetObjEquiv _ σ.val), ∃ hz : z ∈ D, f ⟨z, hz⟩ ∈ B)

include hmono hgood

theorem good (q : ℕ)
    (σ : (Z.smallSingularSubcomplex (cover h W) : SSet) _⦋k + (p + q)⦌)
    (hcap : (TopCat.toSSet.obj Z).ιChainComplex σ.val ≫
      PartialDoubleCap.cap Z k p q (cochainPullback h k φ) (cochainPullback h p ψ) ≠ 0) :
    ∀ z ∈ Set.range (Z.toSSetObjEquiv _ σ.val),
      ∃ hz : z ∈ h ⁻¹' D, retained h D f ⟨z, hz⟩ ∈ B := by
  let τ : (X.smallSingularSubcomplex W : SSet) _⦋k + (p + q)⦌ :=
    ⟨(TopCat.toSSet.map h).app _ σ.val, by
      apply (TopCat.mem_smallSingularSubcomplex_iff X W _).mpr
      obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff Z (cover h W) σ.val).mp σ.property
      refine ⟨i, ?_⟩
      rintro y ⟨t, rfl⟩
      rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
      exact hi ⟨t, rfl⟩⟩
  have he : (TopCat.toSSet.obj X).ιChainComplex τ.val ≫ PartialDoubleCap.cap X k p q φ ψ =
      ((TopCat.toSSet.obj Z).ιChainComplex σ.val ≫
        PartialDoubleCap.cap Z k p q (cochainPullback h k φ) (cochainPullback h p ψ)) ≫
          (push h).f q := by
    calc
      _ = ((TopCat.toSSet.obj Z).ιChainComplex σ.val ≫ (push h).f (k + (p + q))) ≫
          PartialDoubleCap.cap X k p q φ ψ := by
        rw [push, SSet.ι_chainComplexMap_f]
      _ = _ := by rw [Category.assoc, ← PartialDoubleCap.cap_natural, ← Category.assoc]
  haveI : Mono ((push h).f q) := hmono q
  have hn : (TopCat.toSSet.obj X).ιChainComplex τ.val ≫ PartialDoubleCap.cap X k p q φ ψ ≠ 0 := by
    intro hz
    apply hcap
    apply (cancel_mono ((push h).f q)).mp
    rw [zero_comp]
    exact he.symm.trans hz
  intro z hz
  have hzr : h z ∈ Set.range (X.toSSetObjEquiv _ τ.val) := by
    obtain ⟨t, ht⟩ := hz
    refine ⟨t, ?_⟩
    change X.toSSetObjEquiv _ ((TopCat.toSSet.map h).app _ σ.val) t = h z
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
    exact congrArg h ht
  obtain ⟨hd, hb⟩ := hgood q τ hn (h z) hzr
  exact ⟨hd, hb⟩

end
end Finsler.DoubleCapEmbeddingPullback
