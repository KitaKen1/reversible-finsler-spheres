module

public import Finsler.Topology.CapOutputSupport

/-! Turn actual carrier bounds into chains in an actual target subspace.
Only degreewise chain inclusions are cancelled; no homology injectivity
or replacement of the original target subspace is assumed. -/

@[expose] public section
namespace Finsler.CarrierSubspaceFactor

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {X Y : TopCat.{0}} {ι : Type*} (W : ι → Set X) (f : X ⟶ Y) (B : Set Y)
  (hf : ∀ i, Set.MapsTo f (W i) B)

include hf

theorem simplex_image {n : ℕ} (σ : (X.smallSingularSubcomplex W : SSet) _⦋n⦌) :
    Set.range (Y.toSSetObjEquiv _ ((TopCat.toSSet.map f).app _ σ.val)) ⊆ B := by
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X W σ.val).mp σ.property
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  rintro _ ⟨t, rfl⟩
  exact hf i (hi ⟨t, rfl⟩)

def liftedSimplex {n : ℕ} (σ : (X.smallSingularSubcomplex W : SSet) _⦋n⦌) :
    TopCat.toSSet.obj (TopCat.of B) _⦋n⦌ :=
  SupportedCap.simplexLift Y B ((TopCat.toSSet.map f).app _ σ.val) (simplex_image W f B hf σ)

theorem liftedSimplex_image {n : ℕ} (σ : (X.smallSingularSubcomplex W : SSet) _⦋n⦌) :
    (TopCat.toSSet.map (SupportedCap.subspaceMap Y B)).app _ (liftedSimplex W f B hf σ) =
      (TopCat.toSSet.map f).app _ σ.val :=
  SupportedCap.simplexLift_image Y B _ (simplex_image W f B hf σ)

def component (n : ℕ) : (small X W).X n ⟶ (chains (TopCat.of B)).X n :=
  Cofan.IsColimit.desc ((X.smallSingularSubcomplex W : SSet).isColimitChainComplexXCofan coeff n)
    fun σ => (TopCat.toSSet.obj (TopCat.of B)).ιChainComplex (liftedSimplex W f B hf σ)

theorem component_inclusion (n : ℕ) :
    component W f B hf n ≫ (push (SupportedCap.subspaceMap Y B)).f n =
      (inclusion X W).f n ≫ (push f).f n := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex W : SSet)) (R := coeff)
  intro σ
  have hc : (X.smallSingularSubcomplex W : SSet).ιChainComplex σ ≫ component W f B hf n =
      (TopCat.toSSet.obj (TopCat.of B)).ιChainComplex (liftedSimplex W f B hf σ) :=
    Cofan.IsColimit.fac _ _ σ
  rw [← Category.assoc, hc]
  simp only [push, SSet.ι_chainComplexMap_f, ← Category.assoc, inclusion]
  exact congrArg (fun τ => (TopCat.toSSet.obj Y).ιChainComplex (R := coeff) τ)
    (liftedSimplex_image W f B hf σ)

def chainMap : small X W ⟶ chains (TopCat.of B) where
  f := component W f B hf
  comm' i j _ := by
    let k := push (SupportedCap.subspaceMap Y B)
    haveI : Mono (k.f j) := SupportedCap.subspacePush_mono Y B j
    apply (cancel_mono (k.f j)).mp
    rw [Category.assoc, ← k.comm, ← Category.assoc, component_inclusion]
    simp only [Category.assoc]
    rw [(push f).comm, ← Category.assoc ((inclusion X W).f i), (inclusion X W).comm]
    simp only [Category.assoc]
    rw [component_inclusion]

theorem chainMap_inclusion :
    chainMap W f B hf ≫ push (SupportedCap.subspaceMap Y B) = inclusion X W ≫ push f := by
  ext n : 1
  exact component_inclusion W f B hf n

theorem push_factor {n : ℕ} {c : coeff ⟶ (chains X).X n} (hc : c ∈ supported X W n) :
    ∃ d : coeff ⟶ (chains (TopCat.of B)).X n,
      d ≫ (push (SupportedCap.subspaceMap Y B)).f n = c ≫ (push f).f n := by
  obtain ⟨a, ha⟩ := (TauCeti.mem_smallSingularChains_iff _).mp hc
  refine ⟨a ≫ (chainMap W f B hf).f n, ?_⟩
  change (a ≫ component W f B hf n) ≫ _ = _
  rw [Category.assoc, component_inclusion, ← Category.assoc, ha]

end
end Finsler.CarrierSubspaceFactor
