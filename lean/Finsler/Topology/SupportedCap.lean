module

public import Finsler.Topology.SmallCapCarrier

/-! A cochain supported off A annihilates chains carried by A already on chains.
This is the support input for localizing a diagonal cap to a neighborhood. -/

@[expose] public section

namespace Finsler.SupportedCap

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology Simplicial
open SphereOddDegree Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SmallCapCarrier Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def subspaceMap (X : TopCat.{0}) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def simplexLift (X : TopCat.{0}) (A : Set X) {n : ℕ}
    (σ : TopCat.toSSet.obj X _⦋n⦌) (hσ : Set.range (X.toSSetObjEquiv _ σ) ⊆ A) :
    TopCat.toSSet.obj (TopCat.of A) _⦋n⦌ :=
  ((TopCat.of A).toSSetObjEquiv _).symm
    ⟨fun t => ⟨X.toSSetObjEquiv _ σ t, hσ ⟨t, rfl⟩⟩,
      Continuous.subtype_mk (X.toSSetObjEquiv _ σ).continuous _⟩

theorem simplexLift_image (X : TopCat.{0}) (A : Set X) {n : ℕ}
    (σ : TopCat.toSSet.obj X _⦋n⦌) (hσ : Set.range (X.toSSetObjEquiv _ σ) ⊆ A) :
    (TopCat.toSSet.map (subspaceMap X A)).app (Opposite.op ⦋n⦌)
      (simplexLift X A σ hσ) = σ := by
  apply (X.toSSetObjEquiv _).injective
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  ext t
  change (((TopCat.of A).toSSetObjEquiv _)
    (((TopCat.of A).toSSetObjEquiv _).symm _ ) t).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem cap_zero_on_map {X Y : TopCat.{0}} (f : X ⟶ Y)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) Y p)
    (hφ : cochainPullback f p φ = 0) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) coeff).f n ≫
      absoluteChain Y p q n h φ = 0 := by
  rw [← Finsler.RelativeCapBoundary.absolute_chain_natural f p q n h φ, hφ]
  change (TauCeti.ChainComplex.capChain (ZMod 2) _ _ p q n h 0) ≫ _ = 0
  rw [map_zero, zero_comp]

theorem cap_zero_on_simplex (X : TopCat.{0}) (A : Set X)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0)
    (σ : TopCat.toSSet.obj X _⦋n⦌) (hσ : Set.range (X.toSSetObjEquiv _ σ) ⊆ A) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X p q n h φ = 0 := by
  have he : (TopCat.toSSet.obj X).ιChainComplex σ =
      (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (simplexLift X A σ hσ) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (subspaceMap X A)) coeff).f n := by
    rw [SSet.ι_chainComplexMap_f, simplexLift_image]
  rw [he, Category.assoc, cap_zero_on_map (subspaceMap X A) p q n h φ hφ, comp_zero]

def cover (X : TopCat.{0}) (A B : Set X) : Bool → Set X := fun b => if b then B else A

theorem exists_localized_simplex (X : TopCat.{0}) (A B : Set X)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0)
    (σ : (X.smallSingularSubcomplex (cover X A B) : SSet) _⦋n⦌) :
    ∃ g : coeff ⟶ (chains (TopCat.of B)).X q,
      g ≫ (SSet.chainComplexMap (TopCat.toSSet.map (subspaceMap X B)) coeff).f q =
        (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ absoluteChain X p q n h φ := by
  classical
  by_cases hB : Set.range (X.toSSetObjEquiv _ σ.val) ⊆ B
  · refine ⟨(TopCat.toSSet.obj (TopCat.of B)).ιChainComplex (simplexLift X B σ.val hB) ≫
      absoluteChain (TopCat.of B) p q n h (cochainPullback (subspaceMap X B) p φ), ?_⟩
    rw [Category.assoc, Finsler.RelativeCapBoundary.absolute_chain_natural,
      ← Category.assoc, SSet.ι_chainComplexMap_f, simplexLift_image]
  · have hA : Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A := by
      obtain ⟨b, hb⟩ := (TopCat.mem_smallSingularSubcomplex_iff X (cover X A B) σ.val).mp σ.property
      cases b with
      | false => exact hb
      | true => exact (hB hb).elim
    refine ⟨0, ?_⟩
    rw [zero_comp, cap_zero_on_simplex X A p q n h φ hφ σ.val hA]

def localizedCap (X : TopCat.{0}) (A B : Set X)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0) :
    (small X (cover X A B)).X n ⟶ (chains (TopCat.of B)).X q :=
  Cofan.IsColimit.desc
    ((X.smallSingularSubcomplex (cover X A B) : SSet).isColimitChainComplexXCofan coeff n)
    fun σ => (exists_localized_simplex X A B p q n h φ hφ σ).choose

theorem localizedCap_inclusion (X : TopCat.{0}) (A B : Set X)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0) :
    localizedCap X A B p q n h φ hφ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (subspaceMap X B)) coeff).f q =
      (inclusion X (cover X A B)).f n ≫ absoluteChain X p q n h φ := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex (cover X A B) : SSet))
    (R := coeff)
  intro σ
  have hc : (X.smallSingularSubcomplex (cover X A B) : SSet).ιChainComplex σ ≫
      localizedCap X A B p q n h φ hφ =
        (exists_localized_simplex X A B p q n h φ hφ σ).choose :=
    Cofan.IsColimit.fac _ _ σ
  rw [← Category.assoc, hc]
  simp only [inclusion, SSet.ι_chainComplexMap_f_assoc]
  exact (exists_localized_simplex X A B p q n h φ hφ σ).choose_spec.trans (by rfl)

theorem subspacePush_mono (X : TopCat.{0}) (B : Set X) (q : ℕ) :
    Mono ((SSet.chainComplexMap (TopCat.toSSet.map (subspaceMap X B)) coeff).f q) := by
  haveI : Mono (subspaceMap X B) := (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  exact inferInstanceAs (Mono ((sigmaConst.obj coeff).map
    ((TopCat.toSSet.map (subspaceMap X B)).app (Opposite.op ⦋q⦌))))

theorem localizedCap_boundary (X : TopCat.{0}) (A B : Set X)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0)
    (hclosed : cochainCoboundary (ZMod 2) X p φ = 0) :
    localizedCap X A B p (q + 1) (n + 1) (by omega) φ hφ ≫
        (chains (TopCat.of B)).d (q + 1) q =
      (small X (cover X A B)).d (n + 1) n ≫ localizedCap X A B p q n h φ hφ := by
  let j := SSet.chainComplexMap (TopCat.toSSet.map (subspaceMap X B)) coeff
  haveI : Mono (j.f q) := subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  calc
    _ = localizedCap X A B p (q + 1) (n + 1) (by omega) φ hφ ≫
        (j.f (q + 1) ≫ (chains X).d (q + 1) q) := by
      rw [Category.assoc, ← HomologicalComplex.Hom.comm]
    _ = (inclusion X (cover X A B)).f (n + 1) ≫
        (absoluteChain X p (q + 1) (n + 1) (by omega) φ ≫ (chains X).d (q + 1) q) := by
      rw [← Category.assoc]
      change (_ ≫ (SSet.chainComplexMap (TopCat.toSSet.map (subspaceMap X B)) coeff).f
        (q + 1)) ≫ _ = _
      rw [localizedCap_inclusion, Category.assoc]
    _ = (inclusion X (cover X A B)).f (n + 1) ≫
        ((chains X).d (n + 1) n ≫ absoluteChain X p q n h φ) := by
      rw [Finsler.RelativeCapBoundary.absolute_chain_boundary X p q n h φ hclosed]
    _ = _ := by
      rw [← Category.assoc, HomologicalComplex.Hom.comm, Category.assoc,
        ← localizedCap_inclusion, ← Category.assoc]

theorem cover_open (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    ∀ b, IsOpen (cover X A B b) := by
  intro b
  cases b
  · exact hA
  · exact hB

theorem cover_univ (X : TopCat.{0}) (A B : Set X) (hcover : A ∪ B = Set.univ) :
    ⋃ b, cover X A B b = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have hx : x ∈ A ∪ B := hcover.symm ▸ Set.mem_univ x
  rcases hx with hx | hx
  · exact ⟨false, hx⟩
  · exact ⟨true, hx⟩

def cut (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0) :
    (chains X).X n ⟶ (chains (TopCat.of B)).X q :=
  (TauCeti.smallSingularRetraction coeff (cover X A B)
    (cover_open X A B hA hB) (cover_univ X A B hcover)).f n ≫
    localizedCap X A B p q n h φ hφ

theorem cut_inclusion (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0) :
    cut X A B hA hB hcover p q n h φ hφ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (subspaceMap X B)) coeff).f q =
      (TauCeti.singularSmallApprox coeff (cover X A B)).f n ≫ absoluteChain X p q n h φ := by
  rw [cut, Category.assoc, localizedCap_inclusion, ← Category.assoc,
    ← HomologicalComplex.comp_f]
  exact congrArg (fun f => f.f n ≫ absoluteChain X p q n h φ)
    (TauCeti.smallSingularRetraction_comp_ι coeff (cover X A B)
      (cover_open X A B hA hB) (cover_univ X A B hcover))

theorem cut_boundary (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0)
    (hclosed : cochainCoboundary (ZMod 2) X p φ = 0) :
    cut X A B hA hB hcover p (q + 1) (n + 1) (by omega) φ hφ ≫
        (chains (TopCat.of B)).d (q + 1) q =
      (chains X).d (n + 1) n ≫ cut X A B hA hB hcover p q n h φ hφ := by
  rw [cut, Category.assoc, localizedCap_boundary X A B p q n h φ hφ hclosed,
    ← Category.assoc, HomologicalComplex.Hom.comm, Category.assoc]
  rfl


end
end Finsler.SupportedCap
