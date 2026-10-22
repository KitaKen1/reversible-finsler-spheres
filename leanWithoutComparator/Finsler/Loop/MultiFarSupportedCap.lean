module

public import Finsler.Topology.SupportedCapCochain
public import Finsler.Topology.SupportedCapNaturality

/-! A genuine supported cap for SEVERAL separate far sets and one near
set. A small simplex lies in one actual far set or in the near set.
No literal cochain vanishing on the UNION of the far sets is assumed.
The original TauCeti approximation is retained on this actual cover. -/
@[expose] public section
namespace Finsler.MultiFarSupportedCap
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Simplicial
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (X : TopCat.{0}) {ι : Type*} (A : ι → Set X) (B : Set X)

def cover : Option ι → Set X := fun i => match i with
  | .none => B
  | .some i => A i

theorem cover_open (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B) :
    ∀ i, IsOpen (cover X A B i) := by
  intro i
  cases i with
  | none => exact hB
  | some i => exact hA i

theorem cover_univ (hc : (⋃ i, A i) ∪ B = Set.univ) :
    ⋃ i, cover X A B i = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have hx : x ∈ (⋃ i, A i) ∪ B := hc.symm ▸ Set.mem_univ x
  rcases hx with hx | hx
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨some i, hi⟩
  · exact ⟨none, hx⟩

theorem exists_localized_simplex (p q N : ℕ) (h : p + q = N)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p φ = 0)
    (σ : (X.smallSingularSubcomplex (cover X A B) : SSet) _⦋N⦌) :
    ∃ g : coeff ⟶ (chains (TopCat.of B)).X q,
      g ≫ (push (SupportedCap.subspaceMap X B)).f q =
        (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ absoluteChain X p q N h φ := by
  classical
  by_cases hB : Set.range (X.toSSetObjEquiv _ σ.val) ⊆ B
  · refine ⟨(TopCat.toSSet.obj (TopCat.of B)).ιChainComplex
      (SupportedCap.simplexLift X B σ.val hB) ≫
        absoluteChain (TopCat.of B) p q N h
          (cochainPullback (SupportedCap.subspaceMap X B) p φ), ?_⟩
    rw [Category.assoc, push, RelativeCapBoundary.absolute_chain_natural,
      ← Category.assoc, SSet.ι_chainComplexMap_f, SupportedCap.simplexLift_image]
  · obtain ⟨i, hi⟩ :=
      (TopCat.mem_smallSingularSubcomplex_iff X (cover X A B) σ.val).mp σ.property
    cases i with
    | none => exact (hB hi).elim
    | some i =>
      refine ⟨0, ?_⟩
      rw [zero_comp, SupportedCap.cap_zero_on_simplex X (A i) p q N h φ (hs i) σ.val hi]

def localizedCap (p q N : ℕ) (h : p + q = N)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p φ = 0) :
    (small X (cover X A B)).X N ⟶ (chains (TopCat.of B)).X q :=
  Cofan.IsColimit.desc
    ((X.smallSingularSubcomplex (cover X A B) : SSet).isColimitChainComplexXCofan coeff N)
    fun σ => (exists_localized_simplex X A B p q N h φ hs σ).choose

theorem localizedCap_inclusion (p q N : ℕ) (h : p + q = N)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p φ = 0) :
    localizedCap X A B p q N h φ hs ≫ (push (SupportedCap.subspaceMap X B)).f q =
      (inclusion X (cover X A B)).f N ≫ absoluteChain X p q N h φ := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex (cover X A B) : SSet)) (R := coeff)
  intro σ
  have he : (X.smallSingularSubcomplex (cover X A B) : SSet).ιChainComplex σ ≫
      localizedCap X A B p q N h φ hs =
      (exists_localized_simplex X A B p q N h φ hs σ).choose :=
    Cofan.IsColimit.fac _ _ σ
  rw [← Category.assoc, he]
  simp only [inclusion, SSet.ι_chainComplexMap_f_assoc]
  exact (exists_localized_simplex X A B p q N h φ hs σ).choose_spec

theorem localizedCap_coboundary (p q N : ℕ) (h : p + q = N)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p φ = 0)
    (hd : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) (p + 1)
      (cochainCoboundary (ZMod 2) X p φ) = 0) :
    localizedCap X A B p (q + 1) (N + 1) (by omega) φ hs ≫ (chains (TopCat.of B)).d (q + 1) q =
      (small X (cover X A B)).d (N + 1) N ≫ localizedCap X A B p q N h φ hs -
        localizedCap X A B (p + 1) q (N + 1) (by omega)
          (cochainCoboundary (ZMod 2) X p φ) hd := by
  let j := push (SupportedCap.subspaceMap X B)
  have : Mono (j.f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  calc
    _ = localizedCap X A B p (q + 1) (N + 1) (by omega) φ hs ≫
        (j.f (q + 1) ≫ (chains X).d (q + 1) q) := by
      rw [Category.assoc, ← HomologicalComplex.Hom.comm]
    _ = (inclusion X (cover X A B)).f (N + 1) ≫
        (absoluteChain X p (q + 1) (N + 1) (by omega) φ ≫ (chains X).d (q + 1) q) := by
      rw [← Category.assoc, localizedCap_inclusion, Category.assoc]
    _ = (inclusion X (cover X A B)).f (N + 1) ≫
        ((chains X).d (N + 1) N ≫ absoluteChain X p q N h φ -
          absoluteChain X (p + 1) q (N + 1) (by omega) (cochainCoboundary (ZMod 2) X p φ)) := by
      rw [SupportedCapCochain.absolute_coboundary X p q N h φ]
    _ = _ := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
        localizedCap_inclusion, ← Category.assoc, HomologicalComplex.Hom.comm,
        Category.assoc, localizedCap_inclusion]

def cut (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B)
    (hc : (⋃ i, A i) ∪ B = Set.univ) (p q N : ℕ) (h : p + q = N)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p φ = 0) :
    (chains X).X N ⟶ (chains (TopCat.of B)).X q :=
  (TauCeti.smallSingularRetraction coeff (cover X A B)
    (cover_open X A B hA hB) (cover_univ X A B hc)).f N ≫ localizedCap X A B p q N h φ hs

theorem cut_inclusion (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B)
    (hc : (⋃ i, A i) ∪ B = Set.univ) (p q N : ℕ) (h : p + q = N)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p φ = 0) :
    cut X A B hA hB hc p q N h φ hs ≫ (push (SupportedCap.subspaceMap X B)).f q =
      (TauCeti.singularSmallApprox coeff (cover X A B)).f N ≫ absoluteChain X p q N h φ := by
  rw [cut, Category.assoc, localizedCap_inclusion, ← Category.assoc, ← HomologicalComplex.comp_f]
  exact congrArg (fun f => f.f N ≫ absoluteChain X p q N h φ)
    (TauCeti.smallSingularRetraction_comp_ι coeff (cover X A B)
      (cover_open X A B hA hB) (cover_univ X A B hc))

theorem cut_coboundary (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B)
    (hc : (⋃ i, A i) ∪ B = Set.univ) (p q N : ℕ) (h : p + q = N)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p φ = 0)
    (hd : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) (p + 1)
      (cochainCoboundary (ZMod 2) X p φ) = 0) :
    cut X A B hA hB hc p (q + 1) (N + 1) (by omega) φ hs ≫ (chains (TopCat.of B)).d (q + 1) q =
      (chains X).d (N + 1) N ≫ cut X A B hA hB hc p q N h φ hs -
        cut X A B hA hB hc (p + 1) q (N + 1) (by omega)
          (cochainCoboundary (ZMod 2) X p φ) hd := by
  rw [cut, Category.assoc, localizedCap_coboundary X A B p q N h φ hs hd,
    Preadditive.comp_sub, ← Category.assoc, HomologicalComplex.Hom.comm, Category.assoc]
  rfl

end
end Finsler.MultiFarSupportedCap
