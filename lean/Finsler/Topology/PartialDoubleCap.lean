module

public import Finsler.Topology.CarrierSubspaceFactor

/-! Actual successive caps lift through a genuine partial-map domain
when each nonzero whole parent lies there. If the whole parent also has
a target bound, the actual partial-map output factors through that
subspace. No global closure of the zero-extended cochains is assumed. -/

@[expose] public section
namespace Finsler.PartialDoubleCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def cap (X : TopCat.{0}) (k p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p) :
    (chains X).X (k + (p + q)) ⟶ (chains X).X q :=
  absoluteChain X k (p + q) (k + (p + q)) rfl φ ≫
    absoluteChain X p q (p + q) rfl ψ

theorem cap_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (k p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y k) (ψ : singularCochainGroup (ZMod 2) Y p) :
    cap X k p q (cochainPullback f k φ) (cochainPullback f p ψ) ≫ (push f).f q =
      (push f).f (k + (p + q)) ≫ cap Y k p q φ ψ := by
  unfold cap
  have h₁ := RelativeCapBoundary.absolute_chain_natural f k (p + q) (k + (p + q)) rfl φ
  have h₂ := RelativeCapBoundary.absolute_chain_natural f p q (p + q) rfl ψ
  change absoluteChain X k (p + q) (k + (p + q)) rfl (cochainPullback f k φ) ≫
    (absoluteChain X p q (p + q) rfl (cochainPullback f p ψ) ≫ (push f).f q) = _
  rw [show absoluteChain X p q (p + q) rfl (cochainPullback f p ψ) ≫ (push f).f q =
    (push f).f (p + q) ≫ absoluteChain Y p q (p + q) rfl ψ from h₂]
  rw [← Category.assoc]
  rw [show absoluteChain X k (p + q) (k + (p + q)) rfl (cochainPullback f k φ) ≫
    (push f).f (p + q) = (push f).f (k + (p + q)) ≫
      absoluteChain Y k (p + q) (k + (p + q)) rfl φ from h₁]
  rw [Category.assoc]

theorem lifted_simplex_inclusion (X : TopCat.{0}) (D : Set X) (k p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
    (σ : TopCat.toSSet.obj X _⦋k + (p + q)⦌)
    (hD : Set.range (X.toSSetObjEquiv _ σ) ⊆ D) :
    ((TopCat.toSSet.obj (TopCat.of D)).ιChainComplex (SupportedCap.simplexLift X D σ hD) ≫
      cap (TopCat.of D) k p q (cochainPullback (SupportedCap.subspaceMap X D) k φ)
        (cochainPullback (SupportedCap.subspaceMap X D) p ψ)) ≫
        (push (SupportedCap.subspaceMap X D)).f q =
      (TopCat.toSSet.obj X).ιChainComplex σ ≫ cap X k p q φ ψ := by
  rw [Category.assoc, cap_natural, ← Category.assoc, push, SSet.ι_chainComplexMap_f,
    SupportedCap.simplexLift_image]

theorem exists_localized_simplex (X : TopCat.{0}) (D : Set X) (k p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
    (σ : TopCat.toSSet.obj X _⦋k + (p + q)⦌)
    (hgood : (TopCat.toSSet.obj X).ιChainComplex σ ≫ cap X k p q φ ψ ≠ 0 →
      Set.range (X.toSSetObjEquiv _ σ) ⊆ D) :
    ∃ c : coeff ⟶ (chains (TopCat.of D)).X q,
      c ≫ (push (SupportedCap.subspaceMap X D)).f q =
        (TopCat.toSSet.obj X).ιChainComplex σ ≫ cap X k p q φ ψ := by
  classical
  by_cases hz : (TopCat.toSSet.obj X).ιChainComplex σ ≫ cap X k p q φ ψ = 0
  · exact ⟨0, by rw [zero_comp, hz]⟩
  exact ⟨_, lifted_simplex_inclusion X D k p q φ ψ σ (hgood hz)⟩

theorem lifted_parent (X : TopCat.{0}) (D : Set X) {N : ℕ}
    (σ : TopCat.toSSet.obj X _⦋N⦌) (hD : Set.range (X.toSSetObjEquiv _ σ) ⊆ D)
    (z : D) (hz : z ∈ Set.range ((TopCat.of D).toSSetObjEquiv _ (SupportedCap.simplexLift X D σ hD))) :
    z.val ∈ Set.range (X.toSSetObjEquiv _ σ) := by
  obtain ⟨t, ht⟩ := hz
  refine ⟨t, ?_⟩
  have he := congrArg (fun τ => X.toSSetObjEquiv _ τ t) (SupportedCap.simplexLift_image X D σ hD)
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at he
  exact he.symm.trans (congrArg Subtype.val ht)

theorem exists_filtered_simplex {X Y : TopCat.{0}} (D : Set X) (f : TopCat.of D ⟶ Y)
    (B : Set Y) (k p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
    (σ : TopCat.toSSet.obj X _⦋k + (p + q)⦌)
    (hgood : (TopCat.toSSet.obj X).ιChainComplex σ ≫ cap X k p q φ ψ ≠ 0 →
      ∀ z ∈ Set.range (X.toSSetObjEquiv _ σ), ∃ hz : z ∈ D, f ⟨z, hz⟩ ∈ B) :
    ∃ (c : coeff ⟶ (chains (TopCat.of D)).X q) (d : coeff ⟶ (chains (TopCat.of B)).X q),
      (c ≫ (push (SupportedCap.subspaceMap X D)).f q =
        (TopCat.toSSet.obj X).ιChainComplex σ ≫ cap X k p q φ ψ) ∧
      (d ≫ (push (SupportedCap.subspaceMap Y B)).f q = c ≫ (push f).f q) := by
  classical
  by_cases hz : (TopCat.toSSet.obj X).ιChainComplex σ ≫ cap X k p q φ ψ = 0
  · exact ⟨0, 0, by rw [zero_comp, hz], by rw [zero_comp, zero_comp]⟩
  have hD : Set.range (X.toSSetObjEquiv _ σ) ⊆ D := fun z hz' => (hgood hz z hz').choose
  let τ := SupportedCap.simplexLift X D σ hD
  let c := (TopCat.toSSet.obj (TopCat.of D)).ιChainComplex τ ≫ cap (TopCat.of D) k p q
    (cochainPullback (SupportedCap.subspaceMap X D) k φ)
    (cochainPullback (SupportedCap.subspaceMap X D) p ψ)
  have hc : c ∈ supported (TopCat.of D) (parentFamily.{1} τ) q :=
    SmallCapCarrier.cap_preserves (parentFamily.{1} τ) p q (p + q) rfl _
      (SmallCapCarrier.cap_parent k (p + q) (k + (p + q)) rfl _ τ)
  have hf : ∀ i : PUnit.{1}, Set.MapsTo f (parentFamily τ i) B := by
    intro i z hz'
    have hzp := lifted_parent X D σ hD z hz'
    exact (hgood hz z.val hzp).choose_spec
  obtain ⟨d, hd⟩ := CarrierSubspaceFactor.push_factor (parentFamily.{1} τ) f B hf hc
  exact ⟨c, d, lifted_simplex_inclusion X D k p q φ ψ σ hD, hd⟩

section
variable (X : TopCat.{0}) {ι : Type*} (W : ι → Set X) (D : Set X) (k p : ℕ)
  (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
  (hgood : ∀ q (σ : (X.smallSingularSubcomplex W : SSet) _⦋k + (p + q)⦌),
    (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ cap X k p q φ ψ ≠ 0 →
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ D)

def localized (q : ℕ) : (small X W).X (k + (p + q)) ⟶ (chains (TopCat.of D)).X q :=
  Cofan.IsColimit.desc ((X.smallSingularSubcomplex W : SSet).isColimitChainComplexXCofan coeff (k + (p + q)))
    fun σ => (exists_localized_simplex X D k p q φ ψ σ.val (hgood q σ)).choose

theorem localized_inclusion (q : ℕ) :
    localized X W D k p φ ψ hgood q ≫ (push (SupportedCap.subspaceMap X D)).f q =
      (inclusion X W).f (k + (p + q)) ≫ cap X k p q φ ψ := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex W : SSet)) (R := coeff)
  intro σ
  have he : (X.smallSingularSubcomplex W : SSet).ιChainComplex σ ≫ localized X W D k p φ ψ hgood q =
      (exists_localized_simplex X D k p q φ ψ σ.val (hgood q σ)).choose := Cofan.IsColimit.fac _ _ σ
  rw [← Category.assoc, he]
  simpa only [inclusion, push, SSet.ι_chainComplexMap_f_assoc,
    Subfunctor.ι_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply] using
    (exists_localized_simplex X D k p q φ ψ σ.val (hgood q σ)).choose_spec

end
end
end Finsler.PartialDoubleCap
