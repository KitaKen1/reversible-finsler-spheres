module

public import Finsler.Topology.SupportedCapHomology
public import Finsler.Topology.SmallRetractionHomology

/-! Naturality in the actual neighborhood, using monicity only on chains.
The small-chain retraction is used naturally only after passing to homology. -/

@[expose] public section

namespace Finsler.SupportedCapNaturality

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def push {X Y : TopCat.{0}} (f : X ⟶ Y) : chains X ⟶ chains Y :=
  SSet.chainComplexMap (TopCat.toSSet.map f) coeff

theorem push_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    push (f ≫ g) = push f ≫ push g := by
  simp only [push, Functor.map_comp]

def restriction {X Y : TopCat.{0}} (f : X ⟶ Y) (B : Set X) (D : Set Y)
    (hf : Set.MapsTo f B D) : TopCat.of B ⟶ TopCat.of D :=
  TopCat.ofHom ⟨fun x => ⟨f x.val, hf x.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem restriction_inclusion {X Y : TopCat.{0}} (f : X ⟶ Y) (B : Set X) (D : Set Y)
    (hf : Set.MapsTo f B D) :
    restriction f B D hf ≫ subspaceMap Y D = subspaceMap X B ≫ f := by
  ext x : 1
  rfl

theorem restriction_push {X Y : TopCat.{0}} (f : X ⟶ Y) (B : Set X) (D : Set Y)
    (hf : Set.MapsTo f B D) :
    push (restriction f B D hf) ≫ push (subspaceMap Y D) =
      push (subspaceMap X B) ≫ push f := by
  rw [← push_comp, restriction_inclusion, push_comp]

theorem pullback_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : ℕ) (φ : singularCochainGroup (ZMod 2) Z p) :
    cochainPullback (f ≫ g) p φ = cochainPullback f p (cochainPullback g p φ) := by
  change (push (f ≫ g)).f p ≫ φ = (push f).f p ≫ ((push g).f p ≫ φ)
  rw [push_comp, HomologicalComplex.comp_f, Category.assoc]

theorem pullback_support {X Y : TopCat.{0}} (f : X ⟶ Y) (A : Set X) (C : Set Y)
    (hf : Set.MapsTo f A C) (p : ℕ) (φ : singularCochainGroup (ZMod 2) Y p)
    (hs : cochainPullback (subspaceMap Y C) p φ = 0) :
    cochainPullback (subspaceMap X A) p (cochainPullback f p φ) = 0 := by
  rw [← pullback_comp, ← restriction_inclusion f A C hf, pullback_comp, hs]
  change (push (restriction f A C hf)).f p ≫ 0 = 0
  exact comp_zero

def smallMap {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) :
    small X (cover X A B) ⟶ small Y (cover Y C D) :=
  SSet.chainComplexMap (X.smallSingularSubcomplexMap (cover X A B) (cover Y C D) f id
    (fun b => by cases b; exact hA; exact hB)) coeff

theorem smallMap_inclusion {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) :
    smallMap f A B C D hA hB ≫ inclusion Y (cover Y C D) =
      inclusion X (cover X A B) ≫ push f := by
  simpa only [smallMap, inclusion, push, Functor.map_comp] using
    congrArg (fun g => SSet.chainComplexMap g coeff)
      (TopCat.smallSingularSubcomplexMap_ι (cover X A B) (cover Y C D) f id
        (fun b => by cases b; exact hA; exact hB))

theorem localized_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) Y p)
    (hs : cochainPullback (subspaceMap Y C) p φ = 0) :
    (smallMap f A B C D hA hB).f n ≫ localizedCap Y C D p q n h φ hs =
      localizedCap X A B p q n h (cochainPullback f p φ)
        (pullback_support f A C hA p φ hs) ≫ (push (restriction f B D hB)).f q := by
  let s := smallMap f A B C D hA hB
  let j := push (subspaceMap Y D)
  haveI : Mono (j.f q) := subspacePush_mono Y D q
  apply (cancel_mono (j.f q)).mp
  change (s.f n ≫ localizedCap Y C D p q n h φ hs) ≫
      (push (subspaceMap Y D)).f q = _
  calc
    _ = s.f n ≫ ((inclusion Y (cover Y C D)).f n ≫ absoluteChain Y p q n h φ) := by
      rw [Category.assoc]
      exact congrArg (fun m => s.f n ≫ m) (localizedCap_inclusion Y C D p q n h φ hs)
    _ = (inclusion X (cover X A B)).f n ≫
        ((push f).f n ≫ absoluteChain Y p q n h φ) := by
      rw [← Category.assoc, ← HomologicalComplex.comp_f, smallMap_inclusion,
        HomologicalComplex.comp_f, Category.assoc]
    _ = (inclusion X (cover X A B)).f n ≫
        (absoluteChain X p q n h (cochainPullback f p φ) ≫ (push f).f q) := by
      exact congrArg (fun m => (inclusion X (cover X A B)).f n ≫ m)
        (RelativeCapBoundary.absolute_chain_natural f p q n h φ).symm
    _ = (localizedCap X A B p q n h (cochainPullback f p φ)
        (pullback_support f A C hA p φ hs) ≫ (push (subspaceMap X B)).f q) ≫
        (push f).f q := by
      rw [← Category.assoc]
      exact congrArg (fun m => m ≫ (push f).f q)
        (localizedCap_inclusion X A B p q n h (cochainPullback f p φ)
          (pullback_support f A C hA p φ hs)).symm
    _ = _ := by
      rw [Category.assoc, ← HomologicalComplex.comp_f, ← restriction_push f B D hB,
        HomologicalComplex.comp_f, ← Category.assoc]

theorem pullback_closed {X Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y p)
    (hc : cochainCoboundary (ZMod 2) Y p φ = 0) :
    cochainCoboundary (ZMod 2) X p (cochainPullback f p φ) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 Y) (singularCochainComplexZMod2.map f.op) p φ hc

def localizedOperation (X : TopCat.{0}) (A B : Set X) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (subspaceMap X A) p φ = 0)
    (hc : cochainCoboundary (ZMod 2) X p φ = 0) :
    DegreeLoweringHomology.Map (small X (cover X A B)) (chains (TopCat.of B)) p where
  component q := localizedCap X A B p q (p + q) rfl φ hs
  comm q := by
    convert localizedCap_boundary X A B p q (p + q) rfl φ hs hc using 1

theorem operation_factor (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q : ℕ) (φ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (subspaceMap X A) p φ = 0)
    (hc : cochainCoboundary (ZMod 2) X p φ = 0) :
    (SupportedCapHomology.operation X A B hA hB hcover p φ hs hc).homology q =
      HomologicalComplex.homologyMap (TauCeti.smallSingularRetraction coeff (cover X A B)
        (cover_open X A B hA hB) (cover_univ X A B hcover)) (p + q) ≫
        (localizedOperation X A B p φ hs hc).homology q := by
  let l := localizedOperation X A B p φ hs hc
  let r := TauCeti.smallSingularRetraction coeff (cover X A B)
    (cover_open X A B hA hB) (cover_univ X A B hcover)
  calc
    _ = (l.pre r).homology q := by
      apply DegreeLoweringHomology.Map.homology_eq_of_components
      intro k
      rfl
    _ = _ := l.pre_homology r q

theorem localized_homology_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (A B : Set X) (C D : Set Y) (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)
    (p q : ℕ) (φ : singularCochainGroup (ZMod 2) Y p)
    (hs : cochainPullback (subspaceMap Y C) p φ = 0)
    (hc : cochainCoboundary (ZMod 2) Y p φ = 0) :
    HomologicalComplex.homologyMap (smallMap f A B C D hA hB) (p + q) ≫
        (localizedOperation Y C D p φ hs hc).homology q =
      (localizedOperation X A B p (cochainPullback f p φ)
        (pullback_support f A C hA p φ hs) (pullback_closed f p φ hc)).homology q ≫
        HomologicalComplex.homologyMap (push (restriction f B D hB)) q := by
  let ly := localizedOperation Y C D p φ hs hc
  let lx := localizedOperation X A B p (cochainPullback f p φ)
    (pullback_support f A C hA p φ hs) (pullback_closed f p φ hc)
  calc
    _ = (ly.pre (smallMap f A B C D hA hB)).homology q := (ly.pre_homology _ q).symm
    _ = (lx.post (push (restriction f B D hB))).homology q := by
      apply DegreeLoweringHomology.Map.homology_eq_of_components
      intro k
      exact localized_naturality f A B C D hA hB p k (p + k) rfl φ hs
    _ = _ := lx.post_homology _ q

theorem homology_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (A B : Set X) (C D : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hcoverX : A ∪ B = Set.univ)
    (hC : IsOpen C) (hD : IsOpen D) (hcoverY : C ∪ D = Set.univ)
    (hfA : Set.MapsTo f A C) (hfB : Set.MapsTo f B D)
    (p q : ℕ) (φ : singularCochainGroup (ZMod 2) Y p)
    (hs : cochainPullback (subspaceMap Y C) p φ = 0)
    (hc : cochainCoboundary (ZMod 2) Y p φ = 0) :
    HomologicalComplex.homologyMap (push f) (p + q) ≫
        (SupportedCapHomology.operation Y C D hC hD hcoverY p φ hs hc).homology q =
      (SupportedCapHomology.operation X A B hA hB hcoverX p (cochainPullback f p φ)
        (pullback_support f A C hfA p φ hs) (pullback_closed f p φ hc)).homology q ≫
        HomologicalComplex.homologyMap (push (restriction f B D hfB)) q := by
  rw [operation_factor, operation_factor]
  have hr := SmallRetractionHomology.homology_naturality (cover X A B) (cover Y C D)
    (cover_open X A B hA hB) (cover_univ X A B hcoverX)
    (cover_open Y C D hC hD) (cover_univ Y C D hcoverY) f id
    (fun b => by cases b; exact hfA; exact hfB) (p + q)
  change HomologicalComplex.homologyMap (TauCeti.smallSingularRetraction coeff (cover X A B)
      (cover_open X A B hA hB) (cover_univ X A B hcoverX)) (p + q) ≫
      HomologicalComplex.homologyMap (smallMap f A B C D hfA hfB) (p + q) =
    HomologicalComplex.homologyMap (push f) (p + q) ≫
      HomologicalComplex.homologyMap (TauCeti.smallSingularRetraction coeff (cover Y C D)
        (cover_open Y C D hC hD) (cover_univ Y C D hcoverY)) (p + q) at hr
  rw [← Category.assoc, ← hr, Category.assoc,
    localized_homology_naturality f A B C D hfA hfB p q φ hs hc, ← Category.assoc]

end
end Finsler.SupportedCapNaturality

