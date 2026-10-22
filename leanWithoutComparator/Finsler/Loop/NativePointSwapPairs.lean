module

public import Finsler.Loop.NativeWrappedQuarterSupport
public import Finsler.Loop.NativeGraphPointSwapClass

/-! The real native/graph point exchanges commute with the ACTUAL
support map of pairs and are genuine involutions, including relative
cohomology. These are geometric pair squares, not assumed corrections. -/
@[expose] public section
namespace Finsler.NativePointSwapPairs
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativeMeridianPairCoordinates
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

theorem subsetMap_congr {X Y : TopCat.{0}} {A : Set X} {B : Set Y} (f g : X ⟶ Y)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (h : f = g) :
    TopPair.ofSubsetMap f hf = TopPair.ofSubsetMap g hg := by
  subst g
  rfl

theorem subset_square {X Y : TopCat.{0}} {A : Set X} {B : Set Y}
    (s : X ⟶ X) (t : Y ⟶ Y) (f : X ⟶ Y)
    (hs : Set.MapsTo s A A) (ht : Set.MapsTo t B B) (hf : Set.MapsTo f A B) (h : s ≫ f = f ≫ t) :
    TopPair.ofSubsetMap s hs ≫ TopPair.ofSubsetMap f hf = TopPair.ofSubsetMap f hf ≫ TopPair.ofSubsetMap t ht := by
  have hl := TopPair.ofSubsetMap_comp s f hs hf (fun x hx => hf (hs hx))
  have hr := TopPair.ofSubsetMap_comp f t hf ht (fun x hx => ht (hf hx))
  exact hl.symm.trans ((subsetMap_congr (s ≫ f) (f ≫ t) _ _ h).trans hr)

theorem subset_involution {X : TopCat.{0}} {A : Set X} (f : X ⟶ X) (hf : Set.MapsTo f A A)
    (h : f ≫ f = 𝟙 X) : TopPair.ofSubsetMap f hf ≫ TopPair.ofSubsetMap f hf = 𝟙 (TopPair.ofSubset A) := by
  have hc := TopPair.ofSubsetMap_comp f f hf hf (fun x hx => hf (hf hx))
  have he := subsetMap_congr (f ≫ f) (𝟙 X) (fun x hx => hf (hf hx)) (fun _ hx => hx) h
  exact hc.symm.trans (he.trans (TopPair.ofSubsetMap_id (fun _ hx => hx)))

theorem native_graph_square {n : ℕ} (P : Sphere n) :
    NativeCutPointSwap.nativeSwap P ≫ sphereCoordinates P = sphereCoordinates P ≫ NativeCutPointSwap.graphSwap P := rfl

theorem native_support_square {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativeWrappedQuarterSupport.nativePairSwap P v₀ ≫ NativeQuarterGraphDescent.supportMap P v₀ =
      NativeQuarterGraphDescent.supportMap P v₀ ≫ NativeCutPointSwap.graphPairSwap P v₀ := by
  exact subset_square (A := (NativeQuarterSupport.good P v₀)ᶜ) (B := (NativeQuarterGraphPatch.graphGood P v₀)ᶜ)
    (NativeCutPointSwap.nativeSwap P) (NativeCutPointSwap.graphSwap P) (sphereCoordinates P)
    (fun z hz hg => hz ((NativeCutPointSwap.native_good P v₀ z).mp hg))
    (fun z hz hg => hz ((NativeCutPointSwap.graph_good P v₀ z).mp hg))
    (NativeQuarterGraphPatch.maps_support P v₀) (native_graph_square P)

theorem nativePairSwap_involution {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativeWrappedQuarterSupport.nativePairSwap P v₀ ≫ NativeWrappedQuarterSupport.nativePairSwap P v₀ =
      𝟙 (NativeQuarterSupport.supportPair P v₀) := by
  exact subset_involution (A := (NativeQuarterSupport.good P v₀)ᶜ) (NativeCutPointSwap.nativeSwap P)
    (fun z hz hg => hz ((NativeCutPointSwap.native_good P v₀ z).mp hg)) (NativeCutPointSwap.native_involution P)

theorem graphPairSwap_involution {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativeCutPointSwap.graphPairSwap P v₀ ≫ NativeCutPointSwap.graphPairSwap P v₀ =
      𝟙 (NativeQuarterGraphDescent.graphSupportPair P v₀) := by
  exact subset_involution (A := (NativeQuarterGraphPatch.graphGood P v₀)ᶜ) (NativeCutPointSwap.graphSwap P)
    (fun z hz hg => hz ((NativeCutPointSwap.graph_good P v₀ z).mp hg)) (NativeCutPointSwap.graph_involution P)

theorem graphPairSwap_fst {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopPair.Hom.fst (NativeCutPointSwap.graphPairSwap P v₀) = NativeCutPointSwap.graphSwap P := by
  apply TopCat.ext
  intro z
  exact TopPair.ofSubsetMap_fst_apply (B := (NativeQuarterGraphPatch.graphGood P v₀)ᶜ)
    (B' := (NativeQuarterGraphPatch.graphGood P v₀)ᶜ) (NativeCutPointSwap.graphSwap P)
    (fun x hx hg => hx ((NativeCutPointSwap.graph_good P v₀ x).mp hg)) z

theorem cohomology_involution (Q : TopPair.{0}) (f : Q ⟶ Q) (h : f ≫ f = 𝟙 Q) (q : ℕ)
    (a : Q.singularCohomology coeff (ZMod 2) coeff q) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f q).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f q).hom a) = a := by
  have he := congrArg (fun g => TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) g q) h
  rw [TopPair.singularCohomologyMap_comp, TopPair.singularCohomologyMap_id] at he
  exact ConcreteCategory.congr_hom he a

theorem support_pullback_exchange {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (a : (NativeQuarterGraphDescent.graphSupportPair P v₀).singularCohomology coeff (ZMod 2) coeff q) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeQuarterGraphDescent.supportMap P v₀) q).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeCutPointSwap.graphPairSwap P v₀) q).hom a) =
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeWrappedQuarterSupport.nativePairSwap P v₀) q).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeQuarterGraphDescent.supportMap P v₀) q).hom a) := by
  have he := congrArg (fun f => TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f q)
    (native_support_square P v₀)
  rw [TopPair.singularCohomologyMap_comp, TopPair.singularCohomologyMap_comp] at he
  exact (ConcreteCategory.congr_hom he a).symm

end
end Finsler.NativePointSwapPairs
