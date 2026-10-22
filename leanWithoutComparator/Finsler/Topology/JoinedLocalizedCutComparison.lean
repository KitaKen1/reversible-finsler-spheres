module

public import Finsler.Topology.JoinedFamilyNaturality
public import Finsler.Topology.SupportedDoubleCapNaturality
public import Finsler.Topology.DoubleCapCoverComparison

/-! On an actual refinement of a genuine joined-family far/domain cover,
the original localized supported tested cap is precisely the actual
domain component of the successive ambient caps, followed by toCut.
The full original cut still has its separate small-chain retraction. -/

@[expose] public section
namespace Finsler.JoinedLocalizedCutComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedFamilyNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
  (ρ r : ℝ) (i : Fin 3)

theorem local_naturality (k p q N : ℕ) (hN : k + (p + q) = N)
    (φ : singularCochainGroup (ZMod 2) (parameters n) k)
    (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood n r)) p) :
    (smallMap (globalMap u a ha ha1 i)
      (JoinedRectangleRefinement.far u a ha ha1 ρ i)
      (domain (tube X) (family u a ha ha1) (fun _ => r) i)
      (exterior n ρ) (neighborhood n r)
      (far_maps u a ha ha1 ρ i) (domain_maps u a ha ha1 r i)).f N ≫
        SupportedDoubleCap.localized (parameters n) (exterior n ρ) (neighborhood n r)
          k p φ hφ ψ q N hN =
      SupportedDoubleCap.localized (TopCat.of (Outer X))
        (JoinedRectangleRefinement.far u a ha ha1 ρ i)
        (domain (tube X) (family u a ha ha1) (fun _ => r) i) k p
        (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ)
        (JoinedCochainBoundary.extension_far_zero u a ha ha1 ρ i k φ hφ)
        (cochainPullback (toCut (tube X) (family u a ha ha1) (fun _ => r) i) p ψ) q N hN ≫
          (push (toCut (tube X) (family u a ha ha1) (fun _ => r) i)).f q := by
  have hn := SupportedDoubleCapNaturality.localized_naturality (globalMap u a ha ha1 i)
    (JoinedRectangleRefinement.far u a ha ha1 ρ i)
    (domain (tube X) (family u a ha ha1) (fun _ => r) i)
    (exterior n ρ) (neighborhood n r)
    (far_maps u a ha ha1 ρ i) (domain_maps u a ha ha1 r i) k p q N hN φ hφ ψ
  simpa only [← extension_eq_pullback, restriction_eq_toCut] using hn

variable {ι : Type*} (W : ι → Set (Outer X))
  (hW : ∀ j, W j ⊆ JoinedRectangleRefinement.far u a ha ha1 ρ i ∨
    W j ⊆ domain (tube X) (family u a ha ha1) (fun _ => r) i)

def familySmallMap : small (TopCat.of (Outer X)) W ⟶
    small (parameters n) (SupportedCap.cover (parameters n) (exterior n ρ) (neighborhood n r)) :=
  SmallCoverRefinement.map (TopCat.of (Outer X)) W
    (SupportedCap.cover (TopCat.of (Outer X))
      (JoinedRectangleRefinement.far u a ha ha1 ρ i)
      (domain (tube X) (family u a ha ha1) (fun _ => r) i))
    (fun j => by rcases hW j with h | h; exact ⟨false, h⟩; exact ⟨true, h⟩) ≫
    smallMap (globalMap u a ha ha1 i)
      (JoinedRectangleRefinement.far u a ha ha1 ρ i)
      (domain (tube X) (family u a ha ha1) (fun _ => r) i)
      (exterior n ρ) (neighborhood n r)
      (far_maps u a ha ha1 ρ i) (domain_maps u a ha ha1 r i)

theorem familySmallMap_inclusion :
    familySmallMap u a ha ha1 ρ r i W hW ≫
      inclusion (parameters n) (SupportedCap.cover (parameters n) (exterior n ρ) (neighborhood n r)) =
      inclusion (TopCat.of (Outer X)) W ≫ push (globalMap u a ha ha1 i) := by
  unfold familySmallMap
  rw [Category.assoc, smallMap_inclusion, ← Category.assoc, SmallCoverRefinement.map_inclusion]

theorem domain_agreement (k p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) (parameters n) k)
    (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood n r)) p)
    (c : (small (TopCat.of (Outer X)) W).X (k + (p + q)) ⟶
      (chains (TopCat.of (domain (tube X) (family u a ha ha1) (fun _ => r) i))).X q)
    (hc : c ≫ (push (SupportedCap.subspaceMap (TopCat.of (Outer X))
        (domain (tube X) (family u a ha ha1) (fun _ => r) i))).f q =
      (inclusion (TopCat.of (Outer X)) W).f (k + (p + q)) ≫
        PartialDoubleCap.cap (TopCat.of (Outer X)) k p q
          (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ)
          (TubeCochainExtension.extend (TopCat.of (Outer X))
            (domain (tube X) (family u a ha ha1) (fun _ => r) i) p
            (cochainPullback (toCut (tube X) (family u a ha ha1) (fun _ => r) i) p ψ))) :
    (familySmallMap u a ha ha1 ρ r i W hW).f (k + (p + q)) ≫
      SupportedDoubleCap.localized (parameters n) (exterior n ρ) (neighborhood n r)
        k p φ hφ ψ q (k + (p + q)) rfl =
      c ≫ (push (toCut (tube X) (family u a ha ha1) (fun _ => r) i)).f q := by
  unfold familySmallMap
  rw [HomologicalComplex.comp_f, Category.assoc, local_naturality, ← Category.assoc]
  rw [DoubleCapCoverComparison.agreement_of_domain_lift (TopCat.of (Outer X)) W
    (JoinedRectangleRefinement.far u a ha ha1 ρ i)
    (domain (tube X) (family u a ha ha1) (fun _ => r) i) hW k p
    (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ)
    (JoinedCochainBoundary.extension_far_zero u a ha ha1 ρ i k φ hφ)
    (cochainPullback (toCut (tube X) (family u a ha ha1) (fun _ => r) i) p ψ) q c hc]

theorem tested_pullback (hr : r ≤ 1) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback (toCut (tube X) (family u a ha ha1) (fun _ => r) i) p
      (NormalizedSelfCut.testedCocycle n p hr T) =
      cochainPullback (testedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i) p T := by
  rw [NormalizedSelfCut.testedCocycle, ← pullback_comp]
  rfl

theorem output_agreement (hr : r ≤ 1) (k p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) (parameters n) k)
    (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (c : (small (TopCat.of (Outer X)) W).X (k + (p + q)) ⟶
      (chains (TopCat.of (domain (tube X) (family u a ha ha1) (fun _ => r) i))).X q)
    (hc : c ≫ (push (SupportedCap.subspaceMap (TopCat.of (Outer X))
        (domain (tube X) (family u a ha ha1) (fun _ => r) i))).f q =
      (inclusion (TopCat.of (Outer X)) W).f (k + (p + q)) ≫
        PartialDoubleCap.cap (TopCat.of (Outer X)) k p q
          (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ)
          (testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i p T)) :
    (familySmallMap u a ha ha1 ρ r i W hW).f (k + (p + q)) ≫
      SupportedDoubleCap.localized (parameters n) (exterior n ρ) (neighborhood n r)
        k p φ hφ (NormalizedSelfCut.testedCocycle n p hr T) q (k + (p + q)) rfl ≫
        (push (TopCat.ofHom (retained n hr))).f q =
      c ≫ (push (retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i)).f q := by
  have he := tested_pullback u a ha ha1 r i hr p T
  have hh := domain_agreement u a ha ha1 ρ r i W hW k p q φ hφ
    (NormalizedSelfCut.testedCocycle n p hr T) c
    (by simpa only [he, testedExtension] using hc)
  rw [← Category.assoc, hh, Category.assoc, ← HomologicalComplex.comp_f, ← push_comp]
  rfl

end
end Finsler.JoinedLocalizedCutComparison
