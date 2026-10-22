module

public import Finsler.Topology.FirstHalfInteriorTestedCap

/-! Identify the actual interior first-half domain with the native
annular cut neighborhood, its original tested cocycle and its retained
map. These identities precede passage to homology or any global cut/join
interchange assertion. -/

@[expose] public section
namespace Finsler.FirstHalfInteriorNative

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.H1SelfCutNeighborhood Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.FirstHalfInteriorFamily

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {X : Type} [TopologicalSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

def toCut (r : ℝ) : TopCat.of (domain u a ha ha1 r) ⟶ TopCat.of (neighborhood n r) := by
  refine TopCat.ofHom ⟨fun z => ⟨CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u)
    a ha.le ha1.le z.val, ?_⟩, ?_⟩
  · change distance n (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le z.val) < r
    rw [FirstHalfInteriorPrism.distance_trimmed]
    exact z.property
  · exact ((CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u)
      a ha.le ha1.le).hom.continuous.comp continuous_subtype_val).subtype_mk _

variable {r : ℝ} (hr : r ≤ 1)

theorem nativeTube (z : domain u a ha ha1 r) :
    SupportedSelfCut.toTube n hr (toCut u a ha ha1 r z) =
      FirstHalfJoinedCut.joinedTube (input u a ha ha1 hr z) := by
  apply Subtype.ext
  exact (FirstHalfInteriorFamily.joinedTube_parameters u a ha ha1 hr z).symm

def originalRetainedMap : TopCat.of (domain u a ha ha1 r) ⟶ TopCat.of (SphereLoop n) :=
  TopCat.ofHom ((FirstHalfFixedOutput.originalMap (n := n)).comp (input u a ha ha1 hr))

theorem tested_native :
    toCut u a ha ha1 r ≫ TopCat.ofHom (SupportedSelfCut.tested n hr) =
      FirstHalfInteriorTested.sourceMap u a ha ha1 hr := by
  apply TopCat.ext
  intro z
  change left (SupportedSelfCut.toTube n hr (toCut u a ha ha1 r z)) =
    (family u a ha ha1 hr (0, z)).1
  rw [nativeTube, FirstHalfInteriorFamily.tested_fixed]
  exact FirstHalfJoinedCut.tested_eq (input u a ha ha1 hr z)

theorem retained_native :
    toCut u a ha ha1 r ≫ TopCat.ofHom (SupportedSelfCut.retained n hr) =
      originalRetainedMap u a ha ha1 hr := by
  apply TopCat.ext
  intro z
  change right (SupportedSelfCut.toTube n hr (toCut u a ha ha1 r z)) =
    right (FirstHalfJoinedCut.joinedTube (input u a ha ha1 hr z))
  rw [nativeTube]

theorem filteredDomain_eq_native (F : ReversibleMetric n) (A : ℝ) :
    filteredDomain u a ha ha1 hr F A =
      {z : domain u a ha ha1 r | SobolevLength.length F (SupportedSelfCut.retained n hr (toCut u a ha ha1 r z)) < A} := by
  ext z
  change SobolevLength.length F (right (FirstHalfJoinedCut.joinedTube (input u a ha ha1 hr z))) < A ↔
    SobolevLength.length F (right (SupportedSelfCut.toTube n hr (toCut u a ha ha1 r z))) < A
  rw [nativeTube]

theorem tested_cochain_native (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback (toCut u a ha ha1 r) p (NormalizedSelfCut.testedCocycle n p hr T) =
      cochainPullback (FirstHalfInteriorTested.sourceMap u a ha ha1 hr) p T := by
  rw [NormalizedSelfCut.testedCocycle, ← pullback_comp, tested_native]

def filteredNative (F : ReversibleMetric n) (A : ℝ) :
    TopCat.of (filteredDomain u a ha ha1 hr F A) ⟶ TopCat.of (neighborhood n r) :=
  SupportedCap.subspaceMap (TopCat.of (domain u a ha ha1 r)) (filteredDomain u a ha ha1 hr F A) ≫
    toCut u a ha ha1 r

theorem filtered_cochain_native (F : ReversibleMetric n) (A : ℝ) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback (filteredNative u a ha ha1 hr F A) p (NormalizedSelfCut.testedCocycle n p hr T) =
      FirstHalfInteriorTestedCap.cochain u a ha ha1 hr F A p T := by
  dsimp only [filteredNative, FirstHalfInteriorTestedCap.cochain, FirstHalfInteriorTestedCap.testedMap]
  rw [pullback_comp, tested_cochain_native, pullback_comp]

end
end Finsler.FirstHalfInteriorNative
