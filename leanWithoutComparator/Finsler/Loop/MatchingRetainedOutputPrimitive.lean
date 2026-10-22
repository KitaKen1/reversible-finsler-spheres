module

public import Finsler.Loop.IntervalEquatorCohomologyGap
public import Finsler.Loop.ContinuousLoopHomologyEquivalence

/-! On the ENTIRE original nonadjacent matching locus, including
both meridian poles, every output class in degree n has zero absolute
pullback. Its actual strong-H1 retained cochain has a genuine global
primitive. Time-end support is deliberately not inferred from this. -/
@[expose] public section
namespace Finsler.MatchingRetainedOutputPrimitive
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def retainedH1 {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    NativeMeridianMatchingLoci.parameters P ⟶ Loops n :=
  TopCat.ofHom ⟨fun z => H1SelfCutNeighborhood.right
    (DiagonalSelfCutRepresentatives.intoTube (NativeMeridianMatchingLoci.intoDiagonal P v₀ b z)),
    H1SelfCutNeighborhood.continuous_right.comp
      ((DiagonalSelfCutRepresentatives.continuous_intoTube n).comp
        (NativeMeridianMatchingLoci.intoDiagonal P v₀ b).hom.continuous)⟩

theorem ordinary_comparison {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    retainedH1 P v₀ b ≫ ContinuousLoopModel.inclusion n = NativeMatchingRetainedFactors.retainedMap P v₀ b := by
  ext z : 1
  rfl

def reducedH1 {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.of (Finsler.IntervalSobolev.ClosedInterval × equator P) ⟶ Loops n :=
  TopCat.ofHom ⟨fun z => retainedH1 P v₀ 1 (z.1, (z.2, v₀)),
    (retainedH1 P v₀ 1).hom.continuous.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))⟩

theorem H1_factor {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    retainedH1 P v₀ 1 = NativeMatchingAdjacentFactors.reducedProjection P ≫ reducedH1 P v₀ := by
  ext z : 1
  apply ContinuousLoopModel.inclusion_injective n
  exact NativeMatchingRetainedFactors.nonadjacent_independent P v₀ z.2.1 z.2.2 v₀ z.1

theorem ordinary_class_zero (m q : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    (hq : 1 ≤ q) (hqm : q ≠ m) (B : cohomologyZMod2 (ContinuousLoopModel.space (m + 1)) q) :
    (cohPullback (NativeMatchingRetainedFactors.retainedMap P v₀ 1) q).hom B = 0 := by
  rw [NativeMatchingRetainedFactors.nonadjacent_factor, Finsler.Cup.pullback_comp]
  have hz := IntervalEquatorCohomologyGap.equator_zero m q P hq hqm
    ((cohPullback (NativeMatchingRetainedFactors.nonadjacent P v₀) q).hom B)
  rw [hz, map_zero]

theorem H1_class_zero (m q : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    (hq : 1 ≤ q) (hqm : q ≠ m) (B : cohomologyZMod2 (Loops (m + 1)) q) :
    (cohPullback (retainedH1 P v₀ 1) q).hom B = 0 := by
  obtain ⟨b, rfl⟩ := ContinuousLoopHomologyEquivalence.cohomology_surjective (m + 1) q B
  rw [← Finsler.Cup.pullback_comp, ordinary_comparison]
  exact ordinary_class_zero m q P v₀ hq hqm b

variable (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
  (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + 1))
  (hB : cochainCoboundary (ZMod 2) (Loops (m + 1)) (m + 1) B = 0)

def cochain : singularCochainGroup (ZMod 2) (NativeMeridianMatchingLoci.parameters P) (m + 1) :=
  cochainPullback (retainedH1 P v₀ 1) (m + 1) B

def reducedCochain : singularCochainGroup (ZMod 2) (TopCat.of (Finsler.IntervalSobolev.ClosedInterval × equator P)) (m + 1) :=
  cochainPullback (reducedH1 P v₀) (m + 1) B

include hB in
theorem reduced_closed : cochainCoboundary (ZMod 2) (TopCat.of (Finsler.IntervalSobolev.ClosedInterval × equator P)) (m + 1)
    (reducedCochain m P v₀ B) = 0 := pullback_closed _ _ B hB

include hB in
theorem reduced_class_zero : CochainClass.classOf
    (cochainCxZMod2 (TopCat.of (Finsler.IntervalSobolev.ClosedInterval × equator P))) (m + 1)
    (reducedCochain m P v₀ B) (reduced_closed m P v₀ B hB) = 0 :=
  IntervalEquatorCohomologyGap.equator_zero m (m + 1) P (by omega) (by omega) _

def reducedPrimitive : singularCochainGroup (ZMod 2) (TopCat.of (Finsler.IntervalSobolev.ClosedInterval × equator P)) m :=
  CochainClassExact.primitive (cochainCxZMod2 (TopCat.of (Finsler.IntervalSobolev.ClosedInterval × equator P))) (m + 1) (by omega)
    (reducedCochain m P v₀ B) 0 (reduced_closed m P v₀ B hB) (map_zero _)
    ((reduced_class_zero m P v₀ B hB).trans (CochainClass.classOf_zero _ _ (map_zero _)).symm)

theorem reducedPrimitive_d : cochainCoboundary (ZMod 2) (TopCat.of (Finsler.IntervalSobolev.ClosedInterval × equator P)) m
    (reducedPrimitive m P v₀ B hB) = reducedCochain m P v₀ B := by
  have he := CochainClassExact.primitive_d (cochainCxZMod2 (TopCat.of (Finsler.IntervalSobolev.ClosedInterval × equator P))) (m + 1) (by omega)
    (reducedCochain m P v₀ B) 0 (reduced_closed m P v₀ B hB) (map_zero _)
    ((reduced_class_zero m P v₀ B hB).trans (CochainClass.classOf_zero _ _ (map_zero _)).symm)
  exact he.trans (sub_zero _)

include hB in
theorem closed : cochainCoboundary (ZMod 2) (NativeMeridianMatchingLoci.parameters P) (m + 1) (cochain m P v₀ B) = 0 :=
  pullback_closed _ _ B hB

include hB in
theorem class_zero : CochainClass.classOf (cochainCxZMod2 (NativeMeridianMatchingLoci.parameters P)) (m + 1)
    (cochain m P v₀ B) (closed m P v₀ B hB) = 0 := by
  have he := cohPullback_cocycleClass (retainedH1 P v₀ 1) (m + 1) B hB
  exact he.symm.trans (H1_class_zero m (m + 1) P v₀ (by omega) (by omega) (cocycleClass _ (m + 1) B hB))

def primitive : singularCochainGroup (ZMod 2) (NativeMeridianMatchingLoci.parameters P) m :=
  cochainPullback (NativeMatchingAdjacentFactors.reducedProjection P) m (reducedPrimitive m P v₀ B hB)

theorem primitive_d : cochainCoboundary (ZMod 2) (NativeMeridianMatchingLoci.parameters P) m
    (primitive m P v₀ B hB) = cochain m P v₀ B := by
  have he := SmallChainPrimitiveCorrection.pullback_boundary (NativeMatchingAdjacentFactors.reducedProjection P) m (m + 1)
    (reducedPrimitive m P v₀ B hB)
  change cochainCoboundary (ZMod 2) (NativeMeridianMatchingLoci.parameters P) m (primitive m P v₀ B hB) =
    cochainPullback _ (m + 1) (cochainCoboundary (ZMod 2) _ m (reducedPrimitive m P v₀ B hB)) at he
  rw [reducedPrimitive_d, reducedCochain, ← pullback_comp, ← H1_factor] at he
  exact he

end
end Finsler.MatchingRetainedOutputPrimitive
