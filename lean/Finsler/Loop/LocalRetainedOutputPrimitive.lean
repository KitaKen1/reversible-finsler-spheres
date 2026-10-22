module

public import Finsler.Loop.LocalNativeBallSlice
public import Finsler.Loop.ConstantRelativeOutputCochain
public import Finsler.Loop.ContinuousLoopHomologyEquivalence
public import Finsler.Topology.CochainClassExact

/-! On the ACTUAL nonadjacent whole-ball cut chart, EVERY positive
output class pulls back to zero. The true retained factor is constant
on the remaining-factor center slice. The ORIGINAL H1 output cochain
therefore has a genuine primitive, without an H_n loop rank premise.
This is local; global boundary/support compatibility is still required. -/
@[expose] public section
namespace Finsler.LocalRetainedOutputPrimitive
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem slice_constant {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    LocalNativeBallCut.retainedSlice P v₀ 1 =
      TopCat.ofHom (ContinuousMap.const (equator P)
        (NativeMatchingRetainedFactors.retainedMap P v₀ 1 (LocalNativeBallSlice.centerTime P v₀, (LocalNativeBallSlice.centerDirection P v₀, v₀)))) := by
  rw [LocalNativeBallSlice.retainedSlice_matching]
  exact NativeMatchingTestedPairing.middle_retained_constant P v₀ _ _

theorem ordinary_class_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) (hq : q ≠ 0)
    (B : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (LocalNativeBallCut.retained P v₀ 1) q).hom B = 0 := by
  have hz := NativeMatchingTestedPairing.constant_pullback_zero (TopCat.of (equator P)) (ContinuousLoopModel.space n)
    (NativeMatchingRetainedFactors.retainedMap P v₀ 1 (LocalNativeBallSlice.centerTime P v₀, (LocalNativeBallSlice.centerDirection P v₀, v₀))) q hq B
  rw [LocalNativeBallCut.retained_reduced, slice_constant, hz, map_zero]

theorem H1_class_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) (hq : q ≠ 0)
    (B : cohomologyZMod2 (Loops n) q) :
    (cohPullback (LocalNativeBallCut.retainedH1 P v₀ 1) q).hom B = 0 := by
  obtain ⟨b, rfl⟩ := ContinuousLoopHomologyEquivalence.cohomology_surjective n q B
  rw [← NativeMatchingTransgression.pullback_comp]
  exact ordinary_class_zero P v₀ q hq b

variable {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
  (B : singularCochainGroup (ZMod 2) (Loops n) q)
  (hB : cochainCoboundary (ZMod 2) (Loops n) q B = 0)

def cocycle : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) q :=
  cochainPullback (LocalNativeBallCut.retainedH1 P v₀ 1) q B

include hB in
theorem closed : cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) q (cocycle P v₀ q B) = 0 :=
  pullback_closed _ _ B hB

include hB in
theorem class_zero (hq : q ≠ 0) :
    CochainClass.classOf (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) q (cocycle P v₀ q B) (closed P v₀ q B hB) = 0 := by
  have he := cohPullback_cocycleClass (LocalNativeBallCut.retainedH1 P v₀ 1) q B hB
  exact he.symm.trans (H1_class_zero P v₀ q hq (cocycleClass _ q B hB))

def primitive (hq : 1 ≤ q) : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) (q - 1) :=
  CochainClassExact.primitive (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) q hq
    (cocycle P v₀ q B) 0 (closed P v₀ q B hB) (map_zero _)
    ((class_zero P v₀ q B hB (by omega)).trans (CochainClass.classOf_zero _ q (map_zero _)).symm)

theorem primitive_d (hq : 1 ≤ q) :
    ((cochainCxZMod2 (LocalNativeBallCut.space P v₀)).d (q - 1) q).hom (primitive P v₀ q B hB hq) = cocycle P v₀ q B := by
  have he := CochainClassExact.primitive_d (cochainCxZMod2 (LocalNativeBallCut.space P v₀)) q hq
    (cocycle P v₀ q B) 0 (closed P v₀ q B hB) (map_zero _)
    ((class_zero P v₀ q B hB (by omega)).trans (CochainClass.classOf_zero _ q (map_zero _)).symm)
  exact he.trans (sub_zero _)

end
end Finsler.LocalRetainedOutputPrimitive
