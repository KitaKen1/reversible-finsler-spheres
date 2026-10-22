module

public import Finsler.Loop.NativeSequentialTripleComparison
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-! Explicit ORIGINAL singular-prism primitives for BOTH actual
sequential-to-common TRIPLE comparisons. For every closed actual test
cochain the difference is a genuine source coboundary; every actual
source cycle gives equal values. The source primitive is RETAINED for
future whole-parent cap/subdivision and relative-seam gluing. -/
@[expose] public section
namespace Finsler.NativeSequentialTriplePrism
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

section General
variable {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)

def prism (q : ℕ) := (H.toSSet.chainComplexMap coeff).hom q (q + 1)

theorem prism_boundary (q : ℕ) :
    (push f).f (q + 1) - (push g).f (q + 1) =
      (chains X).d (q + 1) q ≫ prism H q + prism H (q + 1) ≫ (chains Y).d (q + 2) (q + 1) := by
  let K := H.toSSet.chainComplexMap coeff
  have h := K.comm (q + 1)
  have he : (chains X).d (q + 1) q ≫ K.hom q (q + 1) +
      K.hom (q + 1) (q + 2) ≫ (chains Y).d (q + 2) (q + 1) =
      (push f).f (q + 1) - (push g).f (q + 1) := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, push] using h.symm
  exact he.symm

def primitive (q : ℕ) (T : singularCochainGroup (ZMod 2) Y (q + 1)) :
    singularCochainGroup (ZMod 2) X q := prism H q ≫ T

theorem primitive_boundary (q : ℕ) (T : singularCochainGroup (ZMod 2) Y (q + 1))
    (hT : cochainCoboundary (ZMod 2) Y (q + 1) T = 0) :
    cochainCoboundary (ZMod 2) X q (primitive H q T) =
      cochainPullback f (q + 1) T - cochainPullback g (q + 1) T := by
  have h := congrArg (fun k => k ≫ T) (prism_boundary H q)
  change (chains Y).d (q + 2) (q + 1) ≫ T = 0 at hT
  simp only [Preadditive.sub_comp, Preadditive.add_comp, Category.assoc, hT, comp_zero, add_zero] at h
  exact h.symm

include H in
theorem cycle_values_equal (q : ℕ) (T : singularCochainGroup (ZMod 2) Y (q + 1))
    (hT : cochainCoboundary (ZMod 2) Y (q + 1) T = 0)
    (c : coeff ⟶ (chains X).X (q + 1)) (hc : c ≫ (chains X).d (q + 1) q = 0) :
    c ≫ cochainPullback f (q + 1) T = c ≫ cochainPullback g (q + 1) T := by
  have h := congrArg (fun k => c ≫ k) (primitive_boundary H q T hT)
  change c ≫ ((chains X).d (q + 1) q ≫ primitive H q T) = _ at h
  simp only [Preadditive.comp_sub, ← Category.assoc, hc, zero_comp] at h
  exact sub_eq_zero.mp h.symm
end General

open Finsler.NativeSequentialTripleComparison
variable {n : ℕ} {r : ℝ} (hr : r ≤ 1) (q : ℕ)
  (T : singularCochainGroup (ZMod 2) (triple n) (q + 1))

def prefixPrimitive := primitive (prefixHomotopy (n := n) hr) q T

def suffixPrimitive := primitive (suffixHomotopy (n := n) hr) q T

theorem prefix_boundary (hT : cochainCoboundary (ZMod 2) (triple n) (q + 1) T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (NativeSequentialPrefixMiddle.inputs n r)) q
      (prefixPrimitive hr q T) =
    cochainPullback (prefixOriginal hr) (q + 1) T - cochainPullback (prefixCommonTriple hr) (q + 1) T :=
  primitive_boundary (prefixHomotopy hr) q T hT

theorem suffix_boundary (hT : cochainCoboundary (ZMod 2) (triple n) (q + 1) T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (NativeSequentialSuffixMiddle.inputs n r)) q
      (suffixPrimitive hr q T) =
    cochainPullback (suffixOriginal hr) (q + 1) T - cochainPullback (suffixCommonTriple hr) (q + 1) T :=
  primitive_boundary (suffixHomotopy hr) q T hT

theorem prefix_cycle_values (hT : cochainCoboundary (ZMod 2) (triple n) (q + 1) T = 0)
    (c : coeff ⟶ (chains (TopCat.of (NativeSequentialPrefixMiddle.inputs n r))).X (q + 1))
    (hc : c ≫ (chains (TopCat.of (NativeSequentialPrefixMiddle.inputs n r))).d (q + 1) q = 0) :
    c ≫ cochainPullback (prefixOriginal hr) (q + 1) T = c ≫ cochainPullback (prefixCommonTriple hr) (q + 1) T :=
  cycle_values_equal (prefixHomotopy hr) q T hT c hc

theorem suffix_cycle_values (hT : cochainCoboundary (ZMod 2) (triple n) (q + 1) T = 0)
    (c : coeff ⟶ (chains (TopCat.of (NativeSequentialSuffixMiddle.inputs n r))).X (q + 1))
    (hc : c ≫ (chains (TopCat.of (NativeSequentialSuffixMiddle.inputs n r))).d (q + 1) q = 0) :
    c ≫ cochainPullback (suffixOriginal hr) (q + 1) T = c ≫ cochainPullback (suffixCommonTriple hr) (q + 1) T :=
  cycle_values_equal (suffixHomotopy hr) q T hT c hc

end
end Finsler.NativeSequentialTriplePrism
