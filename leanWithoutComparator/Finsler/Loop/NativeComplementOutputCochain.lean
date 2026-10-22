module

public import Finsler.Loop.NativeH1ComplementOutputs
public import Finsler.Loop.CupCapOrder

/-! One actual H1 homotopy moves BOTH complementary cut-output tests.
Its prism supplies the cochain primitive directly on the whole near
space. The original supported Thom/time map then supplies constant-
relative support. No extra support or separate cup Leibniz error is
required for this simultaneous output comparison. -/
@[expose] public section
namespace Finsler.NativeComplementOutputCochain
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SupportedSelfCut Finsler.NativeH1ComplementOutputs Finsler.NativeBVThomBoundary
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

private theorem homotopy_boundary {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (k : ℕ) (T : singularCochainGroup (ZMod 2) Y (k + 1))
    (hT : cochainCoboundary (ZMod 2) Y (k + 1) T = 0) :
    cochainCoboundary (ZMod 2) X k ((H.toSSet.chainComplexMap coeff).hom k (k + 1) ≫ T) =
      cochainPullback f (k + 1) T - cochainPullback g (k + 1) T := by
  have he : (push f).f (k + 1) =
      (chains X).d (k + 1) k ≫ (H.toSSet.chainComplexMap coeff).hom k (k + 1) +
      (H.toSSet.chainComplexMap coeff).hom (k + 1) (k + 2) ≫ (chains Y).d (k + 2) (k + 1) +
      (push g).f (k + 1) := by
    simpa only [push, chains, Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] using
      (H.toSSet.chainComplexMap coeff).comm (k + 1)
  have hb := congrArg (fun f => f ≫ T) he
  have hz : (chains Y).d (k + 2) (k + 1) ≫ T = 0 := hT
  simp only [Preadditive.add_comp, Category.assoc, hz, comp_zero, add_zero] at hb
  exact eq_sub_iff_add_eq.mpr hb.symm

variable (n : ℕ) {r : ℝ} (hr : r ≤ 1) (p q k : ℕ) (h : p + q = k + 1)
  (A : singularCochainGroup (ZMod 2) (Loops n) p)
  (B : singularCochainGroup (ZMod 2) (Loops n) q)

def pairTest : singularCochainGroup (ZMod 2) (outputSpace n) (k + 1) :=
  CupOne.cup _ p q (k + 1) h (cochainPullback (first n) p A) (cochainPullback (second n) q B)

theorem pairTest_closed (hA : cochainCoboundary (ZMod 2) _ p A = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0) :
    cochainCoboundary (ZMod 2) _ (k + 1) (pairTest n p q k h A B) = 0 :=
  CupCapOrder.closed _ _ _ _ _ _ _ (cochainPullback_cocycle _ _ _ hA) (cochainPullback_cocycle _ _ _ hB)

def original : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood n r)) (k + 1) :=
  CupOne.cup _ p q (k + 1) h
    (cochainPullback (TopCat.ofHom (retained n hr)) p A) (cochainPullback (TopCat.ofHom (tested n hr)) q B)

def complemented : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood n r)) (k + 1) :=
  cochainPullback (WholeSelfCutComplement.neighborhoodMap n r) (k + 1)
    (CupOne.cup _ p q (k + 1) h
      (cochainPullback (TopCat.ofHom (tested n hr)) p A) (cochainPullback (TopCat.ofHom (retained n hr)) q B))

theorem swapped_test : cochainPullback (swapped n hr) (k + 1) (pairTest n p q k h A B) =
    original n hr p q k h A B := by
  unfold pairTest original
  rw [CupCapOrder.naturality, ← pullback_comp, ← pullback_comp, swapped_first, swapped_second]

theorem complement_test : cochainPullback (WholeSelfCutComplement.neighborhoodMap n r ≫ output n hr)
    (k + 1) (pairTest n p q k h A B) = complemented n hr p q k h A B := by
  rw [pullback_comp]
  unfold pairTest complemented
  rw [CupCapOrder.naturality, ← pullback_comp, ← pullback_comp, output_first, output_second]

def primitive : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood n r)) k :=
  ((NativeH1ComplementOutputs.homotopy n hr).toSSet.chainComplexMap coeff).hom k (k + 1) ≫ pairTest n p q k h A B

theorem boundary (hA : cochainCoboundary (ZMod 2) _ p A = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0) :
    cochainCoboundary (ZMod 2) _ k (primitive n hr p q k h A B) =
      original n hr p q k h A B - complemented n hr p q k h A B := by
  unfold primitive
  rw [homotopy_boundary _ _ _ (pairTest_closed n p q k h A B hA hB), swapped_test, complement_test]

end
end Finsler.NativeComplementOutputCochain
