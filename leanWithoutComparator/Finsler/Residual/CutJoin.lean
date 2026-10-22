module

public import Finsler.Residual.ShuffleSwap
public import Finsler.Loop.StrictLengthProductSwap
public import Finsler.Loop.FilteredCanonicalInterchange

/-! The cut–join identity (Claude, UF prototype, step 4 of hr/UF-PLAN.md).

For a cutting cocycle T and filtered classes x (length a) and y (length b), the loop product of the
cut of x with y equals the loop product of the cut of y with x, as filtered classes of the same
output length:

  (cut_T x) • y = (cut_T y) • x.

Both sides are the genuine operation "product, then cut" applied to the cross product of the two
classes (`FilteredCanonicalInterchange.value`, the cut acting on the first factor); the product is
symmetric under the source swap (`StrictLengthProductSwap.homology`) and the mod-2 cross product
is symmetric under the swap (`SSet.ShuffleSwap.cross_swap`). -/

@[expose] public section

namespace Finsler.CutJoin

open CategoryTheory AlgebraicTopology SphereOddDegree MonoidalCategory
open Finsler.SphereGeometry Finsler.Geometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.StrictLengthEnergyBridge Finsler.BorelLoop Finsler.SupportedCapNaturality
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

theorem eqToHom_homologyMap {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (φ : C ⟶ D) {i j : ℕ}
    (h : i = j) :
    eqToHom (congrArg (fun k => C.homology k) h) ≫ HomologicalComplex.homologyMap φ j =
      HomologicalComplex.homologyMap φ i ≫ eqToHom (congrArg (fun k => D.homology k) h) := by
  subst h
  simp

variable {m : ℕ} (F : ReversibleMetric (m + 1))

theorem swap_eq (a b : ℝ) :
    SmallThomSwap.swap (P := SelfCutOscillation.short F a) (Q := SelfCutOscillation.short F b) =
      (β_ (lengthSpace F a) (lengthSpace F b)).hom := by
  ext z : 1
  rfl

/-- **The product-then-cut operation is symmetric under the source swap.** -/
theorem op_swap (hm : 1 ≤ m) {a b A L ε : ℝ} (hab : a + b < A) (hba : b + a < A) (hε : 0 < ε)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
    (hs : cochainPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F L)) p T = 0)
    (k : ℕ) :
    (CanonicalAfterLengthProduct.operation F hab hε p T hT hs).homology k =
      HomologicalComplex.homologyMap (push (SmallThomSwap.swap (P := SelfCutOscillation.short F a)
        (Q := SelfCutOscillation.short F b))) (((m + 1) + (m + p)) + k) ≫
      (CanonicalAfterLengthProduct.operation F hba hε p T hT hs).homology k := by
  rw [CanonicalAfterLengthProduct.operation, CanonicalAfterLengthProduct.operation,
    DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology,
    DegreeLoweringComposition.homology, DegreeLoweringComposition.homology,
    StrictLengthProductSwap.homology F hm hε (CanonicalAfterLengthProduct.input_budget hab hε)]
  simp only [Category.assoc]
  rw [reassoc_of% (eqToHom_homologyMap _ (Nat.add_assoc (m + 1) (m + p) k))]

/-- **The cut–join identity**: (cut_T x) • y = (cut_T y) • x as filtered classes. -/
theorem cut_join (hm : 1 ≤ m) {a b A L ε : ℝ} (hab : a + b < A) (hba : b + a < A) (hε : 0 < ε)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
    (hs : cochainPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F L)) p T = 0)
    (i i' k : ℕ) (hij : i + ((m + p) + i') = (m + 1) + k) (hji : i' + ((m + p) + i) = (m + 1) + k)
    (hi : 1 < i) (hi' : 1 < i')
    (x : PoolCap.homology (lengthSpace F a) ((m + p) + i))
    (y : PoolCap.homology (lengthSpace F b) ((m + p) + i')) :
    StrictLengthProductBudget.product F (L := L) hab hε (dim_pos m) i ((m + p) + i') k hij
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hs).homology i).hom x) y =
      StrictLengthProductBudget.product F (L := L) hba hε (dim_pos m) i' ((m + p) + i) k hji
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hs).homology i').hom y) x := by
  rw [← FilteredCanonicalInterchange.value F hε hm p L a b A T hT hs hab i ((m + p) + i') k hij hi x y,
    ← FilteredCanonicalInterchange.value F hε hm p L b a A T hT hs hba i' ((m + p) + i) k hji hi' y x,
    op_swap F hm hab hba hε p T hT hs k]
  change ((CanonicalAfterLengthProduct.operation F hba hε p T hT hs).homology k).hom
      ((HomologicalComplex.homologyMap (push (SmallThomSwap.swap (P := SelfCutOscillation.short F a)
        (Q := SelfCutOscillation.short F b))) (((m + 1) + (m + p)) + k)).hom _) = _
  congr 1
  rw [swap_eq]
  exact SSet.ShuffleSwap.cross_swap (lengthSpace F a) (lengthSpace F b) ((m + p) + i) ((m + p) + i')
    (((m + 1) + (m + p)) + k) (by omega) (by omega) x y

end

end Finsler.CutJoin
