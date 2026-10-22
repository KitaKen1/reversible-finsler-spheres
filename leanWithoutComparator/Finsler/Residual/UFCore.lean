module

public import Finsler.Residual.CutJoin
public import Finsler.Loop.StrictLengthProductFirstNaturality
public import Finsler.Loop.StrictLengthFilteredUnit
public import Finsler.Loop.NativeControlledUnitAction

/-! The homological core of the uniform filling (Claude, UF prototype; README §1 four-term chain).

Let T cut lengths by L, let S be a filtered class whose cut is the filtered unit at length B, and
let x be a filtered class at length a whose cut dies after the extra length D₀. Then x dies at
the length max (B + a + ε) ((a − L + 3ε + D₀) + (s + ε)) ⊔ (A − L + 5ε), A = a + s + ε:

  x = 1 • x = (cut S) • x = (cut x) • S = 0

(left unit, unit at B, cut–join identity `CutJoin.cut_join`, filling of the cut). With S a
near-optimal lift of the r-th Theta power and T the r-th GH power cutting by L close to its level,
s − L is bounded by the exact rates, so the loss is uniform once B and D₀ are (UF-PLAN.md U, F). -/

@[expose] public section

namespace Finsler.UFCore

open CategoryTheory AlgebraicTopology SphereOddDegree MonoidalCategory
open Finsler.SphereGeometry Finsler.Geometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.StrictLengthEnergyBridge Finsler.BorelLoop Finsler.SupportedCapNaturality
open Finsler.FarNormalizedDiagonalCap Finsler.SplitPairHomologyKernel

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

variable {m : ℕ} (F : ReversibleMetric (m + 1))

/-- Enlargement of a filtered class. -/
abbrev enl {c d : ℝ} (h : c ≤ d) (k : ℕ) := (homologyPushZMod2 (LengthFilteredLoopRotation.cut F h) k).hom

theorem enl_enl {c d e : ℝ} (h : c ≤ d) (h' : d ≤ e) (k : ℕ) (z : homologyZMod2 (lengthSpace F c) k) :
    enl F h' k (enl F h k z) = enl F (h.trans h') k z := by
  rw [enl, enl, push_comp_apply]
  rfl

theorem enl_outputInclusion {a b A L ε M : ℝ} (hab : a + b < A) (hε : 0 < ε)
    (hM : A - L + 5 * ε ≤ M) (k : ℕ) (z : homologyZMod2 (lengthSpace F ((a - L + 3 * ε) + (b + ε))) k) :
    enl F hM k ((homologyPushZMod2 (StrictLengthProductBudget.outputInclusion F (L := L) hab hε) k).hom z) =
      enl F ((StrictLengthProductBudget.output_bound (L := L) hab hε).le.trans hM) k z := by
  rw [enl, enl, push_comp_apply]
  rfl

/-- **The four-term filling in homology.** -/
theorem kill (hm : 1 ≤ m) {a s L ε B D₀ : ℝ} (hε : 0 < ε) (hs0 : 0 < s) (ha0 : 0 < a)
    (hxa : 0 < a - L + 3 * ε) (hsa : 0 < s - L + 3 * ε) (hB : 0 < B) (hBs : s - L + 3 * ε ≤ B)
    (hD : 0 ≤ D₀)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
    (hsh : cochainPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F L)) p T = 0)
    (i : ℕ) (hi : 1 < i)
    (x : PoolCap.homology (lengthSpace F a) ((m + p) + i))
    (S : PoolCap.homology (lengthSpace F s) ((m + p) + (m + 1)))
    (hunit : enl F hBs (m + 1)
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hsh (a := s)).homology (m + 1)).hom S) =
      StrictLengthFilteredUnit.candidate F (by omega) B hB)
    (hfill : enl F (by linarith : a - L + 3 * ε ≤ a - L + 3 * ε + D₀) i
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hsh (a := a)).homology i).hom x) = 0)
    (M : ℝ) (hM1 : B + (a + ε) ≤ M) (hM2 : (a + s + ε) - L + 5 * ε ≤ M)
    (hM3 : (a - L + 3 * ε + D₀) + (s + ε) ≤ M) :
    enl F (by linarith : a ≤ M) ((m + p) + i) x = 0 := by
  have hab : a + s < a + s + ε := by linarith
  have hba : s + a < a + s + ε := by linarith
  have hij : i + ((m + p) + (m + 1)) = (m + 1) + ((m + p) + i) := by omega
  have hji : (m + 1) + ((m + p) + i) = (m + 1) + ((m + p) + i) := rfl
  set cx := ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hsh (a := a)).homology i).hom x
  set cS := ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hsh (a := s)).homology (m + 1)).hom S
  have CJ := CutJoin.cut_join F hm hab hba hε p T hT hsh i (m + 1) ((m + p) + i) hij hji hi
    (by omega) x S
  -- the side of the cut of x vanishes
  have h1 : enl F hM2 ((m + p) + i) (StrictLengthProductBudget.product F (L := L) hab hε (dim_pos m) i
      ((m + p) + (m + 1)) ((m + p) + i) hij cx S) = 0 := by
    rw [StrictLengthProductBudget.product_apply]
    erw [enl_outputInclusion F hab hε hM2]
    have hle : (a - L + 3 * ε) + (s + ε) ≤ (a - L + 3 * ε + D₀) + (s + ε) := by linarith
    rw [← enl_enl F hle hM3]
    have hN := StrictLengthProductFirstNaturality.product_naturality F hxa (by linarith : 0 < a - L + 3 * ε + D₀)
      hs0 hε (by linarith : a - L + 3 * ε ≤ a - L + 3 * ε + D₀) (by omega) i ((m + p) + (m + 1))
      ((m + p) + i) hij cx S
    erw [← hN, hfill]
    simp
  -- the side of the cut of S is x
  have h2 : enl F hM2 ((m + p) + i) (StrictLengthProductBudget.product F (L := L) hba hε (dim_pos m) (m + 1)
      ((m + p) + i) ((m + p) + i) hji cS x) = enl F (by linarith : a ≤ M) ((m + p) + i) x := by
    rw [StrictLengthProductBudget.product_apply]
    erw [enl_outputInclusion F hba hε hM2]
    have hle : (s - L + 3 * ε) + (a + ε) ≤ B + (a + ε) := by linarith
    rw [← enl_enl F hle hM1]
    have hN := StrictLengthProductFirstNaturality.product_naturality F hsa hB ha0 hε hBs (by omega) (m + 1)
      ((m + p) + i) ((m + p) + i) hji cS x
    erw [← hN, hunit, StrictLengthFilteredUnit.left_unit F (by omega) hB ha0 hε ((m + p) + i) x, enl_enl]
  rw [← h2, ← CJ, h1]

end

end Finsler.UFCore
