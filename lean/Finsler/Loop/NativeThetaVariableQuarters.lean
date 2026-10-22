module

public import Finsler.Loop.NativeFixedReturnRotationZero
public import Finsler.Loop.UncappedTimeSplit

/-! Decompose the ORIGINAL native triple rotation prism into its
TWELVE actual quarter prisms plus an explicit singular boundary.
For the localized ORIGINAL Theta-cut cochain all six fixed-return
terms and the boundary vanish. Only the SIX VARIABLE quarter
prisms remain; no local Thom intersection count is inserted. -/
@[expose] public section
namespace Finsler.NativeThetaVariableQuarters
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily Finsler.SobolevShift
open Finsler.MeridianTripleQuarterClocks Finsler.NativeFixedReturnRotationZero
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem sum_two {A : Type*} [AddCommMonoid A] (f : Fin 2 → A) :
    ∑ i, f i = f 0 + f 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

private theorem sum_three {A : Type*} [AddCommMonoid A] (f : Fin 3 → A) :
    ∑ i, f i = f 0 + f 1 + f 2 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + f 2) = f 0 + f 1 + f 2
  exact (add_assoc _ _ _).symm

private theorem sum_four {A : Type*} [AddCommMonoid A] (f : Fin 4 → A) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + f 3)) = f 0 + f 1 + f 2 + f 3
  abel

def fullMap {n : ℕ} (P : Sphere n) (v₀ : equator P) := (NativeH1TripleMeridian.rotationHomotopy P v₀).h

def blockMap {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :=
  match k with
  | 0 => UncappedTimeSplit.first (UncappedTimeSplit.first (fullMap P v₀))
  | 1 => UncappedTimeSplit.second (UncappedTimeSplit.first (fullMap P v₀))
  | 2 => UncappedTimeSplit.second (fullMap P v₀)

def blockTime (k : Fin 3) (t : _root_.unitInterval) : ℝ :=
  match k with
  | 0 => (t : ℝ) / 4
  | 1 => (1 + (t : ℝ)) / 4
  | 2 => (1 + (t : ℝ)) / 2

theorem blockMap_apply {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3)
    (z : parameters P ⊗ TopCat.I) :
    blockMap P v₀ k z = shiftSphere (NativeH1TripleMeridian.native P v₀ z.1) (blockTime k z.2.down) := by
  fin_cases k
  · change shiftSphere (NativeH1TripleMeridian.native P v₀ z.1) ((z.2.down : ℝ) / 2 / 2) =
      shiftSphere (NativeH1TripleMeridian.native P v₀ z.1) ((z.2.down : ℝ) / 4)
    congr 1
    ring
  · change shiftSphere (NativeH1TripleMeridian.native P v₀ z.1) ((1 + (z.2.down : ℝ)) / 2 / 2) =
      shiftSphere (NativeH1TripleMeridian.native P v₀ z.1) ((1 + (z.2.down : ℝ)) / 4)
    congr 1
    ring
  · rfl

def quarterMap {X Y : TopCat.{0}} (f : X ⊗ TopCat.I ⟶ Y) (q : Fin 4) :=
  match q with
  | 0 => UncappedTimeSplit.first (UncappedTimeSplit.first f)
  | 1 => UncappedTimeSplit.second (UncappedTimeSplit.first f)
  | 2 => UncappedTimeSplit.first (UncappedTimeSplit.second f)
  | 3 => UncappedTimeSplit.second (UncappedTimeSplit.second f)

theorem quarterMap_block {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (q : Fin 4) :
    quarterMap (blockMap P v₀ k) q = (quarterHomotopy P v₀ k q).h := by
  fin_cases q
  · ext z : 1
    change blockMap P v₀ k (z.1, IntervalTriangle.firstMap (IntervalTriangle.firstMap z.2)) = _
    rw [blockMap_apply]
    change shiftSphere (NativeH1TripleMeridian.native P v₀ z.1)
      (blockTime k (IntervalTriangle.firstMap (IntervalTriangle.firstMap z.2)).down) =
        shiftSphere (NativeH1TripleMeridian.native P v₀ z.1) (clock k 0 z.2.down)
    congr 1
    have ht : ((IntervalTriangle.firstMap (IntervalTriangle.firstMap z.2)).down : ℝ) = (0 + (z.2.down : ℝ)) / 4 := by
      change (z.2.down : ℝ) / 2 / 2 = (0 + (z.2.down : ℝ)) / 4
      ring
    fin_cases k <;> simp only [blockTime, clock, localTime, ht] <;> norm_num
  · ext z : 1
    change blockMap P v₀ k (z.1, IntervalTriangle.firstMap (IntervalTriangle.secondMap z.2)) = _
    rw [blockMap_apply]
    change shiftSphere (NativeH1TripleMeridian.native P v₀ z.1)
      (blockTime k (IntervalTriangle.firstMap (IntervalTriangle.secondMap z.2)).down) =
        shiftSphere (NativeH1TripleMeridian.native P v₀ z.1) (clock k 1 z.2.down)
    congr 1
    have ht : ((IntervalTriangle.firstMap (IntervalTriangle.secondMap z.2)).down : ℝ) = (1 + (z.2.down : ℝ)) / 4 := by
      change (1 + (z.2.down : ℝ)) / 2 / 2 = (1 + (z.2.down : ℝ)) / 4
      ring
    fin_cases k <;> simp only [blockTime, clock, localTime, ht] <;> norm_num
  · ext z : 1
    change blockMap P v₀ k (z.1, IntervalTriangle.secondMap (IntervalTriangle.firstMap z.2)) = _
    rw [blockMap_apply]
    change shiftSphere (NativeH1TripleMeridian.native P v₀ z.1)
      (blockTime k (IntervalTriangle.secondMap (IntervalTriangle.firstMap z.2)).down) =
        shiftSphere (NativeH1TripleMeridian.native P v₀ z.1) (clock k 2 z.2.down)
    congr 1
    have ht : ((IntervalTriangle.secondMap (IntervalTriangle.firstMap z.2)).down : ℝ) = (2 + (z.2.down : ℝ)) / 4 := by
      change (1 + (z.2.down : ℝ) / 2) / 2 = (2 + (z.2.down : ℝ)) / 4
      ring
    fin_cases k <;> simp only [blockTime, clock, localTime, ht] <;> norm_num
  · ext z : 1
    change blockMap P v₀ k (z.1, IntervalTriangle.secondMap (IntervalTriangle.secondMap z.2)) = _
    rw [blockMap_apply]
    change shiftSphere (NativeH1TripleMeridian.native P v₀ z.1)
      (blockTime k (IntervalTriangle.secondMap (IntervalTriangle.secondMap z.2)).down) =
        shiftSphere (NativeH1TripleMeridian.native P v₀ z.1) (clock k 3 z.2.down)
    congr 1
    have ht : ((IntervalTriangle.secondMap (IntervalTriangle.secondMap z.2)).down : ℝ) = (3 + (z.2.down : ℝ)) / 4 := by
      change (1 + (1 + (z.2.down : ℝ)) / 2) / 2 = (3 + (z.2.down : ℝ)) / 4
      ring
    fin_cases k <;> simp only [blockTime, clock, localTime, ht] <;> norm_num

def blockComparison {n : ℕ} (P : Sphere n) (v₀ : equator P) (j : ℕ) :=
  UncappedTimeSplit.comparison (fullMap P v₀) j +
    UncappedTimeSplit.comparison (UncappedTimeSplit.first (fullMap P v₀)) j

theorem original_blocks_split {n : ℕ} (P : Sphere n) (v₀ : equator P) (j : ℕ) :
    (chains (parameters P)).iCycles j ≫ UncappedTimeSplit.component (fullMap P v₀) j =
      (chains (parameters P)).iCycles j ≫ UncappedTimeSplit.component (blockMap P v₀ 0) j +
      (chains (parameters P)).iCycles j ≫ UncappedTimeSplit.component (blockMap P v₀ 1) j +
      (chains (parameters P)).iCycles j ≫ UncappedTimeSplit.component (blockMap P v₀ 2) j +
      ((chains (parameters P)).iCycles j ≫ blockComparison P v₀ j) ≫ (chains (Loops n)).d (j + 2) (j + 1) := by
  rw [UncappedTimeSplit.full_split, UncappedTimeSplit.full_split (UncappedTimeSplit.first (fullMap P v₀)) j]
  simp only [blockComparison, blockMap, Preadditive.comp_add, Preadditive.add_comp]
  abel

def totalComparison {n : ℕ} (P : Sphere n) (v₀ : equator P) (j : ℕ) :=
  blockComparison P v₀ j + ∑ k : Fin 3, UncappedTimeSplit.fourComparison (blockMap P v₀ k) j

theorem block_four_split {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (j : ℕ) :
    (chains (parameters P)).iCycles j ≫ UncappedTimeSplit.component (blockMap P v₀ k) j =
      (∑ q : Fin 4, (chains (parameters P)).iCycles j ≫
        UncappedTimeSplit.component (quarterMap (blockMap P v₀ k) q) j) +
      ((chains (parameters P)).iCycles j ≫ UncappedTimeSplit.fourComparison (blockMap P v₀ k) j) ≫
        (chains (Loops n)).d (j + 2) (j + 1) := by
  rw [UncappedTimeSplit.four_split, sum_four]
  rfl

theorem original_twelve_split {n : ℕ} (P : Sphere n) (v₀ : equator P) (j : ℕ) :
    (chains (parameters P)).iCycles j ≫
      ((NativeH1TripleMeridian.rotationHomotopy P v₀).toSSet.chainComplexMap coeff).hom j (j + 1) =
      (∑ k : Fin 3, ∑ q : Fin 4, (chains (parameters P)).iCycles j ≫
        ((quarterHomotopy P v₀ k q).toSSet.chainComplexMap coeff).hom j (j + 1)) +
      ((chains (parameters P)).iCycles j ≫ totalComparison P v₀ j) ≫ (chains (Loops n)).d (j + 2) (j + 1) := by
  have hb := original_blocks_split P v₀ j
  rw [block_four_split P v₀ 0 j, block_four_split P v₀ 1 j, block_four_split P v₀ 2 j] at hb
  have hs : (∑ k : Fin 3, ∑ q : Fin 4, (chains (parameters P)).iCycles j ≫
      UncappedTimeSplit.component (quarterMap (blockMap P v₀ k) q) j) +
      ((chains (parameters P)).iCycles j ≫ totalComparison P v₀ j) ≫ (chains (Loops n)).d (j + 2) (j + 1) =
      (chains (parameters P)).iCycles j ≫ UncappedTimeSplit.component (fullMap P v₀) j := by
    rw [hb]
    simp only [totalComparison, sum_three,
      Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
    abel
  rw [fullMap, UncappedTimeSplit.prism_component] at hs
  simp_rw [quarterMap_block, UncappedTimeSplit.prism_component] at hs
  exact hs.symm

theorem variable_quarters_only (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    {η ρ r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    ((chains (parameters P)).iCycles (3 * m) ≫
      ((NativeH1TripleMeridian.rotationHomotopy P v₀).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1)) ≫
      castCochain m (OppositeMeridianEvaluationPoint.target v₀) hη hρ hρr hr =
    ∑ k : Fin 3, ∑ q : Fin 2,
      ((chains (parameters P)).iCycles (3 * m) ≫
        ((quarterHomotopy P v₀ k ⟨q.val, by omega⟩).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1)) ≫
          castCochain m (OppositeMeridianEvaluationPoint.target v₀) hη hρ hρr hr := by
  let ψ := castCochain m (OppositeMeridianEvaluationPoint.target v₀) hη hρ hρr hr
  have hc := cast_closed m (OppositeMeridianEvaluationPoint.target v₀) hη hρ hρr hr
  change (chains (Loops (m + 1))).d (3 * m + 2) (3 * m + 1) ≫ ψ = 0 at hc
  have hs := congrArg (fun a => a ≫ ψ) (original_twelve_split P v₀ (3 * m))
  simp only [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc, hc, comp_zero, add_zero] at hs
  change (chains (parameters P)).iCycles (3 * m) ≫
    ((NativeH1TripleMeridian.rotationHomotopy P v₀).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫ ψ =
      ∑ k : Fin 3, ∑ q : Fin 2, (chains (parameters P)).iCycles (3 * m) ≫
        ((quarterHomotopy P v₀ k ⟨q.val, by omega⟩).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫ ψ
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  have h2 : ((quarterHomotopy P v₀ k 2).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫ ψ = 0 :=
    fixed_quarter_prism_zero m P v₀ k 0 hη hη1 hρ hρr hr
  have h3 : ((quarterHomotopy P v₀ k 3).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫ ψ = 0 :=
    fixed_quarter_prism_zero m P v₀ k 1 hη hη1 hρ hρr hr
  rw [sum_four, sum_two]
  simp only [h2, h3, comp_zero, add_zero]
  rfl

end
end Finsler.NativeThetaVariableQuarters
