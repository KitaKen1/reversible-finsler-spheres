module

public import Finsler.Loop.TripleCrossClosedSweep
public import Finsler.Loop.NativeDoubleFundamentalImage

/-! Compute the SIX actual two-coordinate meridian-sweep inputs on
the ORIGINAL left-associated triple equator fundamental class.
The final sphere factors remain in their original source positions:
S,S,E or S,E,S or E,S,S. Both time orders have the same proved input
in each of these spaces. No source-permutation invariance or general
singular-cross associativity is used. -/
@[expose] public section
namespace Finsler.MeridianOrderedSweepInputs
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.TripleCrossClosedSweep
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

abbrev E {n : ℕ} (P : Sphere n) : TopCat.{0} := TopCat.of (equator P)
abbrev S (n : ℕ) : TopCat.{0} := BorelEvaluation.sphere n
abbrev H {n : ℕ} (P : Sphere n) (v₀ : equator P) := MeridianRelativeSweep.fullHomotopy P v₀

def class01 (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :=
  tripleCross (S (m + 1)) (S (m + 1)) (E P) (m + 1) (m + 1) m (2 * m + 2) (3 * m + 2)
    (by omega) (by omega) (SphereUnitCandidate.fundamental (m + 1) (by omega))
    (SphereUnitCandidate.fundamental (m + 1) (by omega)) (MeridianEquatorHomology.fundamental m hm P)

def class02 (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :=
  tripleCross (S (m + 1)) (E P) (S (m + 1)) (m + 1) m (m + 1) (2 * m + 1) (3 * m + 2)
    (by omega) (by omega) (SphereUnitCandidate.fundamental (m + 1) (by omega))
    (MeridianEquatorHomology.fundamental m hm P) (SphereUnitCandidate.fundamental (m + 1) (by omega))

def class12 (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :=
  tripleCross (E P) (S (m + 1)) (S (m + 1)) m (m + 1) (m + 1) (2 * m + 1) (3 * m + 2)
    (by omega) (by omega) (MeridianEquatorHomology.fundamental m hm P)
    (SphereUnitCandidate.fundamental (m + 1) (by omega)) (SphereUnitCandidate.fundamental (m + 1) (by omega))

def input01Forward (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (SelfHomotopySweep.homology ((second (S (m + 1)) (H P v₀) (E P)).toSSet.chainComplexMap coeff) (3 * m + 1)).hom
    ((SelfHomotopySweep.homology ((first (H P v₀) (E P) (E P)).toSSet.chainComplexMap coeff) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))

def input01Wrapped (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (SelfHomotopySweep.homology ((first (H P v₀) (S (m + 1)) (E P)).toSSet.chainComplexMap coeff) (3 * m + 1)).hom
    ((SelfHomotopySweep.homology ((second (E P) (H P v₀) (E P)).toSSet.chainComplexMap coeff) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))

def input02Forward (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (SelfHomotopySweep.homology ((third (S (m + 1)) (E P) (H P v₀)).toSSet.chainComplexMap coeff) (3 * m + 1)).hom
    ((SelfHomotopySweep.homology ((first (H P v₀) (E P) (E P)).toSSet.chainComplexMap coeff) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))

def input02Wrapped (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (SelfHomotopySweep.homology ((first (H P v₀) (E P) (S (m + 1))).toSSet.chainComplexMap coeff) (3 * m + 1)).hom
    ((SelfHomotopySweep.homology ((third (E P) (E P) (H P v₀)).toSSet.chainComplexMap coeff) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))

def input12Forward (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (SelfHomotopySweep.homology ((third (E P) (S (m + 1)) (H P v₀)).toSSet.chainComplexMap coeff) (3 * m + 1)).hom
    ((SelfHomotopySweep.homology ((second (E P) (H P v₀) (E P)).toSSet.chainComplexMap coeff) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))

def input12Wrapped (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (SelfHomotopySweep.homology ((second (E P) (H P v₀) (S (m + 1))).toSSet.chainComplexMap coeff) (3 * m + 1)).hom
    ((SelfHomotopySweep.homology ((third (E P) (E P) (H P v₀)).toSSet.chainComplexMap coeff) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))

theorem source_eq (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :
    BasedMeridianProducts.tripleSource m hm P =
      tripleCross (E P) (E P) (E P) m m m (2 * m) (3 * m) (by omega) (by omega)
        (MeridianEquatorHomology.fundamental m hm P) (MeridianEquatorHomology.fundamental m hm P)
        (MeridianEquatorHomology.fundamental m hm P) := rfl

theorem forward01_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    input01Forward m hm P v₀ = class01 m hm P := by
  dsimp only [input01Forward]
  rw [source_eq]
  simp only [first_value, second_value, NativeDoubleFundamentalImage.full_fundamental]
  rfl

theorem wrapped01_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    input01Wrapped m hm P v₀ = class01 m hm P := by
  dsimp only [input01Wrapped]
  rw [source_eq]
  simp only [first_value, second_value, NativeDoubleFundamentalImage.full_fundamental]
  rfl

theorem forward02_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    input02Forward m hm P v₀ = class02 m hm P := by
  dsimp only [input02Forward]
  rw [source_eq]
  simp only [first_value, third_value, NativeDoubleFundamentalImage.full_fundamental]
  rfl

theorem wrapped02_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    input02Wrapped m hm P v₀ = class02 m hm P := by
  dsimp only [input02Wrapped]
  rw [source_eq]
  simp only [first_value, third_value, NativeDoubleFundamentalImage.full_fundamental]
  rfl

theorem forward12_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    input12Forward m hm P v₀ = class12 m hm P := by
  dsimp only [input12Forward]
  rw [source_eq]
  simp only [second_value, third_value, NativeDoubleFundamentalImage.full_fundamental]
  rfl

theorem wrapped12_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    input12Wrapped m hm P v₀ = class12 m hm P := by
  dsimp only [input12Wrapped]
  rw [source_eq]
  simp only [second_value, third_value, NativeDoubleFundamentalImage.full_fundamental]
  rfl

end
end Finsler.MeridianOrderedSweepInputs
