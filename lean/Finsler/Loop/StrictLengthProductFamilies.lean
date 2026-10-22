module

public import Finsler.Loop.StrictLengthProductGeometricFactor

/-! Actual separately length-bounded parameter families pull the length
product back to their genuine diagonal cap and raw kept-output join.
Only continuity and the two actual length bounds are required. -/

@[expose] public section
namespace Finsler.StrictLengthProductFamilies

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.StrictLengthEnergyBridge Finsler.StrictLengthLoopProduct
open Finsler.CompactH1Alignment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (F : ReversibleMetric n)
  (p q : ℝ) (hα : ∀ x, SobolevLength.length F (α x) < p)
  (hβ : ∀ y, SobolevLength.length F (β y) < q)

def leftInput : TopCat.of P ⟶ lengthSpace F p :=
  TopCat.ofHom ⟨fun x => ⟨α x, hα x⟩, α.continuous.subtype_mk _⟩

def rightInput : TopCat.of Q ⟶ lengthSpace F q :=
  TopCat.ofHom ⟨fun y => ⟨β y, hβ y⟩, β.continuous.subtype_mk _⟩

def pairInput : TopCat.of (P × Q) ⟶ pairSpace F p q :=
  leftInput α F p hα ⊗ₘ rightInput β F q hβ

def leftEvaluation : TopCat.of (P × Q) ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun z => H1FiberBase.point (α z.1),
    H1FiberBase.continuous_point.comp (α.continuous.comp continuous_fst)⟩

def rightEvaluation : TopCat.of (P × Q) ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun z => H1FiberBase.point (β z.2),
    H1FiberBase.continuous_point.comp (β.continuous.comp continuous_snd)⟩

theorem left_square : pairInput α β F p q hα hβ ≫ LengthProductNormalizationGeometry.leftEvaluation F p q =
    leftEvaluation α (Q := Q) := rfl

theorem right_square : pairInput α β F p q hα hβ ≫ LengthProductNormalizationGeometry.rightEvaluation F p q =
    rightEvaluation β (P := P) := rfl

variable (hp : 0 < p) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε)

def tube : Set (TopCat.of (P × Q)) := (pairInput α β F p q hα hβ) ⁻¹'
  StrictLengthProductJoinComparison.commonTube F p q hp hq hε

theorem tube_open : IsOpen (tube α β F p q hα hβ hp hq hε) :=
  (StrictLengthProductJoinComparison.commonTube_open F p q hp hq hε).preimage
    (pairInput α β F p q hα hβ).hom.continuous

theorem tube_formula (z : P × Q) : z ∈ tube α β F p q hα hβ hp hq hε ↔
    dist (basepoint (α z.1)) (basepoint (β z.2)) < StrictLengthProductJoinComparison.radius F p q hp hq hε := Iff.rfl

theorem diagonal_in_tube (z : P × Q) (hz : leftEvaluation α z = rightEvaluation β z) :
    z ∈ tube α β F p q hα hβ hp hq hε := by
  apply StrictLengthProductGeometricFactor.diagonal_in_common F p q hp hq hε
  exact hz

def toCommon := restriction (pairInput α β F p q hα hβ) (tube α β F p q hα hβ hp hq hε)
  (StrictLengthProductJoinComparison.commonTube F p q hp hq hε) (fun _ hz => hz)

def thomOperation (hn : 1 ≤ n) := DiagonalCutNaturality.operation hn
  (leftEvaluation α (Q := Q)) (rightEvaluation β (P := P)) (tube α β F p q hα hβ hp hq hε)
  (tube_open α β F p q hα hβ hp hq hε) (diagonal_in_tube α β F p q hα hβ hp hq hε)

theorem thom_naturality (hn : 1 ≤ n) (k : ℕ) :
    HomologicalComplex.homologyMap (push (pairInput α β F p q hα hβ)) (n + k) ≫
      (StrictLengthProductGeometricFactor.commonThom F p q hp hq hε hn).homology k =
    (thomOperation α β F p q hα hβ hp hq hε hn).homology k ≫
      HomologicalComplex.homologyMap (push (toCommon α β F p q hα hβ hp hq hε)) k := by
  have he := DiagonalCutNaturality.homology_naturality hn (pairInput α β F p q hα hβ)
    (LengthProductNormalizationGeometry.leftEvaluation F p q) (LengthProductNormalizationGeometry.rightEvaluation F p q)
    (tube α β F p q hα hβ hp hq hε) (StrictLengthProductJoinComparison.commonTube F p q hp hq hε)
    (tube_open α β F p q hα hβ hp hq hε) (StrictLengthProductJoinComparison.commonTube_open F p q hp hq hε)
    (diagonal_in_tube α β F p q hα hβ hp hq hε)
    (StrictLengthProductGeometricFactor.diagonal_in_common F p q hp hq hε) (fun _ hz => hz) k
  exact he

def rawJoin := toCommon α β F p q hα hβ hp hq hε ≫ StrictLengthProductJoinComparison.rawJoin F p q hp hq hε

theorem rawJoin_formula (z : tube α β F p q hα hβ hp hq hε) :
    (rawJoin α β F p q hα hβ hp hq hε z).val =
      JoinDirectionComparison.firstJoin JoinSplitHomotopy.half JoinSplitHomotopy.half.property.1
        JoinSplitHomotopy.half.property.2 (α z.val.1) (β z.val.2) :=
  StrictLengthProductJoinComparison.rawJoin_formula F p q hp hq hε _

def geometricOperation (hn : 1 ≤ n) :=
  (thomOperation α β F p q hα hβ hp hq hε hn).post (push (rawJoin α β F p q hα hβ hp hq hε))

theorem operation_factor (hn : 1 ≤ n) (k : ℕ) :
    ((StrictLengthLoopProduct.operation F hn hε).pre (push (pairInput α β F p q hα hβ))).homology k =
      (geometricOperation α β F p q hα hβ hp hq hε hn).homology k := by
  rw [DegreeLoweringHomology.Map.pre_homology, StrictLengthProductGeometricFactor.operation F p q hp hq hε hn k,
    StrictLengthProductGeometricFactor.geometricOperation, DegreeLoweringHomology.Map.post_homology,
    ← Category.assoc, thom_naturality α β F p q hα hβ hp hq hε hn k,
    Category.assoc, geometricOperation, DegreeLoweringHomology.Map.post_homology,
    rawJoin, push_comp, HomologicalComplex.homologyMap_comp]

theorem product_factor (hn : 1 ≤ n) (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (TopCat.of P) i) (y : PoolCap.homology (TopCat.of Q) j) :
    StrictLengthLoopProduct.product F hn hε i j k h
      ((PoolCap.push (leftInput α F p hα) i).hom x) ((PoolCap.push (rightInput β F q hβ) j).hom y) =
    ((geometricOperation α β F p q hα hβ hp hq hε hn).homology k).hom
      (FilteredBilinearLoopProduct.cross (TopCat.of P) (TopCat.of Q) i j (n + k) h x y) := by
  rw [StrictLengthProductCompatibility.chain_apply,
    CrossProjectionZero.cross_naturality_apply (leftInput α F p hα) (rightInput β F q hβ)]
  have he := ConcreteCategory.congr_hom (operation_factor α β F p q hα hβ hp hq hε hn k)
    (FilteredBilinearLoopProduct.cross (TopCat.of P) (TopCat.of Q) i j (n + k) h x y)
  rw [DegreeLoweringHomology.Map.pre_homology] at he
  exact he

end
end Finsler.StrictLengthProductFamilies
