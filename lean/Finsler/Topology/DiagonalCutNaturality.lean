module

public import Finsler.Topology.SupportedCapNaturality
public import Finsler.Topology.DiagonalPullbackCut

/-! Naturality of the specified diagonal Thom cut in actual neighborhood homology. -/

@[expose] public section

namespace Finsler.DiagonalCutNaturality

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCap
open Finsler.BorelEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem pairEvaluation_comp {n : ℕ} {X Y : TopCat.{0}} (f : X ⟶ Y)
    (a b : Y ⟶ sphere n) :
    DiagonalPullbackCut.pairEvaluation (f ≫ a) (f ≫ b) =
      f ≫ DiagonalPullbackCut.pairEvaluation a b := by
  ext x : 1
  rfl

theorem cocycle_pullback {n : ℕ} (hn : 1 ≤ n) {X Y : TopCat.{0}} (f : X ⟶ Y)
    (a b : Y ⟶ sphere n) :
    DiagonalPullbackCut.cocycle hn (f ≫ a) (f ≫ b) =
      cochainPullback f n (DiagonalPullbackCut.cocycle hn a b) := by
  rw [DiagonalPullbackCut.cocycle_comparison, DiagonalPullbackCut.cocycle_comparison,
    ← SupportedCapNaturality.pullback_comp, pairEvaluation_comp]

def operation {n : ℕ} (hn : 1 ≤ n) {X : TopCat.{0}} (a b : X ⟶ sphere n)
    (B : Set X) (hB : IsOpen B) (hdiag : ∀ x, a x = b x → x ∈ B) :=
  SupportedCapHomology.operation X (DiagonalPullbackCut.exclusion a b) B
    (DiagonalPullbackCut.exclusion_open (n := n) a b) hB
    (DiagonalPullbackCut.neighborhood_cover (n := n) a b B hdiag) n
    (DiagonalPullbackCut.cocycle hn a b) (DiagonalPullbackCut.cocycle_supported hn a b)
    (DiagonalPullbackCut.cocycle_closed hn a b)

theorem homology_naturality {n : ℕ} (hn : 1 ≤ n) {X Y : TopCat.{0}} (f : X ⟶ Y)
    (a b : Y ⟶ sphere n) (B : Set X) (D : Set Y) (hB : IsOpen B) (hD : IsOpen D)
    (hdiagX : ∀ x, (f ≫ a) x = (f ≫ b) x → x ∈ B)
    (hdiagY : ∀ y, a y = b y → y ∈ D) (hfB : Set.MapsTo f B D) (q : ℕ) :
    HomologicalComplex.homologyMap (SupportedCapNaturality.push f) (n + q) ≫
        (operation hn a b D hD hdiagY).homology q =
      (operation hn (f ≫ a) (f ≫ b) B hB hdiagX).homology q ≫
        HomologicalComplex.homologyMap
          (SupportedCapNaturality.push (SupportedCapNaturality.restriction f B D hfB)) q := by
  have hA : Set.MapsTo f (DiagonalPullbackCut.exclusion (f ≫ a) (f ≫ b))
      (DiagonalPullbackCut.exclusion a b) := by
    intro x hx
    exact hx
  have he := SupportedCapNaturality.homology_naturality f
    (DiagonalPullbackCut.exclusion (f ≫ a) (f ≫ b)) B
    (DiagonalPullbackCut.exclusion a b) D
    (DiagonalPullbackCut.exclusion_open (n := n) (f ≫ a) (f ≫ b)) hB
    (DiagonalPullbackCut.neighborhood_cover (n := n) (f ≫ a) (f ≫ b) B hdiagX)
    (DiagonalPullbackCut.exclusion_open (n := n) a b) hD
    (DiagonalPullbackCut.neighborhood_cover (n := n) a b D hdiagY) hA hfB n q
    (DiagonalPullbackCut.cocycle hn a b) (DiagonalPullbackCut.cocycle_supported hn a b)
    (DiagonalPullbackCut.cocycle_closed hn a b)
  simpa only [operation, ← cocycle_pullback hn f a b] using he

end
end Finsler.DiagonalCutNaturality

