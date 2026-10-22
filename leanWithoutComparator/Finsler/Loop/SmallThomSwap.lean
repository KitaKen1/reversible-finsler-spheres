module

public import Finsler.Loop.CompactSpecifiedCapShrink
public import Finsler.Topology.DiagonalCutSwap

/-! Naturality and the actual supported diagonal primitive identify
the specified small-neighborhood Thom cuts under interchange of inputs. -/

@[expose] public section
namespace Finsler.SmallThomSwap
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))

def swap : TopCat.of (P × Q) ⟶ TopCat.of (Q × P) :=
  TopCat.ofHom ⟨Prod.swap, continuous_swap⟩

theorem left_square : swap (P := P) (Q := Q) ≫ StrictLengthProductFamilies.leftEvaluation β =
    StrictLengthProductFamilies.rightEvaluation β (P := P) := rfl

theorem right_square : swap (P := P) (Q := Q) ≫ StrictLengthProductFamilies.rightEvaluation α =
    StrictLengthProductFamilies.leftEvaluation α (Q := Q) := rfl

variable (s : ℝ) (hs : 0 < s)

def nearSwap : TopCat.of (CompactNormalizedJoinCapComparison.near α β s) ⟶
    TopCat.of (CompactNormalizedJoinCapComparison.near β α s) :=
  restriction (swap (P := P) (Q := Q))
    (CompactNormalizedJoinCapComparison.near α β s) (CompactNormalizedJoinCapComparison.near β α s)
    (fun z hz => by
    change dist (basepoint (β z.2)) (basepoint (α z.1)) < s
    rw [dist_comm]
    exact hz)

theorem homology_eq (hm : 1 ≤ m) (q : ℕ) :
    HomologicalComplex.homologyMap (push (swap (P := P) (Q := Q))) ((m + 1) + q) ≫
      (CompactSpecifiedCapShrink.smallOperation β α s hs).homology q =
    (CompactSpecifiedCapShrink.smallOperation α β s hs).homology q ≫
      HomologicalComplex.homologyMap (push (nearSwap α β s)) q := by
  have he := DiagonalCutNaturality.homology_naturality (FarNormalizedDiagonalCap.dim_pos m)
    (swap (P := P) (Q := Q))
    (StrictLengthProductFamilies.leftEvaluation β (Q := P))
    (StrictLengthProductFamilies.rightEvaluation α (P := Q))
    (CompactNormalizedJoinCapComparison.near α β s) (CompactNormalizedJoinCapComparison.near β α s)
    (CompactNormalizedJoinCapComparison.near_open α β s) (CompactNormalizedJoinCapComparison.near_open β α s)
    (fun z hz => CompactSpecifiedCapShrink.diagonal_in_near α β s hs z hz.symm)
    (CompactSpecifiedCapShrink.diagonal_in_near β α s hs)
    (fun z hz => by change dist (basepoint (β z.2)) (basepoint (α z.1)) < s; rw [dist_comm]; exact hz) q
  have hd := DiagonalCutSwap.homology_swap m hm
    (StrictLengthProductFamilies.leftEvaluation α (Q := Q))
    (StrictLengthProductFamilies.rightEvaluation β (P := P))
    (CompactNormalizedJoinCapComparison.near α β s)
    (CompactNormalizedJoinCapComparison.near_open α β s)
    (CompactSpecifiedCapShrink.diagonal_in_near α β s hs) q
  change HomologicalComplex.homologyMap (push (swap (P := P) (Q := Q))) ((m + 1) + q) ≫
      (CompactSpecifiedCapShrink.smallOperation β α s hs).homology q =
    (DiagonalCutNaturality.operation (FarNormalizedDiagonalCap.dim_pos m)
      (StrictLengthProductFamilies.rightEvaluation β (P := P))
      (StrictLengthProductFamilies.leftEvaluation α (Q := Q))
      (CompactNormalizedJoinCapComparison.near α β s)
      (CompactNormalizedJoinCapComparison.near_open α β s)
      (fun z hz => CompactSpecifiedCapShrink.diagonal_in_near α β s hs z hz.symm)).homology q ≫
      HomologicalComplex.homologyMap (push (nearSwap α β s)) q at he
  rw [← hd] at he
  exact he

end
end Finsler.SmallThomSwap
