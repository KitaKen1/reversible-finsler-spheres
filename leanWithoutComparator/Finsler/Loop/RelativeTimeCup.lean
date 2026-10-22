module

public import Finsler.Loop.ConstantRelativeLift
public import Finsler.Loop.GlobalFilteredTimeCup

/-! A genuine HIGH OUTPUT DEGREE relative time-cup operation on the
original full H1-loop pair. The canonical lift is forced by the actual
relative-to-absolute isomorphism. Identification with manuscript GH
generators, all-degree algebra and ordinary-loop models remains separate. -/

@[expose] public section
namespace Finsler.RelativeTimeCup
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

def absolute (n k : ℕ) : RelativeCup.cohomology (fullPair n) k →ₗ[ZMod 2] cohomologyZMod2 (Loops n) k :=
  (FullLoopModel.cohomologyEquiv n k).symm.toLinearMap.comp (relativeToPool (fullPair n) k).hom

variable (m p q : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (hk : (m + 1) + 1 < (m + p) + q)

def ofAbsolute (a : cohomologyZMod2 (Loops (m + 1)) p)
    (b : cohomologyZMod2 (Loops (m + 1)) q) :
    RelativeCup.cohomology (fullPair (m + 1)) ((m + p) + q) :=
  ConstantRelativeLift.lift (m + 1) ((m + p) + q) hk
    (GlobalTimeCupCohomology.product m hρ hρr hr p q a b)

def product (a : RelativeCup.cohomology (fullPair (m + 1)) p)
    (b : RelativeCup.cohomology (fullPair (m + 1)) q) :
    RelativeCup.cohomology (fullPair (m + 1)) ((m + p) + q) :=
  ofAbsolute m p q hρ hρr hr hk (absolute (m + 1) p a) (absolute (m + 1) q b)

theorem ofAbsolute_spec (a : cohomologyZMod2 (Loops (m + 1)) p)
    (b : cohomologyZMod2 (Loops (m + 1)) q) :
    absolute (m + 1) ((m + p) + q) (ofAbsolute m p q hρ hρr hr hk a b) =
      GlobalTimeCupCohomology.product m hρ hρr hr p q a b := by
  change ConstantRelativeLift.equiv (m + 1) ((m + p) + q) hk
    ((ConstantRelativeLift.equiv (m + 1) ((m + p) + q) hk).symm _) = _
  exact (ConstantRelativeLift.equiv (m + 1) ((m + p) + q) hk).apply_symm_apply _

theorem product_spec (a : RelativeCup.cohomology (fullPair (m + 1)) p)
    (b : RelativeCup.cohomology (fullPair (m + 1)) q) :
    absolute (m + 1) ((m + p) + q) (product m p q hρ hρr hr hk a b) =
      GlobalTimeCupCohomology.product m hρ hρr hr p q (absolute (m + 1) p a) (absolute (m + 1) q b) :=
  ofAbsolute_spec m p q hρ hρr hr hk _ _

theorem ofAbsolute_unique (a : cohomologyZMod2 (Loops (m + 1)) p)
    (b : cohomologyZMod2 (Loops (m + 1)) q)
    (c : RelativeCup.cohomology (fullPair (m + 1)) ((m + p) + q))
    (hc : absolute (m + 1) ((m + p) + q) c = GlobalTimeCupCohomology.product m hρ hρr hr p q a b) :
    c = ofAbsolute m p q hρ hρr hr hk a b := by
  apply (ConstantRelativeLift.equiv (m + 1) ((m + p) + q) hk).injective
  change absolute (m + 1) ((m + p) + q) c = absolute (m + 1) ((m + p) + q) _
  rw [hc, ofAbsolute_spec]

end
end Finsler.RelativeTimeCup
