module

public import Finsler.Loop.RelativeTimeCup
public import Finsler.Loop.ConstantRelativePairing

/-! Genuine relative cohomology evaluation on the ORIGINAL fullPair
relative homology quotient equals the original canonical filtered D_T
pairing, in the verified high-output-degree range. -/

@[expose] public section
namespace Finsler.RelativeCanonicalTimeCupPairing
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem pairing (m p : ℕ) (F : ReversibleMetric (m + 1)) {ε a L : ℝ} (hε : 0 < ε)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
    (hshort : cochainPullback (SupportedCap.subspaceMap (Loops (m + 1))
      (SelfCutOscillation.short F L)) p T = 0)
    (q : ℕ) (hk : (m + 1) + 1 < (m + p) + q)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q)
    (hB : cochainCoboundary (ZMod 2) (Loops (m + 1)) q B = 0)
    (z : PoolCap.homology (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q)) :
    RelativeKronecker.comparison (fullPair (m + 1)) ((m + p) + q)
      (RelativeTimeCup.ofAbsolute m p q (half_pos (SelfCutLengthControl.radius_spec F hε).1)
        (half_lt_self (SelfCutLengthControl.radius_spec F hε).1)
        (SelfCutLengthControl.radius_spec F hε).2.1 hk (cocycleClass _ p T hT) (cocycleClass _ q B hB))
      (ConstantRelativePairing.homologyToRelative (m + 1) ((m + p) + q)
        ((PoolCap.push (SupportedCap.subspaceMap (Loops (m + 1))
          (SelfCutOscillation.short F a)) ((m + p) + q)).hom z)) =
    (kroneckerMap (Loops (m + 1)) q).hom (cocycleClass _ q B hB)
      ((PoolCap.push (SupportedCap.subspaceMap (Loops (m + 1))
        (SelfCutOscillation.short F (a - L + 3 * ε))) q).hom
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort (a := a)).homology q).hom z)) := by
  rw [RelativeTimeCup.ofAbsolute, ConstantRelativePairing.pairing]
  have h := GlobalFilteredTimeCup.pairing m p F hε T hT hshort q B hB z
  rw [kroneckerMap_naturality_apply] at h
  exact h

end
end Finsler.RelativeCanonicalTimeCupPairing
