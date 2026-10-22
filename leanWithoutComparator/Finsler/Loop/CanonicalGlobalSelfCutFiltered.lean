module

public import Finsler.Loop.CanonicalGlobalSelfCut

/-! The canonical cohomology-class global cut is the ACTUAL full
image of the ORIGINAL filtered canonical cut, with its original
strict output length<a-L+3epsilon and every output degree retained. -/
@[expose] public section
namespace Finsler.CanonicalGlobalSelfCutFiltered
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem original_filtered (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (F : ReversibleMetric (m + 1))
    {ε a L : ℝ} (hε : 0 < ε)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
    (hs : cochainPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F L)) p T = 0)
    (q : ℕ) (z : homologyZMod2 (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q)) :
    (homologyPushZMod2 (SupportedCap.subspaceMap (Loops (m + 1))
      (SelfCutOscillation.short F (a - L + 3 * ε))) q).hom
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hs (a := a)).homology q).hom z) =
      (CanonicalGlobalSelfCut.map m p q (cocycleClass _ p T hT)).hom
        ((homologyPushZMod2 (SupportedCap.subspaceMap (Loops (m + 1))
          (SelfCutOscillation.short F a)) ((m + p) + q)).hom z) := by
  apply KroneckerHomologyExt.homology_ext (Loops (m + 1)) q
  intro B
  obtain ⟨b, hb, rfl⟩ := cocycleClass_surjective (Loops (m + 1)) q B
  have h := CanonicalTimeCupFilteredPairing.pairing m hm p F hε T hT hs q b hb z
  have hn := congrArg (fun φ : homologyDualZMod2 (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q) => φ z)
    (kroneckerMap_naturality_apply (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F a))
      ((m + p) + q) (CanonicalGlobalTimeCup.product m p q (cocycleClass _ p T hT) (cocycleClass _ q b hb)))
  exact h.symm.trans (hn.trans (CanonicalGlobalSelfCut.pairing m p q _ _ _).symm)

end
end Finsler.CanonicalGlobalSelfCutFiltered
