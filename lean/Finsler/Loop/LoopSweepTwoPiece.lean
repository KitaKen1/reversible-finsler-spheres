module

public import Finsler.Loop.BasedLoopTransgressionPrimitive

/-! The actual sweep split applies to families with a MOVING common
basepoint too. Only the two genuine evaluation-time map identities
are required, not a fixed-basepoint product or a loop-rank premise. -/
@[expose] public section
namespace Finsler.LoopSweepTwoPiece
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.BasedLoopTransgressionPrimitive
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {n : ℕ} {X : TopCat.{0}} (f g h : X ⟶ ContinuousLoopModel.space n)
  (hf : UncappedTimeSplit.first (timeMap f) = timeMap g)
  (hs : UncappedTimeSplit.second (timeMap f) = timeMap h)

include hf hs in
theorem cycles_split (q : ℕ) :
    cycleMap f q = cycleMap g q + cycleMap h q +
      ((chains X).iCycles q ≫ UncappedTimeSplit.comparison (timeMap f) q) ≫
        (chains (BorelEvaluation.sphere n)).toCycles (q + 2) (q + 1) := by
  apply (cancel_mono ((chains (BorelEvaluation.sphere n)).iCycles (q + 1))).mp
  simp only [Preadditive.add_comp, cycleMap_i, Category.assoc, HomologicalComplex.toCycles_i]
  have he := UncappedTimeSplit.full_split (timeMap f) q
  rw [hf, hs] at he
  simpa only [original_prism, Category.assoc] using he

include hf hs in
theorem homology_split (q : ℕ) :
    homologyPushZMod2 f q ≫ ContinuousLoopSweep.homology n q =
      homologyPushZMod2 g q ≫ ContinuousLoopSweep.homology n q +
      homologyPushZMod2 h q ≫ ContinuousLoopSweep.homology n q := by
  apply (cancel_epi ((chains X).homologyπ q)).mp
  rw [Preadditive.comp_add, homologyπ_sweep, homologyπ_sweep, homologyπ_sweep,
    cycles_split f g h hf hs]
  simp only [Preadditive.add_comp, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, comp_zero, add_zero]

include hf hs in
theorem transgression_split (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback f q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback g q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback h q).hom (ContinuousLoopSweep.transgression n q a) := by
  apply kroneckerMap_injective X q
  apply LinearMap.ext
  intro z
  have hpair (k : X ⟶ ContinuousLoopModel.space n) :
      (kroneckerMap X q).hom
        ((cohPullback k q).hom (ContinuousLoopSweep.transgression n q a)) z =
      (kroneckerMap (BorelEvaluation.sphere n) (q + 1)).hom a
        ((ContinuousLoopSweep.homology n q).hom ((homologyPushZMod2 k q).hom z)) := by
    have hn := congrArg (fun v : homologyDualZMod2 X q => v z)
      (kroneckerMap_naturality_apply k q (ContinuousLoopSweep.transgression n q a))
    exact hn.trans (ContinuousLoopSweep.pairing n q a ((homologyPushZMod2 k q).hom z))
  simp only [map_add, LinearMap.add_apply]
  rw [hpair, hpair, hpair]
  have he := ConcreteCategory.congr_hom (homology_split f g h hf hs q) z
  change (ContinuousLoopSweep.homology n q).hom ((homologyPushZMod2 f q).hom z) =
    (ContinuousLoopSweep.homology n q).hom ((homologyPushZMod2 g q).hom z) +
    (ContinuousLoopSweep.homology n q).hom ((homologyPushZMod2 h q).hom z) at he
  rw [he, map_add]

theorem cohomology_homotopy {Y Z : TopCat.{0}} {a b : Y ⟶ Z}
    (H : TopCat.Homotopy a b) (q : ℕ) (c : cohomologyZMod2 Z q) :
    (cohPullback a q).hom c = (cohPullback b q).hom c := by
  apply kroneckerMap_injective Y q
  rw [kroneckerMap_naturality_apply, kroneckerMap_naturality_apply]
  have he : homologyPushZMod2 a q = homologyPushZMod2 b q :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H _ q
  rw [he]

end
end Finsler.LoopSweepTwoPiece
