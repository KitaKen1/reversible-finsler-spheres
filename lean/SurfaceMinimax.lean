import Finsler.Topology.BirkhoffDescent
import Finsler.Geometry.CriticalLevels
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.DiskSphere
import HingstonFilling

/-!
# Critical geodesics detected by relative homology

For the genuine Sobolev energy sublevels, a failure of injectivity of a
relative singular homology inclusion forces a regular closed geodesic in
the intervening length interval. The proof uses polygonal Birkhoff descent,
Tau Ceti's homotopy invariance, and the proved regularity of critical loops.
It applies in particular to dimension two, without a bumpiness assumption.

This is the critical-value extraction step in the surface minimax argument.
The explicit Hingston base slide constructs the filling from quantitative
local-family bounds. Producing a nonzero local class is still required.
-/

namespace Finsler.SurfaceMinimax

open CategoryTheory CategoryTheory.Limits Set
open Finsler.Geometry Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.SobolevCurveVariation

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- In the absence of regular closed geodesics in a positive closed length
interval, polygonal shortening gives an energy-decreasing deformation across
that entire interval. No finiteness assumption on the geodesics is needed. -/
theorem level_deformation_of_no_geodesic (hn : 1 ≤ n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hgap : ∀ g : Geodesics.ClosedGeodesic F,
      a ≤ Real.sqrt (LoopEnergy.energy F g.loop) →
      Real.sqrt (LoopEnergy.energy F g.loop) ≤ b → False) :
    Nonempty (RegularInterval.LevelDeformation F a b b) := by
  obtain ⟨S, k, hk⟩ := BirkhoffDescent.exists_descent F hn ha hab le_rfl (by
    intro u hu hlo hhi
    have hE : 0 < energy F u := lt_of_lt_of_le (sq_pos_of_pos ha) hlo
    obtain ⟨g, rfl⟩ :=
      (SobolevGeodesicCritical.tangentCritical_iff_closedGeodesic F u hE).mp hu
    rw [SmoothSobolev.energy_ofSmooth] at hlo hhi
    apply hgap g
    · exact (Real.le_sqrt ha.le (LoopEnergy.energy_nonneg F g.loop)).mpr hlo
    · exact (Real.sqrt_le_left (ha.le.trans hab)).mpr hhi)
  exact ⟨Shortening.levelDeformation S k hk⟩

/-- Inclusion on actual relative singular homology of energy sublevels,
with a fixed lower sublevel. Coefficients may be any field. -/
abbrev inclusion (K : Type) [Field K] {c a b : ℝ} (hca : c ≤ a) (hab : a ≤ b)
    (q : ℕ) :=
  (pairOf (lev_mono F hca)).singularHomologyMap
    (incPair (lev_mono F hca) (lev_mono F hab)) (ModuleCat.of K K) q

/-- A homology class cannot die across an interval without closed geodesics.
This uses Tau Ceti's relative singular homology, not an abstract replacement
of the loop space or its homology. -/
theorem inclusion_bijective_of_no_geodesic (hn : 1 ≤ n)
    (K : Type) [Field K] {c a b : ℝ} (ha : 0 < a) (hca : c ≤ a) (hab : a ≤ b)
    (hgap : ∀ g : Geodesics.ClosedGeodesic F,
      a ≤ Real.sqrt (LoopEnergy.energy F g.loop) →
      Real.sqrt (LoopEnergy.energy F g.loop) ≤ b → False) (q : ℕ) :
    Function.Bijective (inclusion F K hca hab q) := by
  obtain ⟨D⟩ := level_deformation_of_no_geodesic F hn ha hab hgap
  let d := BorelDeformation.toPair (RegularInterval.toDeformation D c)
  obtain ⟨H⟩ := BorelDeformation.nonempty_homotopy_left
    (lev_mono F hca) ((lev_mono F hca).trans (lev_mono F hab))
    subset_rfl (lev_mono F hab) d
  obtain ⟨H'⟩ := BorelDeformation.nonempty_homotopy_right
    (lev_mono F hca) ((lev_mono F hca).trans (lev_mono F hab))
    subset_rfl (lev_mono F hab) d
  have : IsIso (inclusion F K hca hab q) :=
    TopPair.isIso_singularHomologyMap _ _ H H' (ModuleCat.of K K) q
  exact ConcreteCategory.bijective_of_isIso (inclusion F K hca hab q)

/-- If inclusion kills a nonzero relative homology class, the length interval
contains an actual regular stationary closed geodesic. -/
theorem exists_geodesic_of_not_injective (hn : 1 ≤ n)
    (K : Type) [Field K] {c a b : ℝ} (ha : 0 < a) (hca : c ≤ a) (hab : a ≤ b)
    (q : ℕ) (hdeath : ¬ Function.Injective (inclusion F K hca hab q)) :
    ∃ g : Geodesics.ClosedGeodesic F,
      a ≤ Real.sqrt (LoopEnergy.energy F g.loop) ∧
      Real.sqrt (LoopEnergy.energy F g.loop) ≤ b := by
  by_contra h
  apply hdeath
  exact (inclusion_bijective_of_no_geodesic F hn K ha hca hab
    (fun g hlo hhi => h ⟨g, hlo, hhi⟩) q).1

/-- A nonzero disk class dies if its inclusion factors through a disk pair of
a different dimension. This implements the homological part of the enlarged
parameter-domain construction in the Hingston argument: no explicit singular
chain filling needs to be constructed. The maps still have to respect the
actual energy bounds, including the boundary bound at the fixed lower cut. -/
theorem not_injective_of_disk_filling (K : Type) [Field K]
    {c a b : ℝ} (hca : c ≤ a) (hab : a ≤ b) {q r : ℕ} (hqr : q ≠ r)
    (f : TauCeti.diskBoundaryPair q ⟶ pairOf (lev_mono F hca))
    (j : TauCeti.diskBoundaryPair q ⟶ TauCeti.diskBoundaryPair r)
    (G : TauCeti.diskBoundaryPair r ⟶
      pairOf ((lev_mono F hca).trans (lev_mono F hab)))
    (hnonzero : TopPair.singularHomologyMap f (ModuleCat.of K K) q ≠ 0)
    (hfill : f ≫ incPair (lev_mono F hca) (lev_mono F hab) = j ≫ G) :
    ¬ Function.Injective (inclusion F K hca hab q) := by
  have hz : TopPair.singularHomologyMap j (ModuleCat.of K K) q = 0 :=
    (TauCeti.isZero_singularHomology_diskBoundaryPair_of_ne
      (ModuleCat.of K K) hqr).eq_of_tgt _ _
  have hcomp : TopPair.singularHomologyMap f (ModuleCat.of K K) q ≫
      inclusion F K hca hab q = 0 := by
    rw [inclusion, ← TopPair.singularHomologyMap_comp, hfill,
      TopPair.singularHomologyMap_comp, hz, zero_comp]
  intro hinj
  have : Mono (inclusion F K hca hab q) :=
    (ModuleCat.mono_iff_injective _).mpr hinj
  apply hnonzero
  apply (cancel_mono (inclusion F K hca hab q)).mp
  simpa only [zero_comp] using hcomp

/-- A nonzero local disk class together with an enlarged disk filling forces
a closed geodesic between the two positive length cuts. -/
theorem exists_geodesic_of_disk_filling (hn : 1 ≤ n) (K : Type) [Field K]
    {c a b : ℝ} (ha : 0 < a) (hca : c ≤ a) (hab : a ≤ b)
    {q r : ℕ} (hqr : q ≠ r)
    (f : TauCeti.diskBoundaryPair q ⟶ pairOf (lev_mono F hca))
    (j : TauCeti.diskBoundaryPair q ⟶ TauCeti.diskBoundaryPair r)
    (G : TauCeti.diskBoundaryPair r ⟶
      pairOf ((lev_mono F hca).trans (lev_mono F hab)))
    (hnonzero : TopPair.singularHomologyMap f (ModuleCat.of K K) q ≠ 0)
    (hfill : f ≫ incPair (lev_mono F hca) (lev_mono F hab) = j ≫ G) :
    ∃ g : Geodesics.ClosedGeodesic F,
      a ≤ Real.sqrt (LoopEnergy.energy F g.loop) ∧
      Real.sqrt (LoopEnergy.energy F g.loop) ≤ b :=
  exists_geodesic_of_not_injective F hn K ha hca hab q
    (not_injective_of_disk_filling F K hca hab hqr f j G hnonzero hfill)

/-- The disk-filling criterion only requires factorization up to a homotopy
of pairs. This permits the energy-nonincreasing diagonal pause removal to be
used without imposing literal equality of the two loop parametrizations. -/
theorem not_injective_of_homotopic_disk_filling (K : Type) [Field K]
    {c a b : ℝ} (hca : c ≤ a) (hab : a ≤ b) {q r : ℕ} (hqr : q ≠ r)
    (f : TauCeti.diskBoundaryPair q ⟶ pairOf (lev_mono F hca))
    (j : TauCeti.diskBoundaryPair q ⟶ TauCeti.diskBoundaryPair r)
    (G : TauCeti.diskBoundaryPair r ⟶
      pairOf ((lev_mono F hca).trans (lev_mono F hab)))
    (hnonzero : TopPair.singularHomologyMap f (ModuleCat.of K K) q ≠ 0)
    (H : TopPair.Homotopy (f ≫ incPair (lev_mono F hca) (lev_mono F hab)) (j ≫ G)) :
    ¬ Function.Injective (inclusion F K hca hab q) := by
  have hz : TopPair.singularHomologyMap j (ModuleCat.of K K) q = 0 :=
    (TauCeti.isZero_singularHomology_diskBoundaryPair_of_ne
      (ModuleCat.of K K) hqr).eq_of_tgt _ _
  have hcomp : TopPair.singularHomologyMap f (ModuleCat.of K K) q ≫
      inclusion F K hca hab q = 0 := by
    rw [inclusion, ← TopPair.singularHomologyMap_comp,
      H.congr_singularHomologyMap (ModuleCat.of K K) q,
      TopPair.singularHomologyMap_comp, hz, zero_comp]
  intro hinj
  have : Mono (inclusion F K hca hab q) := (ModuleCat.mono_iff_injective _).mpr hinj
  apply hnonzero
  apply (cancel_mono (inclusion F K hca hab q)).mp
  simpa only [zero_comp] using hcomp

/-- A filling up to a boundary-preserving homotopy suffices to extract an
actual regular closed geodesic. The maps and their nonzero class are inputs. -/
theorem exists_geodesic_of_homotopic_disk_filling (hn : 1 ≤ n) (K : Type) [Field K]
    {c a b : ℝ} (ha : 0 < a) (hca : c ≤ a) (hab : a ≤ b)
    {q r : ℕ} (hqr : q ≠ r)
    (f : TauCeti.diskBoundaryPair q ⟶ pairOf (lev_mono F hca))
    (j : TauCeti.diskBoundaryPair q ⟶ TauCeti.diskBoundaryPair r)
    (G : TauCeti.diskBoundaryPair r ⟶
      pairOf ((lev_mono F hca).trans (lev_mono F hab)))
    (hnonzero : TopPair.singularHomologyMap f (ModuleCat.of K K) q ≠ 0)
    (H : TopPair.Homotopy (f ≫ incPair (lev_mono F hca) (lev_mono F hab)) (j ≫ G)) :
    ∃ g : Geodesics.ClosedGeodesic F,
      a ≤ Real.sqrt (LoopEnergy.energy F g.loop) ∧
      Real.sqrt (LoopEnergy.energy F g.loop) ≤ b :=
  exists_geodesic_of_not_injective F hn K ha hca hab q
    (not_injective_of_homotopic_disk_filling F K hca hab hqr f j G hnonzero H)

section Hingston

open HingstonFilling HingstonConnectors CompactH1Alignment SobolevSpherePath

variable {Y : Type} [TopologicalSpace Y] (φ : C(I × Y, SphereLoop n))
  (hbase : ∀ x y z, basepoint (φ (x, y)) = basepoint (φ (x, z)))
  {ρ : ℝ} (hρ : ρ ≤ shortRadius F)
  (hnear : ∀ x x' y y', ‖basepoint (φ (x', y')) - basepoint (φ (x, y))‖ < ρ)
  (r s : ℕ) {c : ℝ} (hc : 0 < c)
  (hpath : ∀ p : NearPairs F, ‖basepoint p.val.2 - basepoint p.val.1‖ < ρ →
    pathEnergy F (shortData F p).val.2.2 ≤ c ^ 2)
  {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε)
  (BY : Set Y) (bounds : EnergyBounds F φ BY l ε c r s)
  {a : ℝ} (ha : ((r : ℝ) + 1 + ((s : ℝ) + 1)) * l < a)
  (hab : a ≤ ((r : ℝ) + 1 + ((s : ℝ) + 1)) * l + ε)

/-- The explicit Hingston filling kills a nonzero repeated local class.
Only nonvanishing and quantitative bounds on the initial family are inputs;
the filling and the homology death are proved by the base-interval slide. -/
theorem not_injective_of_block_filling (K : Type) [Field K] (q : ℕ)
    (hnonzero : TopPair.singularHomologyMap
      (lowerBlockPairMap F φ hbase hρ hnear r s hc hpath hl hε BY bounds ha)
      (ModuleCat.of K K) q ≠ 0) :
    ¬ Function.Injective (inclusion F K ha.le hab q) := by
  have hcomp : TopPair.singularHomologyMap
      (lowerBlockPairMap F φ hbase hρ hnear r s hc hpath hl hε BY bounds ha)
      (ModuleCat.of K K) q ≫ inclusion F K ha.le hab q = 0 := by
    rw [inclusion, ← TopPair.singularHomologyMap_comp,
      lowerBlockPairMap_comp F φ hbase hρ hnear r s hc hpath hl hε BY bounds ha hab,
      block_homology_eq_zero]
  intro hinj
  have : Mono (inclusion F K ha.le hab q) := (ModuleCat.mono_iff_injective _).mpr hinj
  apply hnonzero
  apply (cancel_mono (inclusion F K ha.le hab q)).mp
  simpa only [zero_comp] using hcomp

include hab in
/-- From a nonzero repeated local class, obtain an actual regular closed
geodesic strictly above the repeated length and within the prescribed margin. -/
theorem exists_geodesic_of_block_filling (hn : 1 ≤ n) (K : Type) [Field K] (q : ℕ)
    (hnonzero : TopPair.singularHomologyMap
      (lowerBlockPairMap F φ hbase hρ hnear r s hc hpath hl hε BY bounds ha)
      (ModuleCat.of K K) q ≠ 0) :
    ∃ g : Geodesics.ClosedGeodesic F,
      ((r : ℝ) + 1 + ((s : ℝ) + 1)) * l < Real.sqrt (LoopEnergy.energy F g.loop) ∧
      Real.sqrt (LoopEnergy.energy F g.loop) ≤ ((r : ℝ) + 1 + ((s : ℝ) + 1)) * l + ε := by
  obtain ⟨g, hg, hg'⟩ := exists_geodesic_of_not_injective F hn K
    (lt_trans (by positivity) ha) ha.le hab q
    (not_injective_of_block_filling F φ hbase hρ hnear r s hc hpath hl hε BY bounds ha hab
      K q hnonzero)
  exact ⟨g, ha.trans_le hg, hg'⟩

end Hingston

end

end Finsler.SurfaceMinimax
