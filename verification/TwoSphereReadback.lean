import Lean
import FCTwoSphere
import SurfaceLocalHomology
import SurfacePolygonHomology
import SurfaceMorseData
import SurfaceSpectralDisk
import SurfacePhaseGeometry
import SurfaceIteration
import SurfaceIterationHomology
import SurfaceIterationEquivalence
import SurfaceZeroMeanIndex
import SurfaceOrbitModel

open Lean Elab Command ReversibleFinslerSphereFC

/-! Check the exact two-sphere criterion, including its still-needed geometric
input, and audit every new public theorem. No FC placeholder is imported. -/

example (F : Finsler.Geometry.ReversibleMetric 2) (l : ℝ) (hl : 0 < l)
    (h : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Odd m →
      ∃ g : Finsler.Geodesics.ClosedGeodesic F,
        (m : ℝ) * l < Real.sqrt (Finsler.LoopEnergy.energy F g.loop) ∧
        Real.sqrt (Finsler.LoopEnergy.energy F g.loop) ≤ (m : ℝ) * l + ε) :
    (PrimeClosedGeodesicImages F).Infinite :=
  infinite_prime_images_of_odd_length_approximation F l hl h

example (F : Finsler.Geometry.ReversibleMetric 2)
    (h : ∀ p : Finsler.SphereGeometry.Sphere 2,
      ∃ g : Finsler.Geodesics.ClosedGeodesic F, ∃ t : ℝ, g.loop t = p) :
    (PrimeClosedGeodesicImages F).Infinite :=
  infinite_prime_images_of_geodesic_cover F (by omega) h

example (F : Finsler.Geometry.ReversibleMetric 2) (l : ℝ) (hl : 0 < l)
    (h : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Odd m →
      ∃ (a b : ℝ) (hma : (m : ℝ) * l < a) (hab : a ≤ b),
        b ≤ (m : ℝ) * l + ε ∧ ∃ q : ℕ,
          ¬ Function.Injective
            (Finsler.SurfaceMinimax.inclusion F (ZMod 2) hma.le hab q)) :
    (PrimeClosedGeodesicImages F).Infinite :=
  infinite_prime_images_of_odd_homology_death F (by omega) (ZMod 2) l hl h

example (F : Finsler.Geometry.ReversibleMetric 2) {c a b : ℝ}
    (ha : 0 < a) (hca : c ≤ a) (hab : a ≤ b) (q : ℕ)
    (h : ¬ Function.Injective (Finsler.SurfaceMinimax.inclusion F (ZMod 2) hca hab q)) :
    ∃ g : Finsler.Geodesics.ClosedGeodesic F,
      a ≤ Real.sqrt (Finsler.LoopEnergy.energy F g.loop) ∧
      Real.sqrt (Finsler.LoopEnergy.energy F g.loop) ≤ b :=
  Finsler.SurfaceMinimax.exists_geodesic_of_not_injective F (by omega)
    (ZMod 2) ha hca hab q h

example (F : Finsler.Geometry.ReversibleMetric 2) (u : Finsler.HingstonBlocks.Blocks 2 2) :
    Finsler.SobolevEnergy.energy F (Finsler.HingstonBlocks.concat u) =
      3 * ∑ i, Finsler.SobolevEnergy.energy F (u.val i) := by
  have h := Finsler.HingstonBlocks.energy_concat F u
  norm_num at h
  exact h

example (u : Finsler.IntervalSobolev.SphereLoop 2) (m : ℕ) :
    Finsler.HingstonBlocks.concat (Finsler.HingstonBlocks.diagonal u m) =
      Finsler.SobolevIteration.iterateSphere u (m + 1) (by omega) :=
  Finsler.HingstonBlocks.concat_diagonal u m

example (F : Finsler.Geometry.ReversibleMetric 2) (p : Finsler.HingstonConnectors.Data 2) :
    Finsler.SobolevEnergy.energy F
      (Finsler.HingstonConnectors.loop (a := 1) (b := 1) (c := 1)
        (by norm_num) (by norm_num) (by norm_num) p) =
      4 * (Finsler.SobolevEnergy.energy F p.val.1 +
        Finsler.SobolevEnergy.energy F p.val.2.1 +
        2 * Finsler.SobolevSpherePath.pathEnergy F p.val.2.2) := by
  have h := Finsler.HingstonConnectors.energy_loop
    (a := 1) (b := 1) (c := 1) (by norm_num) (by norm_num) (by norm_num) F p
  norm_num at h
  exact h

/- The concrete S² connector homotopy preserves any positive cut that
contains its actual start, at every time including zero-pause time one. -/
example (F : Finsler.Geometry.ReversibleMetric 2)
    (p : Finsler.H1JoinContinuity.composable 2) {l : ℝ} (hl : 0 < l)
    (t : _root_.unitInterval)
    (hp : Finsler.HingstonConnectors.shortLoop (a := 1) (b := 1) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) F
      (Finsler.HingstonConnectors.diagonalPairs F p) ∈ Finsler.BorelLoop.lev F l) :
    Finsler.HingstonPause.diagonalHomotopy (a := 1) (b := 1) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) F (t, p) ∈ Finsler.BorelLoop.lev F l :=
  Finsler.HingstonPause.diagonalHomotopy_mem_lev _ _ _ F hl t p hp

/- Two unequal groups of iterates recover the exact five-fold iterate,
checking the weights as well as the fact that the pause disappears. -/
example (F : Finsler.Geometry.ReversibleMetric 2)
    (u : Finsler.IntervalSobolev.SphereLoop 2) :
    Finsler.HingstonPause.diagonalHomotopy (a := 2) (b := 3) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) F
      (1, Finsler.HingstonPause.iteratePair u 2 3 (by norm_num) (by norm_num)) =
    Finsler.SobolevIteration.iterateSphere u 5 (by norm_num) := by
  simpa using Finsler.HingstonPause.diagonalHomotopy_iterates_end
    (c := 1) (by norm_num) F u 2 3 (by norm_num) (by norm_num)

/- The new filling-to-geodesic connection is instantiated on S², with
unequal groups (two plus three blocks), actual energy cuts and Z/2 coefficients. -/
section ConcreteFilling
open Finsler.HingstonFilling Finsler.HingstonConnectors
open Finsler.CompactH1Alignment Finsler.IntervalSobolev Finsler.SobolevSpherePath

example (F : Finsler.Geometry.ReversibleMetric 2) {Y : Type} [TopologicalSpace Y]
    (φ : C(I × Y, SphereLoop 2))
    (hbase : ∀ x y z, basepoint (φ (x, y)) = basepoint (φ (x, z)))
    {ρ c l ε a : ℝ} (hρ : ρ ≤ shortRadius F)
    (hnear : ∀ x x' y y', ‖basepoint (φ (x', y')) - basepoint (φ (x, y))‖ < ρ)
    (hc : 0 < c)
    (hpath : ∀ p : NearPairs F, ‖basepoint p.val.2 - basepoint p.val.1‖ < ρ →
      pathEnergy F (shortData F p).val.2.2 ≤ c ^ 2)
    (hl : 0 < l) (hε : 0 < ε) (BY : Set Y)
    (bounds : EnergyBounds F φ BY l ε c 1 2)
    (ha : 5 * l < a) (hab : a ≤ 5 * l + ε) (q : ℕ)
    (hnonzero : TopPair.singularHomologyMap
      (lowerBlockPairMap F φ hbase hρ hnear 1 2 hc hpath hl hε BY bounds
        (by norm_num; exact ha)) (ModuleCat.of (ZMod 2) (ZMod 2)) q ≠ 0) :
    ∃ g : Finsler.Geodesics.ClosedGeodesic F,
      5 * l < Real.sqrt (Finsler.LoopEnergy.energy F g.loop) ∧
      Real.sqrt (Finsler.LoopEnergy.energy F g.loop) ≤ 5 * l + ε := by
  have h := Finsler.SurfaceMinimax.exists_geodesic_of_block_filling F φ hbase hρ hnear
    1 2 hc hpath hl hε BY bounds (by norm_num; exact ha) (by norm_num; exact hab)
    (by omega) (ZMod 2) q hnonzero
  norm_num at h
  exact h

end ConcreteFilling

/- A degenerate quartic maximum with a positive transverse direction has
an actual nonzero local homology class. This checks the coordinate detector
on a concrete saddle, with the same mod-two coefficients as the surface proof. -/
section ConcreteLocalClass
open Finsler.SurfaceLocalHomology

private noncomputable def saddleEnergy (x : Disk 2 × ℝ) : ℝ :=
  x.2 ^ 2 - ‖coordinates 2 x.1‖ ^ 4

private theorem saddle_strict_maximum (x : Disk 2) (hx : x ≠ center 2) :
    saddleEnergy (x, 0) < saddleEnergy (center 2, 0) := by
  have hn : 0 < ‖coordinates 2 x‖ :=
    norm_pos_iff.mpr (fun h => hx ((coordinates_eq_zero_iff 2 x).mp h))
  have hc : coordinates 2 (center 2) = 0 := rfl
  change (0 : ℝ) ^ 2 - ‖coordinates 2 x‖ ^ 4 < 0 ^ 2 - ‖coordinates 2 (center 2)‖ ^ 4
  rw [hc, norm_zero]
  nlinarith [pow_pos hn 4]

example :
    TopPair.singularHomologyMap
      (familyMap saddleEnergy (saddleEnergy (center 2, 0)) (productFamily (q := 2) (0 : ℝ))
        (fun x => saddle_strict_maximum _ (boundary_ne_center 2 x)))
      (ModuleCat.of (ZMod 2) (ZMod 2)) 2 (diskClass 2 (ZMod 2)) ≠ 0 := by
  apply product_class_ne_zero saddleEnergy (0 : ℝ) saddle_strict_maximum
  intro z
  have hc : coordinates 2 (center 2) = 0 := rfl
  change (0 : ℝ) ^ 2 - ‖coordinates 2 (center 2)‖ ^ 4 ≤
    z ^ 2 - ‖coordinates 2 (center 2)‖ ^ 4
  rw [hc, norm_zero]
  nlinarith [sq_nonneg z]

/- The generator also lives in the lower sublevel with only the critical
point adjoined, rather than requiring positive-energy points. -/
example :
    TopPair.singularHomologyMap
      (familyMap
        (fun x : criticalCarrier saddleEnergy (center 2, (0 : ℝ)) => saddleEnergy x.val)
        (saddleEnergy (center 2, 0))
        (criticalFamily saddleEnergy (productFamily (q := 2) (0 : ℝ)) saddle_strict_maximum)
        (fun x => saddle_strict_maximum _ (boundary_ne_center 2 x)))
      (ModuleCat.of (ZMod 2) (ZMod 2)) 2 (diskClass 2 (ZMod 2)) ≠ 0 := by
  apply criticalClass_ne_zero saddleEnergy (productFamily (q := 2) (0 : ℝ))
    ⟨Prod.fst, continuous_fst⟩ saddle_strict_maximum
  · intro x hx
    change x.1 = center 2 at hx
    have hc : coordinates 2 (center 2) = 0 := rfl
    change (0 : ℝ) ^ 2 - ‖coordinates 2 (center 2)‖ ^ 4 ≤
      x.2 ^ 2 - ‖coordinates 2 x.1‖ ^ 4
    rw [hx, hc, norm_zero]
    nlinarith [sq_nonneg x.2]
  · intro x
    rfl

end ConcreteLocalClass

section PolygonLocalComparison
open Finsler.SurfacePolygonHomology Finsler.SurfaceLocalHomology

/- The local-to-global neighborhood comparison is tested on an actual
proper open neighborhood of a degenerate saddle, with rational coefficients. -/
example : CategoryTheory.IsIso
    (TopPair.singularHomologyMap
      (criticalInclusion saddleEnergy {x : Disk 2 × ℝ | |x.2| < 1}
        ⟨(center 2, 0), by norm_num⟩) (ModuleCat.of ℚ ℚ) 2) := by
  apply isIso_criticalInclusion
  · unfold saddleEnergy
    fun_prop
  · exact isOpen_lt (continuous_abs.comp continuous_snd) continuous_const

/- Every genuine S² geodesic, including degenerate and iterated ones, has
a critical polygon presentation with exactly the original parametrization. -/
example (F : Finsler.Geometry.ReversibleMetric 2) (g : Finsler.Geodesics.ClosedGeodesic F)
    {a : ℝ} (ha : Finsler.SobolevEnergy.energy F (Finsler.SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    Nonempty (GeodesicModel F g a) := nonempty_geodesicModel F g ha

/- The degree-three local class uses rational coefficients, as in the
surface argument's odd-iterate local-to-orbit step. Its target here is the
actual H¹ critical carrier; an orbit inclusion is not smuggled into the type. -/
example (F : Finsler.Geometry.ReversibleMetric 2) {a : ℝ} {N : ℕ} [NeZero N]
    (M : Finsler.PolygonModel.PolygonModelData F a N) (p : Short M)
    (hp : polygonEnergy M p < a ^ 2) :
    Function.Injective (TopPair.singularHomologyMap (brokenPair M p) (ModuleCat.of ℚ ℚ) 3) :=
  brokenPair_homology_injective M p hp ℚ 3

end PolygonLocalComparison

section MorseDiskConstruction
open Finsler.SurfaceMorseData Finsler.SurfaceLocalHomology Finsler.SurfacePolygonHomology
open scoped Topology

/- The detector fixes the unit disk and has no extra preimage of the center,
including in dimension zero. -/
example (x : Disk 0) : clip 0 (coordinates 0 x) = x := clip_of_mem 0 x

example (x : EuclideanSpace ℝ (Fin 2)) : clip 2 x = center 2 ↔ x = 0 :=
  clip_eq_center_iff 2 x

/- A degenerate saddle on an actual open coordinate ball produces its own
small closed disk and detector; neither map is supplied to the theorem. -/
example : Nonempty (MaximalDiskData
    (fun x : EuclideanSpace ℝ (Fin 2) × ℝ => x.2 ^ 2 - ‖x.1‖ ^ 4) (0, 0) 2) := by
  let e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2) × ℝ)
      (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    OpenPartialHomeomorph.ofSet (Metric.ball 0 1) Metric.isOpen_ball
  apply nonempty_maximalDiskData_of_normalForm _ (0, 0) (0 : ℝ) e
    (by change (0, (0 : ℝ)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1; simp)
    rfl (fun v => -‖v‖ ^ 4) (fun z : ℝ => z ^ 2)
  · intro x hx
    change x.2 ^ 2 - ‖x.1‖ ^ 4 = -‖x.1‖ ^ 4 + x.2 ^ 2
    ring
  · apply Filter.Eventually.of_forall
    intro v hv
    have h := pow_pos (norm_pos_iff.mpr hv) 4
    simp only [norm_zero, zero_pow (by omega : 4 ≠ 0), neg_zero]
    linarith
  · intro z hz
    simpa using sq_nonneg z

/- Every genuine S² geodesic has actual splitting coordinates, including
the nonzero-edge condition, exact broken-loop reconstruction and energy cut. -/
example (F : Finsler.Geometry.ReversibleMetric 2) (g : Finsler.Geodesics.ClosedGeodesic F)
    {a : ℝ} (ha : Finsler.SobolevEnergy.energy F (Finsler.SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    Nonempty (GeodesicMorseModel F g a) := nonempty_geodesicMorseModel F g ha

/- The geometric disk data produce both an embedded actual loop family and
a nonzero point-local class, with rational coefficients in degree three. -/
example (F : Finsler.Geometry.ReversibleMetric 2) {a : ℝ} {N : ℕ} [NeZero N]
    (M : Finsler.PolygonModel.PolygonModelData F a N) (p : Short M)
    (D : MaximalDiskData (polygonEnergy M) p 3) (hp : polygonEnergy M p < a ^ 2) :
    Topology.IsClosedEmbedding (diskLoopFamily M p D) ∧
      ∃ f : TauCeti.diskBoundaryPair 3 ⟶ loopPair M p,
        TopPair.singularHomologyMap f (ModuleCat.of ℚ ℚ) 3 (diskClass 3 ℚ) ≠ 0 :=
  ⟨diskLoopFamily_isClosedEmbedding M p D, exists_nonzero_loopClass M p D hp ℚ⟩

end MorseDiskConstruction

section SpectralDiskConstruction
open Finsler.SurfaceSpectralDisk Finsler.SurfaceMorseData
open scoped Topology RealInnerProductSpace

/- A completely degenerate Hessian is allowed. The actual quartic maximum
on a two-dimensional space constructs a two-dimensional disk; its dimension
is checked, rather than left as an opaque spectral rank. -/
example : Nonempty (MaximalDiskData
    (fun x : EuclideanSpace ℝ (Fin 2) => -‖x‖ ^ 4) 0 2) := by
  let T : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) := 0
  have hs : T.toLinearMap.IsSymmetric := by intro x y; simp [T]
  have hU : nonpositive T hs = ⊤ := by
    apply top_unique
    intro x hx
    rw [nonpositive_eq]
    apply Submodule.mem_sup_right
    change T x = 0
    rfl
  have hdim : Module.finrank ℝ (nonpositive T hs) = 2 := by
    rw [hU, finrank_top]
    simp
  suffices h : Nonempty (MaximalDiskData
      (fun x : EuclideanSpace ℝ (Fin 2) => -‖x‖ ^ 4) 0
      (Module.finrank ℝ (nonpositive T hs))) from by simpa only [hdim] using h
  apply nonempty_maximalDiskData_of_spectralSplitting T hs
    (fun x : EuclideanSpace ℝ (Fin 2) => -‖x‖ ^ 4) 0
    (OpenPartialHomeomorph.refl _) (Set.mem_univ _) rfl (fun x => -‖x‖ ^ 4)
  · intro x hx
    simp only [OpenPartialHomeomorph.refl_apply, T, zero_apply,
      inner_zero_left, mul_zero, add_zero]
    rw [Finsler.LyapunovSchmidt.kerProj_of_map_eq_zero T rfl]
    rfl
  · apply Filter.Eventually.of_forall
    intro z hz
    have hne : (z : EuclideanSpace ℝ (Fin 2)) ≠ 0 := fun h => hz (Subtype.ext h)
    have hpos := pow_pos (norm_pos_iff.mpr hne) 4
    simp only [norm_zero, zero_pow (by decide : 4 ≠ 0), neg_zero]
    linarith

/- Removing a nonzero phase direction from a three-dimensional zero
Hessian leaves a genuine restricted operator with nullity exactly two. -/
example (v : EuclideanSpace ℝ (Fin 3)) (hv : v ≠ 0) :
    let T : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) := 0
    let hs : T.toLinearMap.IsSymmetric := by intro x y; simp [T]
    Module.finrank ℝ (LinearMap.ker (phaseRestriction (hT := hs) v rfl).toLinearMap) = 2 := by
  dsimp only
  have hs : (0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)).toLinearMap.IsSymmetric :=
    by intro x y; simp
  have h := phaseRestriction_nullity (hT := hs) v rfl hv
  have hd : Module.finrank ℝ
      (LinearMap.ker (0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)).toLinearMap) = 3 := by
    change Module.finrank ℝ (LinearMap.ker (0 : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))) = 3
    rw [LinearMap.ker_zero, finrank_top]
    simp
  rw [hd] at h
  omega

end SpectralDiskConstruction


open Finsler.SurfacePhaseGeometry Finsler.SurfaceSpectralDisk
open Finsler.SurfacePolygonHomology Finsler.PolygonHessian
open scoped Topology ContDiff RealInnerProductSpace
section ActualPhaseGeometry
set_option backward.isDefEq.respectTransparency true

/- A nonlinear curve is straightened with its original parameter. -/
example : ∃ e : OpenPartialHomeomorph ℝ (ℝ × phaseSlice (1 : ℝ)),
    (0 : ℝ) ∈ e.source ∧ e 0 = 0 ∧
    (∀ y, e.symm y = (y.1 + y.1 ^ 2) + (y.2 : ℝ)) ∧
    (∀ᶠ t in nhds (0 : ℝ), t + t ^ 2 ∈ e.source ∧ e (t + t ^ 2) = (t, 0)) := by
  apply exists_straightening (fun t : ℝ => t + t ^ 2)
  · exact (contDiff_id.add (contDiff_id.pow 2)).contDiffAt
  · norm_num
  · have hd := (hasDerivAt_id (0 : ℝ)).add ((hasDerivAt_id (0 : ℝ)).pow 2)
    have he : (id + id ^ 2 : ℝ → ℝ) = (fun t : ℝ => t + t ^ 2) := by funext t; rfl
    rw [he] at hd
    simpa using hd
  · norm_num

/- On S², the genuine transverse Hessian is obtained for an arbitrary
closed geodesic, using only its strict energy cut. -/
example (F : Finsler.Geometry.ReversibleMetric 2)
    (g : Finsler.Geodesics.ClosedGeodesic F) {a : ℝ}
    (ha : Finsler.SobolevEnergy.energy F (Finsler.SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    ∃ D : GeodesicPhaseModel F g a,
      HasFDerivAt (transverseGradient D)
        (Finsler.Hessian.operator (transverseEnergy D) 0) 0 ∧
      Module.finrank ℝ (LinearMap.ker (Finsler.Hessian.operator (transverseEnergy D) 0).toLinearMap) + 1 =
        nullity F (phasePoint D 0).val := by
  obtain ⟨D⟩ := nonempty_geodesicPhaseModel F g ha
  refine ⟨D, ?_, ?_⟩
  · rw [← transverseHessian_eq_operator]
    exact transverseGradient_hasFDerivAt D
  · rw [← transverseHessian_eq_operator]
    exact transverseHessian_nullity D

/- The energy is the energy of an actual broken H¹ loop on the phase-zero
slice of the constructed nonlinear chart. -/
example (F : Finsler.Geometry.ReversibleMetric 2)
    (g : Finsler.Geodesics.ClosedGeodesic F) {a : ℝ}
    (ha : Finsler.SobolevEnergy.energy F (Finsler.SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    ∃ (D : GeodesicPhaseModel F g a)
      (e : OpenPartialHomeomorph (Short D.model) (ℝ × phaseSlice (phaseVector D.vertices g.loop))),
      phasePoint D 0 ∈ e.source ∧ e (phasePoint D 0) = 0 ∧
      (∀ w, (0, w) ∈ e.target →
        Finsler.SobolevEnergy.energy F (Finsler.PolygonModel.broken D.model (e.symm (0, w))) =
          transverseEnergy D w) ∧
      (∀ᶠ t in nhds (0 : ℝ), phasePoint D t ∈ e.source ∧ e (phasePoint D t) = (t, 0)) := by
  obtain ⟨D⟩ := nonempty_geodesicPhaseModel F g ha
  obtain ⟨e, hp, he, hE, hphase⟩ := exists_phaseChart_energy D
  exact ⟨D, e, hp, he, fun w hw => (hE w hw).2, hphase⟩
end ActualPhaseGeometry

section ActualTransverseIteration
open Finsler.SurfaceIteration
set_option backward.isDefEq.respectTransparency true

/- The iteration module uses exactly the transverse energy previously
identified with the actual broken-loop energy, and the same Hessian. -/
example (F : Finsler.Geometry.ReversibleMetric 2)
    (g : Finsler.Geodesics.ClosedGeodesic F) {a : ℝ} (D : GeodesicPhaseModel F g a) :
    (PolygonSlice.ofGeodesic D).energy = transverseEnergy D ∧
      (PolygonSlice.ofGeodesic D).operator = transverseHessian D := ⟨rfl, rfl⟩

/- Every actual S² geodesic supplies the twist hypothesis. No nullity
period or bounded-gap set is postulated in this specialization. -/
example (F : Finsler.Geometry.ReversibleMetric 2)
    (g : Finsler.Geodesics.ClosedGeodesic F) {a : ℝ}
    (ha : Finsler.SobolevEnergy.energy F (Finsler.SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    ∃ D : GeodesicPhaseModel F g a, ∃ L : ℕ, 1 ≤ L ∧
      (∀ j : ℕ, Odd (2 * L * j + 1)) ∧
      (∀ t : ℕ, ∃ j : ℕ, t ≤ 2 * L * j + 1 ∧ 2 * L * j + 1 ≤ t + (2 * L + 1)) ∧
      ∀ (d : ℕ) [NeZero d] (j : ℕ),
        nullity F (((PolygonSlice.ofGeodesic D).iterated d).iterated (2 * L * j + 1)).point =
          nullity F ((PolygonSlice.ofGeodesic D).iterated d).point := by
  obtain ⟨D⟩ := nonempty_geodesicPhaseModel F g ha
  obtain ⟨L, hL, hper⟩ := (PolygonSlice.ofGeodesic D).exists_stable_odd_progression
    (PolygonSlice.ofGeodesic_twist D)
  obtain ⟨hodd, hgap⟩ := PolygonSlice.odd_progression_bounded_gaps L hL
  exact ⟨D, L, hL, hodd, hgap, hper⟩

/- Once the base reduced maximum is supplied, every stable iterate has
an actual maximal disk of index plus transverse nullity. This example
deliberately keeps that geometric maximum as an explicit hypothesis. -/
example (F : Finsler.Geometry.ReversibleMetric 2)
    (g : Finsler.Geodesics.ClosedGeodesic F) {a : ℝ} (D : GeodesicPhaseModel F g a)
    (m : ℕ) [NeZero m]
    (D₀ : ReductionData (PolygonSlice.ofGeodesic D).operator
      (PolygonSlice.ofGeodesic D).operator_symmetric (PolygonSlice.ofGeodesic D).gradient)
    (hnull : nullity F ((PolygonSlice.ofGeodesic D).iterated m).point ≤
      nullity F (PolygonSlice.ofGeodesic D).point)
    (hmax : ∀ᶠ (z : LinearMap.ker (PolygonSlice.ofGeodesic D).operator.toLinearMap) in nhds 0,
      z ≠ 0 → transverseEnergy D (D₀.reduction z) < transverseEnergy D (D₀.reduction 0)) :
    Nonempty (Finsler.SurfaceMorseData.MaximalDiskData
      ((PolygonSlice.ofGeodesic D).iterated m).energy 0
      (index F ((PolygonSlice.ofGeodesic D).iterated m).point
        ((PolygonSlice.ofGeodesic D).iterated m).symmetric +
        Module.finrank ℝ (LinearMap.ker ((PolygonSlice.ofGeodesic D).iterated m).operator.toLinearMap))) :=
  (PolygonSlice.ofGeodesic D).iterated_maximalDisk m D₀ hnull hmax

end ActualTransverseIteration

section ActualIterationHomology
open Finsler.SurfaceIteration Finsler.SurfaceIterationHomology
open Finsler.SurfaceLocalHomology

private noncomputable def quarticAxis : C(ℝ, ℝ × ℝ) :=
  ⟨fun x => (x, 0), continuous_id.prodMk continuous_const⟩

/- A proper open square suffices for the local retraction. This exercises
both excision maps on a degenerate saddle, with mod-two coefficients. -/
example : Function.Injective
    (TopPair.singularHomologyMap
      (criticalMap (fun x : ℝ => -x ^ 4) (fun y : ℝ × ℝ => y.2 ^ 2 - y.1 ^ 4)
        0 (0, 0) quarticAxis rfl (by intro x hx; simpa [quarticAxis] using hx))
      (ModuleCat.of (ZMod 2) (ZMod 2)) 1) := by
  let V : Set (ℝ × ℝ) := {y | |y.1| < 1 ∧ |y.2| < 1}
  apply criticalMap_injective_of_local_retraction (by fun_prop) (by fun_prop)
    quarticAxis rfl _ V
    ((isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const))
    (by norm_num [V, quarticAxis])
    ⟨fun y => y.val.1, continuous_fst.comp continuous_subtype_val⟩
    (by intro x hx; rfl) _ (ZMod 2) 1
  intro y hy
  change y.val.2 ^ 2 - y.val.1 ^ 4 < (0 : ℝ) ^ 2 - 0 ^ 4 at hy
  change -y.val.1 ^ 4 < -(0 : ℝ) ^ 4
  nlinarith [sq_nonneg y.val.2]

/- A given zero-mean S² geodesic supplies the base iterate and the actual
homology injections on a bounded-gap odd progression. There is no separate
index-stability or homology-comparison hypothesis. Existence of such a
geodesic, and nonzero classes in orbit/upper-cut pairs, remain unproved. -/
example (F : Finsler.Geometry.ReversibleMetric 2)
    (g : Finsler.Geodesics.ClosedGeodesic F) (D : Finsler.GeodesicFrames.IterData g)
    (hzero : D.Δ = 0) {a : ℝ}
    (ha : Finsler.SobolevEnergy.energy F (Finsler.SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    ∃ G : GeodesicPhaseModel F g a, ∃ d : ℕ+, ∃ L : ℕ, 1 ≤ L ∧
      (∀ j : ℕ, Odd (2 * L * j + 1)) ∧
      (∀ t : ℕ, ∃ j : ℕ, t ≤ 2 * L * j + 1 ∧ 2 * L * j + 1 ≤ t + (2 * L + 1)) ∧
      ∀ j q : ℕ, Function.Injective (TopPair.singularHomologyMap
        (polygonIterationPair ((PolygonSlice.ofGeodesic G).iterated (d : ℕ)) (2 * L * j + 1))
        (ModuleCat.of (ZMod 2) (ZMod 2)) q) := by
  obtain ⟨G, d, L, hL, hinj⟩ := exists_zero_mean_iteration_injections D (by omega) hzero ha
  obtain ⟨hodd, hgap⟩ := PolygonSlice.odd_progression_bounded_gaps L hL
  exact ⟨G, d, L, hL, hodd, hgap, fun j q => hinj j (ZMod 2) q⟩

end ActualIterationHomology

section ActualIterationEquivalence
open Finsler.SurfaceIteration Finsler.SurfaceIterationHomology Finsler.SurfaceIterationEquivalence
open Finsler.SurfaceLocalHomology Finsler.MorseBott

/- A nonlinear one-dimensional normal chart gives a decreasing deformation
inside a prescribed bounded domain. The energy is (x+x²)²/2, not a quadratic
function in the original coordinate. -/
example : ∃ (V : Set ℝ) (hV0 : (0 : ℝ) ∈ V), IsOpen V ∧ V ⊆ Metric.ball 0 1 ∧
    ∃ H : C(_root_.unitInterval × V, Metric.ball (0 : ℝ) 1),
      (∀ z : V, (H (0,z)).val = z.val) ∧
      (∀ z : V, (H (1,z)).val = 0) ∧
      (∀ t : _root_.unitInterval, (H (t,⟨0,hV0⟩)).val = 0) ∧
      ∀ (t : _root_.unitInterval) (z : V),
        ((H (t,z)).val + (H (t,z)).val ^ 2)^2 / 2 ≤ (z.val + z.val ^ 2)^2 / 2 := by
  let φ : ℝ → ℝ := fun x => x + x ^ 2
  have hc : ContDiff ℝ 1 φ := by dsimp [φ]; fun_prop
  have hd : HasFDerivAt φ (ContinuousLinearEquiv.refl ℝ ℝ : ℝ →L[ℝ] ℝ) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).add ((hasDerivAt_id (0 : ℝ)).pow 2)).hasFDerivAt
    have he : (id + id ^ 2 : ℝ → ℝ) = φ := by funext x; rfl
    rw [he] at h
    norm_num at h
    convert h using 1
    apply ContinuousLinearMap.ext
    intro x
    simp
  let e := hc.contDiffAt.toOpenPartialHomeomorph φ hd (by norm_num)
  have he0 : (0 : ℝ) ∈ e.source := hc.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  have hezero : e 0 = 0 := by change φ 0 = 0; norm_num [φ]
  have hπ : ∀ x : ℝ, tanProj (⊥ : Submodule ℝ ℝ) x = 0 := fun x => by
    change (⊥ : Submodule ℝ ℝ).starProjection x = 0
    simp
  obtain ⟨V, hV0, hV, hVB, H, h₀, h₁, hp, hE⟩ :=
    exists_normal_deformation (fun x : ℝ => (x + x^2)^2 / 2) ⊥
      (ContinuousLinearMap.id ℝ ℝ) e he0 hezero
      (Filter.Eventually.of_forall (fun x => by simp only [hπ]))
      (Filter.Eventually.of_forall (fun x => by
        simp only [hπ, norProj_apply, sub_zero, ContinuousLinearMap.id_apply]
        change (x + x^2)^2 / 2 = (0 + 0^2)^2 / 2 + 1/2 * (φ x * φ x)
        dsimp [φ]
        ring))
      (fun x _ => by simpa using sq_nonneg x) (Metric.ball 0 1) Metric.isOpen_ball
      (Metric.mem_ball_self (by norm_num))
  exact ⟨V,hV0,hV,hVB,H,h₀,fun z => (h₁ z).trans (hπ z.val),hp,hE⟩

/- Every class on a stable actual S² polygon iterate has a preimage, and
rotation by one base period fixes every class, over rational coefficients. -/
example (F : Finsler.Geometry.ReversibleMetric 2) {N m : ℕ} [NeZero N] [NeZero m]
    (P : PolygonSlice F N)
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric)
    (q : ℕ) :
    Function.Bijective (TopPair.singularHomologyMap (polygonIterationPair P m)
      (ModuleCat.of ℚ ℚ) q) ∧
      TopPair.singularHomologyMap (periodRotationPair P m) (ModuleCat.of ℚ ℚ) q = CategoryTheory.CategoryStruct.id _ :=
  ⟨polygonIterationPair_homology_bijective P m (by omega) hnull hidx ℚ q,
    periodRotationPair_homology_eq_id P m (by omega) hnull hidx ℚ q⟩

/- The actual zero-mean endpoint uses rational coefficients and an entire
bounded-gap odd progression. The geodesic and zero mean remain explicit. -/
example (F : Finsler.Geometry.ReversibleMetric 2)
    (g : Finsler.Geodesics.ClosedGeodesic F) (D : Finsler.GeodesicFrames.IterData g)
    (hzero : D.Δ = 0) {a : ℝ}
    (ha : Finsler.SobolevEnergy.energy F (Finsler.SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    ∃ G : GeodesicPhaseModel F g a, ∃ d : ℕ+, ∃ L : ℕ, 1 ≤ L ∧
      (∀ j : ℕ, Odd (2 * L * j + 1)) ∧
      (∀ t : ℕ, ∃ j : ℕ, t ≤ 2 * L * j + 1 ∧ 2 * L * j + 1 ≤ t + (2 * L + 1)) ∧
      ∀ j q : ℕ, Function.Bijective (TopPair.singularHomologyMap
        (polygonIterationPair ((PolygonSlice.ofGeodesic G).iterated (d : ℕ)) (2 * L * j + 1))
        (ModuleCat.of ℚ ℚ) q) := by
  obtain ⟨G, d, L, hL, he⟩ := exists_zero_mean_iteration_equivalences D (by omega) hzero ha
  obtain ⟨hodd, hgap⟩ := PolygonSlice.odd_progression_bounded_gaps L hL
  exact ⟨G,d,L,hL,hodd,hgap,fun j q => he j ℚ q⟩

end ActualIterationEquivalence

section ZeroMeanWithoutBaseChange
open Finsler.ChainForm Finsler.SurfaceChainIndex Finsler.SurfaceZeroMeanIndex
open Finsler.SurfaceIteration Finsler.SurfaceIterationHomology Finsler.SurfaceIterationEquivalence

private noncomputable def cutTestEdge : QuadraticForm ℝ (ℝ × ℝ) :=
  (QuadraticMap.sq (R := ℝ)).comp (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ) -
    (1 / 2 : ℝ) • (QuadraticMap.sq (R := ℝ)).comp (LinearMap.fst ℝ ℝ ℝ)

private theorem cutTestEdge_apply (x y : ℝ) :
    cutTestEdge (x,y) = (x - y)^2 - x^2 / 2 := by
  simp [cutTestEdge, QuadraticMap.sq]
  ring

/- Fixing the marked vertex removes all negative directions of this base
chain, but the third repetition has an explicit negative based variation.
This checks that the proof handles a genuine boundary-cost obstruction. -/
example :
    (∀ w : based (V := ℝ) 2, 0 ≤ form (fun _ : ZMod 2 => cutTestEdge) w.val) ∧
    (∃ z : based (V := ℝ) 6,
      form (iter 3 2 (fun _ : ZMod 2 => cutTestEdge)) z.val = -(1 / 2 : ℝ)) := by
  classical
  constructor
  · intro w
    have hw : w.val 0 = 0 := w.property
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [form_apply, sum_zmod]
    norm_num [Finset.sum_range_succ, cutTestEdge_apply, h2, hw]
    nlinarith [sq_nonneg (w.val 1)]
  · let z : ZMod 6 → ℝ := Function.update (fun _ => 1) 0 0
    have hz : z ∈ based 6 := by simp [z]
    have h1 : (1 : ZMod 6) ≠ 0 := by decide
    have h2 : (2 : ZMod 6) ≠ 0 := by decide
    have h3 : (3 : ZMod 6) ≠ 0 := by decide
    have h4 : (4 : ZMod 6) ≠ 0 := by decide
    have h5 : (5 : ZMod 6) ≠ 0 := by decide
    have h6 : (6 : ZMod 6) = 0 := by decide
    refine ⟨⟨z,hz⟩, ?_⟩
    rw [form_apply, sum_zmod]
    norm_num [Finset.sum_range_succ, iter_natCast, cutTestEdge_apply, z, h1,h2,h3,h4,h5,h6]
    rw [h6]
    norm_num

/- On an actual S² geodesic, a negative direction at the seventh iterate
forces all sufficiently large indices to exceed one hundred. -/
example (F : Finsler.Geometry.ReversibleMetric 2)
    (g : Finsler.Geodesics.ClosedGeodesic F) (D : Finsler.GeodesicFrames.IterData g)
    (h : 0 < D.I 7) :
    0 < D.Δ ∧ ∃ M : ℕ, 1 ≤ M ∧ ∀ k : ℕ, M ≤ k → 100 < D.I k :=
  ⟨mean_pos_of_index_pos D (by omega) h,
    index_eventually_gt_of_index_pos D (by omega) h 100⟩

/- The zero-mean comparison now starts at the original sampled geodesic,
and simultaneously checks the original-period rotation over ℚ. -/
example (F : Finsler.Geometry.ReversibleMetric 2)
    (g : Finsler.Geodesics.ClosedGeodesic F) (D : Finsler.GeodesicFrames.IterData g)
    (hzero : D.Δ = 0) {a : ℝ}
    (ha : Finsler.SobolevEnergy.energy F (Finsler.SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    (∀ m : ℕ, 1 ≤ m → D.I m = 0) ∧
    ∃ G : GeodesicPhaseModel F g a, ∃ L : ℕ, 1 ≤ L ∧
      (∀ j : ℕ, Odd (2 * L * j + 1)) ∧
      (∀ t : ℕ, ∃ j : ℕ, t ≤ 2 * L * j + 1 ∧ 2 * L * j + 1 ≤ t + (2 * L + 1)) ∧
      ∀ j q : ℕ,
        Function.Bijective (TopPair.singularHomologyMap
          (polygonIterationPair (PolygonSlice.ofGeodesic G) (2 * L * j + 1))
          (ModuleCat.of ℚ ℚ) q) ∧
        TopPair.singularHomologyMap
          (periodRotationPair (PolygonSlice.ofGeodesic G) (2 * L * j + 1))
          (ModuleCat.of ℚ ℚ) q = CategoryTheory.CategoryStruct.id _ := by
  obtain ⟨G,L,hL,he⟩ := exists_original_iteration_equivalences D (by omega) hzero ha
  obtain ⟨hodd,hgap⟩ := PolygonSlice.odd_progression_bounded_gaps L hL
  exact ⟨index_eq_zero_of_zero_mean D hzero, G,L,hL,hodd,hgap,fun j q => he j ℚ q⟩

end ZeroMeanWithoutBaseChange


section PeriodRotationMappingTorus
open Finsler.SurfaceOrbitModel Finsler.SurfaceIteration Finsler.SurfaceIterationEquivalence
open Finsler.SurfacePhaseGeometry

-- This is a nonvanishing statement for the actual quotient map, with no
-- assumed homological injection. It still names the polygon mapping torus.
example {N : ℕ} [NeZero N] {F : Finsler.Geometry.ReversibleMetric 2}
    (P : PolygonSlice F N) (m : ℕ) [NeZero m]
    (hnull : Finsler.PolygonHessian.nullity F (P.iterated m).point ≤
      Finsler.PolygonHessian.nullity F P.point)
    (hidx : Finsler.PolygonHessian.index F (P.iterated m).point (P.iterated m).symmetric =
      Finsler.PolygonHessian.index F P.point P.symmetric) :
    ∃ (W : Set (ZMod (m * N) → Finsler.SphereGeometry.Sphere 2)), IsOpen W ∧
      ∃ (hpW : (P.iterated m).point ∈ W)
        (hW : ∀ x, periodRotation (N := N) m x ∈ W ↔ x ∈ W),
      ∀ q : ℕ, ∀ z, z ≠ 0 →
        TopPair.singularHomologyMap (polygonTorusFibrePair P m W hpW hW)
          (ModuleCat.of ℚ ℚ) q z ≠ 0 := by
  obtain ⟨W, hWo, hpW, hW, hi⟩ := exists_polygon_torus_injection P m (by omega) hnull hidx
  refine ⟨W, hWo, hpW, hW, fun q z hz he => hz ?_⟩
  exact hi ℚ q (he.trans (map_zero _).symm)

-- On S² the geometric index/nullity hypotheses are discharged by mean
-- index zero. One fixed sampling works along the entire odd progression.
example {F : Finsler.Geometry.ReversibleMetric 2} {g : Finsler.Geodesics.ClosedGeodesic F}
    (D : Finsler.GeodesicFrames.IterData g) (hzero : D.Δ = 0)
    {a : ℝ} (ha : Finsler.SobolevEnergy.energy F (Finsler.SmoothSobolev.ofSmooth g.loop) < a^2) :
    ∃ G : GeodesicPhaseModel F g a, ∃ L : ℕ, 1 ≤ L ∧
      (∀ j : ℕ, Odd (2 * L * j + 1)) ∧
      ∀ j : ℕ,
        ∃ (W : Set (ZMod ((2 * L * j + 1) * G.vertices) → Finsler.SphereGeometry.Sphere 2)),
          IsOpen W ∧
          ∃ (hpW : ((PolygonSlice.ofGeodesic G).iterated (2 * L * j + 1)).point ∈ W)
            (hW : ∀ x, periodRotation (N := G.vertices) (2 * L * j + 1) x ∈ W ↔ x ∈ W),
            ∀ q : ℕ, Function.Injective (TopPair.singularHomologyMap
              (polygonTorusFibrePair (PolygonSlice.ofGeodesic G) (2 * L * j + 1) W hpW hW)
              (ModuleCat.of ℚ ℚ) q) := by
  obtain ⟨G, L, hL, hi⟩ := exists_original_torus_injections D (by omega) hzero ha
  refine ⟨G, L, hL, (PolygonSlice.odd_progression_bounded_gaps L hL).1, fun j => ?_⟩
  obtain ⟨W, hWo, hpW, hW, hj⟩ := hi j
  exact ⟨W, hWo, hpW, hW, fun q => hj ℚ q⟩

end PeriodRotationMappingTorus

run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets : List Name := [
    ``Finsler.TwoSphere.Arithmetic.forward_dense_of_symmetric_dense,
    ``Finsler.TwoSphere.Arithmetic.finite_spectrum_progression_gap,
    ``Finsler.TwoSphere.Arithmetic.finite_spectrum_not_dense_approximated,
    ``Finsler.TwoSphere.Arithmetic.finite_spectrum_not_odd_approximated,
    ``prime_images_not_countable_of_geodesic_cover,
    ``infinite_prime_images_of_geodesic_cover,
    ``infinite_prime_images_of_dense_length_approximation,
    ``infinite_prime_images_of_odd_length_approximation,
    ``Finsler.SurfaceMinimax.level_deformation_of_no_geodesic,
    ``Finsler.SurfaceMinimax.inclusion_bijective_of_no_geodesic,
    ``Finsler.SurfaceMinimax.exists_geodesic_of_not_injective,
    ``Finsler.SurfaceMinimax.not_injective_of_disk_filling,
    ``Finsler.SurfaceMinimax.exists_geodesic_of_disk_filling,
    ``infinite_prime_images_of_odd_homology_death,
    ``Finsler.HingstonBlocks.basepoint_concat,
    ``Finsler.HingstonBlocks.continuous_concat,
    ``Finsler.HingstonBlocks.energy_concat,
    ``Finsler.HingstonBlocks.energy_concat_le,
    ``Finsler.HingstonBlocks.energy_concat_deficit,
    ``Finsler.HingstonBlocks.energy_concat_lt,
    ``Finsler.HingstonBlocks.concat_injective,
    ``Finsler.HingstonBlocks.concat_diagonal,
    ``Finsler.HingstonBlocks.family_diagonal,
    ``Finsler.HingstonBlocks.energy_family,
    ``Finsler.HingstonBlocks.energy_family_lt,
    ``Finsler.HingstonBlocks.family_injective,
    ``Finsler.HingstonBlocks.family_isClosedEmbedding,
    ``Finsler.HingstonBlocks.exists_boundary_deficit,
    ``Finsler.HingstonBlocks.family_mem_lev,
    ``Finsler.HingstonBlocks.family_boundary_mem,
    ``Finsler.HingstonBlocks.familyPairMap_apply,
    ``Finsler.HingstonConnectors.basepoint_loop,
    ``Finsler.HingstonConnectors.energy_loop,
    ``Finsler.HingstonConnectors.continuous_loop,
    ``Finsler.HingstonConnectors.shortRadius_pos,
    ``Finsler.HingstonConnectors.continuous_shortData,
    ``Finsler.HingstonConnectors.energy_shortLoop,
    ``Finsler.HingstonConnectors.exists_small_connector_radius,
    ``Finsler.HingstonConnectors.energy_loop_le,
    ``Finsler.HingstonConnectors.energy_loop_lt,
    ``Finsler.HingstonConnectors.loop_mem_lev,
    ``Finsler.HingstonConnectors.exists_small_overhead,
    ``Finsler.HingstonConnectors.exists_uniform_budget,
    ``Finsler.HingstonConnectors.energy_blockLoop,
    ``Finsler.HingstonConnectors.blockLoop_boundary_lt,
    ``Finsler.HingstonConnectors.blockLoop_mem_lev,
    ``Finsler.HingstonConnectors.blockLoop_base_boundary_lt,
    ``Finsler.HingstonConnectors.exists_base_boundary_threshold,
    ``Finsler.HingstonBlocks.basepoint_iterate,
    ``Finsler.HingstonBlocks.join_iterates,
    ``Finsler.HingstonConnectors.shortPath_self,
    ``Finsler.HingstonConnectors.shortData_diagonal_path,
    ``Finsler.HingstonConnectors.loop_data,
    ``Finsler.HingstonPause.basepoint_value,
    ``Finsler.HingstonPause.continuous_value,
    ``Finsler.HingstonPause.value_zero,
    ``Finsler.HingstonPause.energy_value,
    ``Finsler.HingstonPause.energy_value_mono,
    ``Finsler.HingstonPause.homotopy_energy_le,
    ``Finsler.HingstonPause.homotopy_mem_lev,
    ``Finsler.HingstonPause.shortLoop_diagonal_eq,
    ``Finsler.HingstonPause.diagonalHomotopy_mem_lev,
    ``Finsler.HingstonPause.diagonalHomotopy_iterates_end,
    ``Finsler.HingstonPause.family_homology_eq,
    ``Finsler.HingstonPause.familyPairMap_zero,
    ``Finsler.HingstonPause.familyPairMap_one,
    ``Finsler.SurfaceMinimax.not_injective_of_homotopic_disk_filling,
    ``Finsler.SurfaceMinimax.exists_geodesic_of_homotopic_disk_filling,
    ``Finsler.HingstonFilling.homologyMap_eq_zero_of_factor,
    ``Finsler.HingstonFilling.slide_zero,
    ``Finsler.HingstonFilling.slide_one,
    ``Finsler.HingstonFilling.slidePairMap_zero,
    ``Finsler.HingstonFilling.slidePairMap_one,
    ``Finsler.HingstonFilling.slide_homology_eq_zero,
    ``Finsler.HingstonFilling.ordinaryPairMap_apply,
    ``Finsler.HingstonFilling.ordinary_homology_eq_zero,
    ``Finsler.HingstonFilling.enlargedFamily_diagonal,
    ``Finsler.HingstonFilling.enlargedFamily_mem_lev,
    ``Finsler.HingstonFilling.enlargedFamily_boundary_mem,
    ``Finsler.HingstonFilling.block_homology_eq_zero,
    ``Finsler.HingstonFilling.blockPairMap_apply,
    ``Finsler.HingstonFilling.blockPairMap_center,
    ``Finsler.HingstonFilling.energy_blockPairMap_le,
    ``Finsler.HingstonFilling.lowerBlockPairMap_comp,
    ``Finsler.SurfaceMinimax.not_injective_of_block_filling,
    ``Finsler.SurfaceMinimax.exists_geodesic_of_block_filling,
    ``Finsler.SurfaceLocalHomology.coordinates_eq_zero_iff,
    ``Finsler.SurfaceLocalHomology.isIso_relative_of_equivalences,
    ``Finsler.SurfaceLocalHomology.isIso_boundaryToPunctured,
    ``Finsler.SurfaceLocalHomology.diskClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.puncturedClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.detectedClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.boundary_ne_center,
    ``Finsler.SurfaceLocalHomology.detector_of_fiber_minimum,
    ``Finsler.SurfaceLocalHomology.familyMap_projectionMap,
    ``Finsler.SurfaceLocalHomology.localClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.familyMap_homology_ne_zero,
    ``Finsler.SurfaceLocalHomology.criticalClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.criticalCarrier_cover,
    ``Finsler.SurfaceLocalHomology.isIso_critical_excision,
    ``Finsler.SurfaceLocalHomology.strictMaximum_class_ne_zero,
    ``Finsler.SurfaceLocalHomology.product_class_ne_zero,
    ``Finsler.SurfaceLocalHomology.chart_class_ne_zero,
    ``Finsler.SurfaceLocalHomology.excisedClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.isIso_criticalInclusion,
    ``Finsler.SurfacePolygonHomology.energy_broken_eq,
    ``Finsler.SurfacePolygonHomology.polygonEnergy_continuous,
    ``Finsler.SurfacePolygonHomology.carrier_energy_lt,
    ``Finsler.SurfacePolygonHomology.brokenPair_samplePair,
    ``Finsler.SurfacePolygonHomology.brokenPair_homology_injective,
    ``Finsler.SurfacePolygonHomology.brokenPair_class_ne_zero,
    ``Finsler.SurfacePolygonHomology.localDiskToLoops_apply,
    ``Finsler.SurfacePolygonHomology.localDiskToLoops_class_ne_zero,
    ``Finsler.SurfacePolygonHomology.nonempty_geodesicModel,
    ``Finsler.SurfaceMorseData.clip_coordinates,
    ``Finsler.SurfaceMorseData.clip_of_mem,
    ``Finsler.SurfaceMorseData.clip_eq_center_iff,
    ``Finsler.SurfaceMorseData.nonempty_maximalDiskData_of_normalForm,
    ``Finsler.SurfaceMorseData.nonempty_regularGeodesicModel,
    ``Finsler.SurfaceMorseData.shortChart_center_mem,
    ``Finsler.SurfaceMorseData.shortChart_center,
    ``Finsler.SurfaceMorseData.shortChart_energy,
    ``Finsler.SurfaceMorseData.centeredChart_center_mem,
    ``Finsler.SurfaceMorseData.centeredChart_center,
    ``Finsler.SurfaceMorseData.centeredChart_energy,
    ``Finsler.SurfaceMorseData.exists_short_splitting,
    ``Finsler.SurfaceMorseData.nonempty_geodesicMorseModel,
    ``Finsler.SurfaceMorseData.diskLoopFamily_center,
    ``Finsler.SurfaceMorseData.diskLoopFamily_isClosedEmbedding,
    ``Finsler.SurfaceMorseData.diskLoopFamily_strict_max,
    ``Finsler.SurfaceMorseData.exists_nonzero_loopClass,
    ``Finsler.SurfaceMorseData.exists_nonzero_loopClass_of_normalForm,
    ``Finsler.SurfaceSpectralDisk.repr_zero_of_not_mem,
    ``Finsler.SurfaceSpectralDisk.inner_eq_sum,
    ``Finsler.SurfaceSpectralDisk.quadratic_eq_sum,
    ``Finsler.SurfaceSpectralDisk.spectral_inner_eq_zero,
    ``Finsler.SurfaceSpectralDisk.nonpositive_eq,
    ``Finsler.SurfaceSpectralDisk.nonpositive_isCompl_positive,
    ``Finsler.SurfaceSpectralDisk.quadratic_nonpos,
    ``Finsler.SurfaceSpectralDisk.quadratic_nonneg,
    ``Finsler.SurfaceSpectralDisk.quadratic_eq_zero_iff,
    ``Finsler.SurfaceSpectralDisk.finrank_nonpositive,
    ``Finsler.SurfaceSpectralDisk.splitEquiv_symm_apply,
    ``Finsler.SurfaceSpectralDisk.nonpositive_inner_positive,
    ``Finsler.SurfaceSpectralDisk.quadratic_add,
    ``Finsler.SurfaceSpectralDisk.kerProj_positive,
    ``Finsler.SurfaceSpectralDisk.reducedPart_zero,
    ``Finsler.SurfaceSpectralDisk.reducedPart_strict_max,
    ``Finsler.SurfaceSpectralDisk.energy_split,
    ``Finsler.SurfaceSpectralDisk.diskCoordinates_symm_apply,
    ``Finsler.SurfaceSpectralDisk.nonempty_maximalDiskData_of_spectralSplitting,
    ``Finsler.SurfaceSpectralDisk.map_mem_phaseSlice,
    ``Finsler.SurfaceSpectralDisk.phaseRestriction_apply,
    ``Finsler.SurfaceSpectralDisk.phaseRestriction_symmetric,
    ``Finsler.SurfaceSpectralDisk.phaseRestriction_nullity,
    ``Finsler.SurfacePhaseGeometry.axisEquiv_apply,
    ``Finsler.SurfacePhaseGeometry.exists_straightening,
    ``Finsler.SurfacePhaseGeometry.phasePolygon_eq_sample,
    ``Finsler.SurfacePhaseGeometry.phasePolygon_continuous,
    ``Finsler.SurfacePhaseGeometry.phaseCoordinates_zero,
    ``Finsler.SurfacePhaseGeometry.phaseCoordinates_smooth,
    ``Finsler.SurfacePhaseGeometry.phaseCoordinates_hasDerivAt,
    ``Finsler.SurfacePhaseGeometry.phaseVector_ne_zero,
    ``Finsler.SurfacePhaseGeometry.phaseCoordinates_eventually_source,
    ``Finsler.SurfacePhaseGeometry.grad_eq_zero_in_chart,
    ``Finsler.SurfacePhaseGeometry.phaseCoordinates_gradient_zero,
    ``Finsler.SurfacePhaseGeometry.phaseVector_mem_ker,
    ``Finsler.SurfacePhaseGeometry.one_le_nullity,
    ``Finsler.SurfacePhaseGeometry.nonempty_geodesicPhaseModel,
    ``Finsler.SurfacePhaseGeometry.phasePoint_continuous,
    ``Finsler.SurfacePhaseGeometry.phasePoint_critical,
    ``Finsler.SurfacePhaseGeometry.phasePoint_nonzero_edges,
    ``Finsler.SurfacePhaseGeometry.phasePoint_broken,
    ``Finsler.SurfacePhaseGeometry.phasePoint_energy,
    ``Finsler.SurfacePhaseGeometry.phasePoint_below,
    ``Finsler.SurfacePhaseGeometry.phase_hessian_symmetric,
    ``Finsler.SurfacePhaseGeometry.actual_phase_nullity,
    ``Finsler.SurfacePhaseGeometry.exists_phaseChart,
    ``Finsler.SurfacePhaseGeometry.exists_phaseChart_energy,
    ``Finsler.SurfacePhaseGeometry.transverseHessian_symmetric,
    ``Finsler.SurfacePhaseGeometry.transverseHessian_nullity,
    ``Finsler.SurfacePhaseGeometry.transverseEnergy_smooth,
    ``Finsler.SurfacePhaseGeometry.transverseGradient_smooth,
    ``Finsler.SurfacePhaseGeometry.transverseGradient_zero,
    ``Finsler.SurfacePhaseGeometry.transverseGradient_hasFDerivAt,
    ``Finsler.SurfacePhaseGeometry.transverseEnergy_eventually_hasFDerivAt,
    ``Finsler.SurfacePhaseGeometry.transverseHessian_eq_operator,
    ``Finsler.SurfacePhaseGeometry.exists_transverse_splitting,
    ``Finsler.SurfaceIteration.phaseRestriction_index,
    ``Finsler.SurfaceIteration.sliceMap_apply,
    ``Finsler.SurfaceIteration.sliceMap_inner,
    ``Finsler.SurfaceIteration.sliceMap_injective,
    ``Finsler.SurfaceIteration.phase_projection_map,
    ``Finsler.SurfaceIteration.phase_image_mem_kernel,
    ``Finsler.SurfaceIteration.slice_hessian_map,
    ``Finsler.SurfaceIteration.slice_nullity_eq,
    ``Finsler.SurfaceIteration.sliceKernelEquiv_apply,
    ``Finsler.SurfaceIteration.sliceGradient_smooth,
    ``Finsler.SurfaceIteration.sliceGradient_zero,
    ``Finsler.SurfaceIteration.sliceGradient_derivative,
    ``Finsler.SurfaceIteration.sliceEnergy_derivative,
    ``Finsler.SurfaceIteration.nonempty_reductionData,
    ``Finsler.SurfaceIteration.ReductionData.exists_splitting,
    ``Finsler.SurfaceIteration.ReductionData.maximalDisk,
    ``Finsler.SurfaceIteration.strict_max_of_equiv,
    ``Finsler.SurfaceIteration.PolygonSlice.ofGeodesic_twist,
    ``Finsler.SurfaceIteration.PolygonSlice.symmetric,
    ``Finsler.SurfaceIteration.PolygonSlice.operator_symmetric,
    ``Finsler.SurfaceIteration.PolygonSlice.operator_index,
    ``Finsler.SurfaceIteration.PolygonSlice.operator_nullity,
    ``Finsler.SurfaceIteration.PolygonSlice.gradient_smooth,
    ``Finsler.SurfaceIteration.PolygonSlice.gradient_zero,
    ``Finsler.SurfaceIteration.PolygonSlice.gradient_derivative,
    ``Finsler.SurfaceIteration.PolygonSlice.energy_derivative,
    ``Finsler.SurfaceIteration.PolygonSlice.nonempty_reduction,
    ``Finsler.SurfaceIteration.PolygonSlice.iterationMap_injective,
    ``Finsler.SurfaceIteration.PolygonSlice.iterationMap_inner,
    ``Finsler.SurfaceIteration.PolygonSlice.energy_iteration,
    ``Finsler.SurfaceIteration.PolygonSlice.gradient_iteration,
    ``Finsler.SurfaceIteration.PolygonSlice.operator_iteration,
    ``Finsler.SurfaceIteration.PolygonSlice.kernelEquiv_apply,
    ``Finsler.SurfaceIteration.PolygonSlice.reduced_energy_iteration,
    ``Finsler.SurfaceIteration.PolygonSlice.reduced_max_iteration,
    ``Finsler.SurfaceIteration.PolygonSlice.iterated_maximalDisk,
    ``Finsler.SurfaceIteration.PolygonSlice.exists_stable_odd_progression,
    ``Finsler.SurfaceIteration.PolygonSlice.odd_progression_bounded_gaps,
    ``Finsler.SurfaceIteration.PolygonSlice.exists_stable_odd_maximalDisks,
    ``Finsler.SurfaceIterationHomology.criticalMap_injective_of_local_retraction,
    ``Finsler.SurfaceIterationHomology.normal_nonneg_of_index_eq,
    ``Finsler.SurfaceIterationHomology.eventually_energy_projection_le,
    ``Finsler.SurfaceIterationHomology.polygonIteration_energy,
    ``Finsler.SurfaceIterationHomology.centeredPolygonChart_mem,
    ``Finsler.SurfaceIterationHomology.centeredPolygonChart_zero,
    ``Finsler.SurfaceIterationHomology.centeredPolygonChart_energy,
    ``Finsler.SurfaceIterationHomology.centeredPolygonChart_iterate,
    ``Finsler.SurfaceIterationHomology.mem_centeredPolygonChart_of_iterate,
    ``Finsler.SurfaceIterationHomology.exists_polygon_retraction,
    ``Finsler.SurfaceIterationHomology.polygonIterationPair_homology_injective,
    ``Finsler.SurfaceIterationHomology.polygonIterationPair_class_ne_zero,
    ``Finsler.SurfaceIterationHomology.iteration_index_mul_le,
    ``Finsler.SurfaceIterationHomology.index_le_dimension_of_zero_mean,
    ``Finsler.SurfaceIterationHomology.exists_stable_base_index,
    ``Finsler.SurfaceIterationHomology.exists_stable_base_of_zero_mean,
    ``Finsler.SurfaceIterationHomology.exists_zero_mean_iteration_injections,
    ``Finsler.SurfaceIterationEquivalence.quadratic_segment_le,
    ``Finsler.SurfaceIterationEquivalence.exists_normal_deformation,
    ``Finsler.SurfaceIterationEquivalence.criticalMap_surjective_of_local_deformation,
    ``Finsler.SurfaceIterationEquivalence.mem_centeredPolygonChart_iterate,
    ``Finsler.SurfaceIterationEquivalence.projected_energy,
    ``Finsler.SurfaceIterationEquivalence.exists_polygon_deformation,
    ``Finsler.SurfaceIterationEquivalence.polygonIterationPair_homology_surjective,
    ``Finsler.SurfaceIterationEquivalence.polygonIterationPair_homology_bijective,
    ``Finsler.SurfaceIterationEquivalence.isIso_polygonIterationPair,
    ``Finsler.SurfaceIterationEquivalence.periodRotation_iterate,
    ``Finsler.SurfaceIterationEquivalence.periodRotation_energy,
    ``Finsler.SurfaceIterationEquivalence.polygonIterationPair_periodRotationPair,
    ``Finsler.SurfaceIterationEquivalence.periodRotationPair_homology_eq_id,
    ``Finsler.SurfaceIterationEquivalence.exists_zero_mean_iteration_equivalences,
    ``Finsler.SurfaceChainIndex.mem_based,
    ``Finsler.SurfaceChainIndex.basedIndex_le,
    ``Finsler.SurfaceChainIndex.basedIndex_add,
    ``Finsler.SurfaceChainIndex.mul_basedIndex_le,
    ``Finsler.SurfaceChainIndex.basedIndex_eq_zero_of_bounded,
    ``Finsler.SurfaceChainIndex.form_repeat,
    ``Finsler.SurfaceChainIndex.form_update_zero,
    ``Finsler.SurfaceChainIndex.exists_negative_based_repeat,
    ``Finsler.SurfaceChainIndex.form_nonneg_of_bounded,
    ``Finsler.SurfaceChainIndex.idx_eq_zero_of_bounded,
    ``Finsler.SurfaceZeroMeanIndex.polygon_index_eq_zero_of_bounded,
    ``Finsler.SurfaceZeroMeanIndex.exists_original_nullity_progression,
    ``Finsler.SurfaceZeroMeanIndex.index_eq_zero_of_zero_mean,
    ``Finsler.SurfaceZeroMeanIndex.mean_pos_of_index_pos,
    ``Finsler.SurfaceZeroMeanIndex.index_eventually_gt_of_index_pos,
    ``Finsler.SurfaceZeroMeanIndex.exists_original_iteration_equivalences,
    ``Finsler.SurfaceIterationEquivalence.exists_polygon_deformation_with_projection,
    ``Finsler.SurfaceZeroMeanIndex.exists_original_stable_progression,
    ``Finsler.SurfaceOrbitModel.descendInvariant_mk,
    ``Finsler.SurfaceOrbitModel.fibrePair_comp_descendPair,
    ``Finsler.SurfaceOrbitModel.fibrePair_homology_injective,
    ``Finsler.SurfaceOrbitModel.criticalRetraction_homology_injective,
    ``Finsler.SurfaceOrbitModel.tanProj_shiftL,
    ``Finsler.SurfaceOrbitModel.centeredPolygonChart_periodRotation,
    ``Finsler.SurfaceOrbitModel.invariantNeighborhood_isOpen,
    ``Finsler.SurfaceOrbitModel.invariantNeighborhood_subset,
    ``Finsler.SurfaceOrbitModel.invariantNeighborhood_mem,
    ``Finsler.SurfaceOrbitModel.invariantNeighborhood_rotation_iff,
    ``Finsler.SurfaceOrbitModel.exists_polygon_torus_injection,
    ``Finsler.SurfaceOrbitModel.exists_original_torus_injections]
  for target in targets do
    let axioms ← collectAxioms target
    let bad := axioms.filter fun name => !allowed.contains name
    unless bad.isEmpty do
      throwError "Disallowed axiom in {target}: {bad}"
    logInfo m!"PASS {target}: {axioms}"
  let env ← getEnv
  for target in [``infinite_prime_images_of_dense_length_approximation,
      ``infinite_prime_images_of_odd_length_approximation,
      ``infinite_prime_images_of_odd_homology_death,
      ``Finsler.SurfaceMinimax.exists_geodesic_of_disk_filling,
      ``Finsler.HingstonBlocks.family_isClosedEmbedding,
      ``Finsler.HingstonBlocks.exists_boundary_deficit,
      ``Finsler.HingstonBlocks.familyPairMap_apply,
      ``Finsler.HingstonConnectors.exists_uniform_budget,
      ``Finsler.HingstonConnectors.blockLoop_base_boundary_lt,
      ``Finsler.HingstonPause.shortLoop_diagonal_eq,
      ``Finsler.HingstonPause.family_homology_eq,
      ``Finsler.SurfaceMinimax.exists_geodesic_of_homotopic_disk_filling,
      ``Finsler.HingstonFilling.block_homology_eq_zero,
      ``Finsler.SurfaceMinimax.exists_geodesic_of_block_filling,
    ``Finsler.SurfaceLocalHomology.coordinates_eq_zero_iff,
    ``Finsler.SurfaceLocalHomology.isIso_relative_of_equivalences,
    ``Finsler.SurfaceLocalHomology.isIso_boundaryToPunctured,
    ``Finsler.SurfaceLocalHomology.diskClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.puncturedClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.detectedClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.boundary_ne_center,
    ``Finsler.SurfaceLocalHomology.detector_of_fiber_minimum,
    ``Finsler.SurfaceLocalHomology.familyMap_projectionMap,
    ``Finsler.SurfaceLocalHomology.localClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.familyMap_homology_ne_zero,
    ``Finsler.SurfaceLocalHomology.criticalClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.criticalCarrier_cover,
    ``Finsler.SurfaceLocalHomology.isIso_critical_excision,
    ``Finsler.SurfaceLocalHomology.strictMaximum_class_ne_zero,
    ``Finsler.SurfaceLocalHomology.product_class_ne_zero,
    ``Finsler.SurfaceLocalHomology.chart_class_ne_zero,
    ``Finsler.SurfaceLocalHomology.excisedClass_ne_zero,
    ``Finsler.SurfaceLocalHomology.isIso_criticalInclusion,
    ``Finsler.SurfacePolygonHomology.energy_broken_eq,
    ``Finsler.SurfacePolygonHomology.polygonEnergy_continuous,
    ``Finsler.SurfacePolygonHomology.carrier_energy_lt,
    ``Finsler.SurfacePolygonHomology.brokenPair_samplePair,
    ``Finsler.SurfacePolygonHomology.brokenPair_homology_injective,
    ``Finsler.SurfacePolygonHomology.brokenPair_class_ne_zero,
    ``Finsler.SurfacePolygonHomology.localDiskToLoops_apply,
    ``Finsler.SurfacePolygonHomology.localDiskToLoops_class_ne_zero,
    ``Finsler.SurfacePolygonHomology.nonempty_geodesicModel,
    ``Finsler.SurfaceMorseData.clip_coordinates,
    ``Finsler.SurfaceMorseData.clip_of_mem,
    ``Finsler.SurfaceMorseData.clip_eq_center_iff,
    ``Finsler.SurfaceMorseData.nonempty_maximalDiskData_of_normalForm,
    ``Finsler.SurfaceMorseData.nonempty_regularGeodesicModel,
    ``Finsler.SurfaceMorseData.shortChart_center_mem,
    ``Finsler.SurfaceMorseData.shortChart_center,
    ``Finsler.SurfaceMorseData.shortChart_energy,
    ``Finsler.SurfaceMorseData.centeredChart_center_mem,
    ``Finsler.SurfaceMorseData.centeredChart_center,
    ``Finsler.SurfaceMorseData.centeredChart_energy,
    ``Finsler.SurfaceMorseData.exists_short_splitting,
    ``Finsler.SurfaceMorseData.nonempty_geodesicMorseModel,
    ``Finsler.SurfaceMorseData.diskLoopFamily_center,
    ``Finsler.SurfaceMorseData.diskLoopFamily_isClosedEmbedding,
    ``Finsler.SurfaceMorseData.diskLoopFamily_strict_max,
    ``Finsler.SurfaceMorseData.exists_nonzero_loopClass,
    ``Finsler.SurfaceMorseData.exists_nonzero_loopClass_of_normalForm,
    ``Finsler.SurfaceSpectralDisk.repr_zero_of_not_mem,
    ``Finsler.SurfaceSpectralDisk.inner_eq_sum,
    ``Finsler.SurfaceSpectralDisk.quadratic_eq_sum,
    ``Finsler.SurfaceSpectralDisk.spectral_inner_eq_zero,
    ``Finsler.SurfaceSpectralDisk.nonpositive_eq,
    ``Finsler.SurfaceSpectralDisk.nonpositive_isCompl_positive,
    ``Finsler.SurfaceSpectralDisk.quadratic_nonpos,
    ``Finsler.SurfaceSpectralDisk.quadratic_nonneg,
    ``Finsler.SurfaceSpectralDisk.quadratic_eq_zero_iff,
    ``Finsler.SurfaceSpectralDisk.finrank_nonpositive,
    ``Finsler.SurfaceSpectralDisk.splitEquiv_symm_apply,
    ``Finsler.SurfaceSpectralDisk.nonpositive_inner_positive,
    ``Finsler.SurfaceSpectralDisk.quadratic_add,
    ``Finsler.SurfaceSpectralDisk.kerProj_positive,
    ``Finsler.SurfaceSpectralDisk.reducedPart_zero,
    ``Finsler.SurfaceSpectralDisk.reducedPart_strict_max,
    ``Finsler.SurfaceSpectralDisk.energy_split,
    ``Finsler.SurfaceSpectralDisk.diskCoordinates_symm_apply,
    ``Finsler.SurfaceSpectralDisk.nonempty_maximalDiskData_of_spectralSplitting,
    ``Finsler.SurfaceSpectralDisk.map_mem_phaseSlice,
    ``Finsler.SurfaceSpectralDisk.phaseRestriction_apply,
    ``Finsler.SurfaceSpectralDisk.phaseRestriction_symmetric,
    ``Finsler.SurfaceSpectralDisk.phaseRestriction_nullity,
    ``Finsler.SurfacePhaseGeometry.axisEquiv_apply,
    ``Finsler.SurfacePhaseGeometry.exists_straightening,
    ``Finsler.SurfacePhaseGeometry.phasePolygon_eq_sample,
    ``Finsler.SurfacePhaseGeometry.phasePolygon_continuous,
    ``Finsler.SurfacePhaseGeometry.phaseCoordinates_zero,
    ``Finsler.SurfacePhaseGeometry.phaseCoordinates_smooth,
    ``Finsler.SurfacePhaseGeometry.phaseCoordinates_hasDerivAt,
    ``Finsler.SurfacePhaseGeometry.phaseVector_ne_zero,
    ``Finsler.SurfacePhaseGeometry.phaseCoordinates_eventually_source,
    ``Finsler.SurfacePhaseGeometry.grad_eq_zero_in_chart,
    ``Finsler.SurfacePhaseGeometry.phaseCoordinates_gradient_zero,
    ``Finsler.SurfacePhaseGeometry.phaseVector_mem_ker,
    ``Finsler.SurfacePhaseGeometry.one_le_nullity,
    ``Finsler.SurfacePhaseGeometry.nonempty_geodesicPhaseModel,
    ``Finsler.SurfacePhaseGeometry.phasePoint_continuous,
    ``Finsler.SurfacePhaseGeometry.phasePoint_critical,
    ``Finsler.SurfacePhaseGeometry.phasePoint_nonzero_edges,
    ``Finsler.SurfacePhaseGeometry.phasePoint_broken,
    ``Finsler.SurfacePhaseGeometry.phasePoint_energy,
    ``Finsler.SurfacePhaseGeometry.phasePoint_below,
    ``Finsler.SurfacePhaseGeometry.phase_hessian_symmetric,
    ``Finsler.SurfacePhaseGeometry.actual_phase_nullity,
    ``Finsler.SurfacePhaseGeometry.exists_phaseChart,
    ``Finsler.SurfacePhaseGeometry.exists_phaseChart_energy,
    ``Finsler.SurfacePhaseGeometry.transverseHessian_symmetric,
    ``Finsler.SurfacePhaseGeometry.transverseHessian_nullity,
    ``Finsler.SurfacePhaseGeometry.transverseEnergy_smooth,
    ``Finsler.SurfacePhaseGeometry.transverseGradient_smooth,
    ``Finsler.SurfacePhaseGeometry.transverseGradient_zero,
    ``Finsler.SurfacePhaseGeometry.transverseGradient_hasFDerivAt,
    ``Finsler.SurfacePhaseGeometry.transverseEnergy_eventually_hasFDerivAt,
    ``Finsler.SurfacePhaseGeometry.transverseHessian_eq_operator,
    ``Finsler.SurfacePhaseGeometry.exists_transverse_splitting,
    ``Finsler.SurfaceIteration.phaseRestriction_index,
    ``Finsler.SurfaceIteration.sliceMap_apply,
    ``Finsler.SurfaceIteration.sliceMap_inner,
    ``Finsler.SurfaceIteration.sliceMap_injective,
    ``Finsler.SurfaceIteration.phase_projection_map,
    ``Finsler.SurfaceIteration.phase_image_mem_kernel,
    ``Finsler.SurfaceIteration.slice_hessian_map,
    ``Finsler.SurfaceIteration.slice_nullity_eq,
    ``Finsler.SurfaceIteration.sliceKernelEquiv_apply,
    ``Finsler.SurfaceIteration.sliceGradient_smooth,
    ``Finsler.SurfaceIteration.sliceGradient_zero,
    ``Finsler.SurfaceIteration.sliceGradient_derivative,
    ``Finsler.SurfaceIteration.sliceEnergy_derivative,
    ``Finsler.SurfaceIteration.nonempty_reductionData,
    ``Finsler.SurfaceIteration.ReductionData.exists_splitting,
    ``Finsler.SurfaceIteration.ReductionData.maximalDisk,
    ``Finsler.SurfaceIteration.strict_max_of_equiv,
    ``Finsler.SurfaceIteration.PolygonSlice.ofGeodesic_twist,
    ``Finsler.SurfaceIteration.PolygonSlice.symmetric,
    ``Finsler.SurfaceIteration.PolygonSlice.operator_symmetric,
    ``Finsler.SurfaceIteration.PolygonSlice.operator_index,
    ``Finsler.SurfaceIteration.PolygonSlice.operator_nullity,
    ``Finsler.SurfaceIteration.PolygonSlice.gradient_smooth,
    ``Finsler.SurfaceIteration.PolygonSlice.gradient_zero,
    ``Finsler.SurfaceIteration.PolygonSlice.gradient_derivative,
    ``Finsler.SurfaceIteration.PolygonSlice.energy_derivative,
    ``Finsler.SurfaceIteration.PolygonSlice.nonempty_reduction,
    ``Finsler.SurfaceIteration.PolygonSlice.iterationMap_injective,
    ``Finsler.SurfaceIteration.PolygonSlice.iterationMap_inner,
    ``Finsler.SurfaceIteration.PolygonSlice.energy_iteration,
    ``Finsler.SurfaceIteration.PolygonSlice.gradient_iteration,
    ``Finsler.SurfaceIteration.PolygonSlice.operator_iteration,
    ``Finsler.SurfaceIteration.PolygonSlice.kernelEquiv_apply,
    ``Finsler.SurfaceIteration.PolygonSlice.reduced_energy_iteration,
    ``Finsler.SurfaceIteration.PolygonSlice.reduced_max_iteration,
    ``Finsler.SurfaceIteration.PolygonSlice.iterated_maximalDisk,
    ``Finsler.SurfaceIteration.PolygonSlice.exists_stable_odd_progression,
    ``Finsler.SurfaceIteration.PolygonSlice.odd_progression_bounded_gaps,
    ``Finsler.SurfaceIteration.PolygonSlice.exists_stable_odd_maximalDisks,
    ``Finsler.SurfaceIterationHomology.criticalMap_injective_of_local_retraction,
    ``Finsler.SurfaceIterationHomology.normal_nonneg_of_index_eq,
    ``Finsler.SurfaceIterationHomology.eventually_energy_projection_le,
    ``Finsler.SurfaceIterationHomology.polygonIteration_energy,
    ``Finsler.SurfaceIterationHomology.centeredPolygonChart_mem,
    ``Finsler.SurfaceIterationHomology.centeredPolygonChart_zero,
    ``Finsler.SurfaceIterationHomology.centeredPolygonChart_energy,
    ``Finsler.SurfaceIterationHomology.centeredPolygonChart_iterate,
    ``Finsler.SurfaceIterationHomology.mem_centeredPolygonChart_of_iterate,
    ``Finsler.SurfaceIterationHomology.exists_polygon_retraction,
    ``Finsler.SurfaceIterationHomology.polygonIterationPair_homology_injective,
    ``Finsler.SurfaceIterationHomology.polygonIterationPair_class_ne_zero,
    ``Finsler.SurfaceIterationHomology.iteration_index_mul_le,
    ``Finsler.SurfaceIterationHomology.index_le_dimension_of_zero_mean,
    ``Finsler.SurfaceIterationHomology.exists_stable_base_index,
    ``Finsler.SurfaceIterationHomology.exists_stable_base_of_zero_mean,
    ``Finsler.SurfaceIterationHomology.exists_zero_mean_iteration_injections,
    ``Finsler.SurfaceIterationEquivalence.quadratic_segment_le,
    ``Finsler.SurfaceIterationEquivalence.exists_normal_deformation,
    ``Finsler.SurfaceIterationEquivalence.criticalMap_surjective_of_local_deformation,
    ``Finsler.SurfaceIterationEquivalence.mem_centeredPolygonChart_iterate,
    ``Finsler.SurfaceIterationEquivalence.projected_energy,
    ``Finsler.SurfaceIterationEquivalence.exists_polygon_deformation,
    ``Finsler.SurfaceIterationEquivalence.polygonIterationPair_homology_surjective,
    ``Finsler.SurfaceIterationEquivalence.polygonIterationPair_homology_bijective,
    ``Finsler.SurfaceIterationEquivalence.isIso_polygonIterationPair,
    ``Finsler.SurfaceIterationEquivalence.periodRotation_iterate,
    ``Finsler.SurfaceIterationEquivalence.periodRotation_energy,
    ``Finsler.SurfaceIterationEquivalence.polygonIterationPair_periodRotationPair,
    ``Finsler.SurfaceIterationEquivalence.periodRotationPair_homology_eq_id,
    ``Finsler.SurfaceIterationEquivalence.exists_zero_mean_iteration_equivalences,
    ``Finsler.SurfaceChainIndex.mem_based,
    ``Finsler.SurfaceChainIndex.basedIndex_le,
    ``Finsler.SurfaceChainIndex.basedIndex_add,
    ``Finsler.SurfaceChainIndex.mul_basedIndex_le,
    ``Finsler.SurfaceChainIndex.basedIndex_eq_zero_of_bounded,
    ``Finsler.SurfaceChainIndex.form_repeat,
    ``Finsler.SurfaceChainIndex.form_update_zero,
    ``Finsler.SurfaceChainIndex.exists_negative_based_repeat,
    ``Finsler.SurfaceChainIndex.form_nonneg_of_bounded,
    ``Finsler.SurfaceChainIndex.idx_eq_zero_of_bounded,
    ``Finsler.SurfaceZeroMeanIndex.polygon_index_eq_zero_of_bounded,
    ``Finsler.SurfaceZeroMeanIndex.exists_original_nullity_progression,
    ``Finsler.SurfaceZeroMeanIndex.index_eq_zero_of_zero_mean,
    ``Finsler.SurfaceZeroMeanIndex.mean_pos_of_index_pos,
    ``Finsler.SurfaceZeroMeanIndex.index_eventually_gt_of_index_pos,
    ``Finsler.SurfaceZeroMeanIndex.exists_original_iteration_equivalences,
    ``Finsler.SurfaceIterationEquivalence.exists_polygon_deformation_with_projection,
    ``Finsler.SurfaceZeroMeanIndex.exists_original_stable_progression,
    ``Finsler.SurfaceOrbitModel.descendInvariant_mk,
    ``Finsler.SurfaceOrbitModel.fibrePair_comp_descendPair,
    ``Finsler.SurfaceOrbitModel.fibrePair_homology_injective,
    ``Finsler.SurfaceOrbitModel.criticalRetraction_homology_injective,
    ``Finsler.SurfaceOrbitModel.tanProj_shiftL,
    ``Finsler.SurfaceOrbitModel.centeredPolygonChart_periodRotation,
    ``Finsler.SurfaceOrbitModel.invariantNeighborhood_isOpen,
    ``Finsler.SurfaceOrbitModel.invariantNeighborhood_subset,
    ``Finsler.SurfaceOrbitModel.invariantNeighborhood_mem,
    ``Finsler.SurfaceOrbitModel.invariantNeighborhood_rotation_iff,
    ``Finsler.SurfaceOrbitModel.exists_polygon_torus_injection,
    ``Finsler.SurfaceOrbitModel.exists_original_torus_injections] do
    let some info := env.find? target | throwError "Missing theorem {target}"
    logInfo m!"Checked type of {target}: {info.type}"
