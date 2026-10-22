import SurfaceZeroMeanIndex
import TauCeti.Topology.MappingTorus

/-!
# Local critical classes in the period-rotation mapping torus

The repetition projection is invariant under rotation by one base period.
It therefore descends to the actual topological mapping torus, and detects
every point-critical class when index and nullity are preserved. This
bypasses the Wang sequence and any orientation-sign calculation in this
branch. The mapping torus here is an explicit local polygon model; its
comparison with a neighborhood of the critical orbit in the Sobolev loop
space is a separate geometric step.
-/

namespace Finsler.SurfaceOrbitModel

open CategoryTheory Set Filter
open Finsler.SurfaceLocalHomology Finsler.SurfaceIterationHomology
open Finsler.SurfaceIterationEquivalence
open scoped Topology RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

section MappingTorus
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (φ : X ≃ₜ X) (A : Set X)

/-- The lower part is the image of the lower cylinder in the mapping torus. -/
def torusLower : Set (TauCeti.MappingTorus φ) :=
  {z | ∃ x ∈ A, ∃ t : ℝ, TauCeti.MappingTorus.mk φ x t = z}

/-- The actual quotient of the cylinder, relative to its lower part. -/
def torusPair : TopPair :=
  TopPair.ofSubset (X := TopCat.of (TauCeti.MappingTorus φ)) (torusLower φ A)

/-- Include the pair at height zero in its mapping torus. -/
def fibrePair : TopPair.ofSubset (X := TopCat.of X) A ⟶ torusPair φ A :=
  TopPair.ofSubsetMap (TopCat.ofHom (TauCeti.MappingTorus.incl φ))
    (fun x hx => ⟨x, hx, 0, rfl⟩)

/-- A genuinely invariant continuous map descends through the cylinder
quotient. The target is the original space, not its homology. -/
def descendInvariant (r : C(X, Y)) (hr : ∀ x, r (φ x) = r x) :
    C(TauCeti.MappingTorus φ, Y) :=
  letI : AddAction ℤ (X × ℝ) := TauCeti.MappingTorus.action φ
  { toFun := Quotient.lift (fun p : X × ℝ => r p.1) (by
      intro a b hab
      obtain ⟨k, rfl⟩ := AddAction.mem_orbit_iff.mp hab
      change r ((φ ^ k) b.1) = r b.1
      have h : Function.Semiconj r φ (Homeomorph.refl Y) := hr
      have hk := h.homeomorph_zpow_right k b.1
      change r ((φ ^ k) b.1) = ((1 : Y ≃ₜ Y) ^ k) (r b.1) at hk
      simpa using hk)
    continuous_toFun := isQuotientMap_quotient_mk'.continuous_iff.mpr
      (r.continuous.comp continuous_fst) }

theorem descendInvariant_mk (r : C(X, Y)) (hr : ∀ x, r (φ x) = r x)
    (x : X) (t : ℝ) :
    descendInvariant φ r hr (TauCeti.MappingTorus.mk φ x t) = r x := rfl

/-- Descend a map of lower pairs whenever its ambient map is invariant. -/
def descendPair (B : Set Y) (r : C(X, Y)) (hr : ∀ x, r (φ x) = r x)
    (hAB : ∀ x ∈ A, r x ∈ B) :
    torusPair φ A ⟶ TopPair.ofSubset (X := TopCat.of Y) B :=
  TopPair.ofSubsetMap (TopCat.ofHom (descendInvariant φ r hr)) (by
    rintro _ ⟨x, hx, t, rfl⟩
    exact hAB x hx)

theorem fibrePair_comp_descendPair (B : Set Y) (r : C(X, Y))
    (hr : ∀ x, r (φ x) = r x) (hAB : ∀ x ∈ A, r x ∈ B) :
    fibrePair φ A ≫ descendPair φ A B r hr hAB =
      TopPair.ofSubsetMap (TopCat.ofHom r) hAB := by
  ext : 1 <;> rfl

/-- An invariant detector which is injective on homology proves that the
fibre classes survive the mapping-torus gluing. No exact sequence is needed. -/
theorem fibrePair_homology_injective (B : Set Y) (r : C(X, Y))
    (hr : ∀ x, r (φ x) = r x) (hAB : ∀ x ∈ A, r x ∈ B)
    (K : Type) [Field K] (q : ℕ)
    (hinj : Function.Injective (TopPair.singularHomologyMap
      (TopPair.ofSubsetMap (TopCat.ofHom r) hAB) (ModuleCat.of K K) q)) :
    Function.Injective (TopPair.singularHomologyMap (fibrePair φ A) (ModuleCat.of K K) q) := by
  have h := congrArg (fun f => TopPair.singularHomologyMap f (ModuleCat.of K K) q)
    (fibrePair_comp_descendPair φ A B r hr hAB)
  rw [TopPair.singularHomologyMap_comp] at h
  intro x y hxy
  apply hinj
  exact (ConcreteCategory.congr_hom h x).symm.trans
    ((congrArg (fun z => TopPair.singularHomologyMap
      (descendPair φ A B r hr hAB) (ModuleCat.of K K) q z) hxy).trans
        (ConcreteCategory.congr_hom h y))

end MappingTorus

section Critical
variable {X : Type} [TopologicalSpace X]
  (E : X → ℝ) (p : X) (φ : X ≃ₜ X)
  (hE : ∀ x, E (φ x) = E x) (hp : φ p = p)

/-- Restrict a genuine energy symmetry to the point-critical carrier. -/
def criticalHomeomorph : criticalCarrier E p ≃ₜ criticalCarrier E p where
  toFun x := ⟨φ x.val, x.property.elim
    (fun hx => Or.inl (by rw [hE]; exact hx))
    (fun hx => Or.inr (by rw [hx, hp]))⟩
  invFun x := ⟨φ.symm x.val, x.property.elim
    (fun hx => Or.inl (by
      have he := hE (φ.symm x.val)
      rw [φ.apply_symm_apply] at he
      exact he.symm.trans_lt hx))
    (fun hx => Or.inr (by
      rw [hx]
      exact (congrArg φ.symm hp).symm.trans (φ.symm_apply_apply p)))⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x.val)
  right_inv x := Subtype.ext (φ.apply_symm_apply x.val)
  continuous_toFun := (φ.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (φ.symm.continuous.comp continuous_subtype_val).subtype_mk _

end Critical

section LocalDetector
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (E : X → ℝ) (G : Y → ℝ) (p : X) (p' : Y)
  (f : C(X, Y)) (hfp : f p = p')
  (hf : ∀ x, E x < E p → G (f x) < G p')
  (V : Set Y) (hpV : p' ∈ V) (r : C(V, X)) (hrp : r ⟨p', hpV⟩ = p)
  (hr : ∀ y : V, G y.val < G p' → E (r y) < E p)
  (H : C(_root_.unitInterval × V, Y))
  (h₀ : ∀ y : V, H (0, y) = y.val)
  (h₁ : ∀ y : V, H (1, y) = f (r y))
  (hp : ∀ t : _root_.unitInterval, H (t, ⟨p', hpV⟩) = p')
  (hE : ∀ (t : _root_.unitInterval) (y : V), G (H (t, y)) ≤ G y.val)

include hfp hf h₀ h₁ hp hE in
/-- A local energy-decreasing deformation makes its endpoint projection
injective on critical homology. The comparison with the global point pair
is excision, and the factorization is proved by a homotopy of actual pairs. -/
theorem criticalRetraction_homology_injective (hGc : Continuous G) (hV : IsOpen V)
    (K : Type) [Field K] (q : ℕ) :
    Function.Injective (TopPair.singularHomologyMap
      (criticalMap (fun y : V => G y.val) E ⟨p', hpV⟩ p r hrp hr)
      (ModuleCat.of K K) q) := by
  have hi := isIso_criticalInclusion G hGc V hV ⟨p', hpV⟩ K q
  have hinj := (ConcreteCategory.bijective_of_isIso
    (TopPair.singularHomologyMap (criticalInclusion G V ⟨p', hpV⟩)
      (ModuleCat.of K K) q)).1
  have he := (criticalDeformationHomotopy E G p p' f hfp hf V hpV r hrp hr
    H h₀ h₁ hp hE).congr_singularHomologyMap (ModuleCat.of K K) q
  rw [TopPair.singularHomologyMap_comp] at he
  intro x y hxy
  apply hinj
  exact (ConcreteCategory.congr_hom he x).trans
    ((congrArg (fun z => TopPair.singularHomologyMap
      (criticalMap E G p p' f hfp hf) (ModuleCat.of K K) q z) hxy).trans
        (ConcreteCategory.congr_hom he y).symm)

end LocalDetector

section Polygon
open Finsler.Geometry Finsler.SphereGeometry Finsler.PolygonChart
open Finsler.PolygonHessian Finsler.PolygonIterate Finsler.PolygonNormal
open Finsler.MorseBott Finsler.SurfaceIteration
open Finsler.SphereCoordinateEuler
open scoped Manifold

variable {n N : ℕ} [NeZero N] {F : ReversibleMetric n}
  (P : PolygonSlice F N) (m : ℕ) [NeZero m]

/-- Orthogonal projection to repeated vectors forgets the period rotation. -/
theorem tanProj_shiftL (z : Model n (m * N)) :
    tanProj (iterSpace m N) (shiftL m N z) = tanProj (iterSpace m N) z := by
  have hfix : ∀ w ∈ iterSpace (n := n) m N, shiftL m N w = w := by
    rintro w ⟨v, rfl⟩
    exact shiftL_iterL m N v
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (tanProj_mem _ z)
  intro w hw
  have h := Submodule.starProjection_inner_eq_zero (K := iterSpace (n := n) m N) z w hw
  change ⟪shiftL m N z - tanProj (iterSpace m N) z, w⟫ = 0
  rw [← hfix _ (tanProj_mem _ z), ← map_sub, ← hfix w hw, inner_shiftL]
  exact h

/-- The centered product chart intertwines the actual period rotation
with the corresponding linear isometry. -/
theorem centeredPolygonChart_periodRotation (x : ZMod (m * N) → Sphere n) :
    centeredPolygonChart (P.iterated m).point (periodRotation (N := N) m x) =
      shiftL m N (centeredPolygonChart (P.iterated m).point x) := by
  apply PiLp.ext
  intro i
  have hpoint : (P.iterated m).point (i + (N : ZMod (m * N))) = (P.iterated m).point i := by
    exact congrFun (periodRotation_iterate m P.point) i
  change extChartAt (𝓡 n) ((P.iterated m).point i) (x (i + (N : ZMod (m * N)))) +
    -extChartAt (𝓡 n) ((P.iterated m).point i) ((P.iterated m).point i) =
    extChartAt (𝓡 n) ((P.iterated m).point (i + (N : ZMod (m * N))))
      (x (i + (N : ZMod (m * N)))) +
    -extChartAt (𝓡 n) ((P.iterated m).point (i + (N : ZMod (m * N))))
      ((P.iterated m).point (i + (N : ZMod (m * N))))
  rw [hpoint]

/-- Rotation by any number of vertices is a genuine homeomorphism. -/
def rotation (a : ZMod (m * N)) :
    (ZMod (m * N) → Sphere n) ≃ₜ (ZMod (m * N) → Sphere n) where
  toFun x i := x (i + a)
  invFun x i := x (i - a)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  continuous_toFun := continuous_pi fun i => continuous_apply (i + a)
  continuous_invFun := continuous_pi fun i => continuous_apply (i - a)

/-- A finite intersection makes any polygon neighborhood invariant under
the base-period rotation. It is still a neighborhood of the repeated point. -/
def invariantNeighborhood (V : Set (ZMod (m * N) → Sphere n)) :
    Set (ZMod (m * N) → Sphere n) :=
  {x | ∀ a : ZMod (m * N), rotation (n := n) m (a * (N : ZMod (m * N))) x ∈ V}

theorem invariantNeighborhood_isOpen (V : Set (ZMod (m * N) → Sphere n))
    (hV : IsOpen V) : IsOpen (invariantNeighborhood m V) := by
  have he : invariantNeighborhood m V =
      ⋂ a : ZMod (m * N), (rotation (n := n) m (a * (N : ZMod (m * N)))) ⁻¹' V := by
    ext x
    simp [invariantNeighborhood]
  rw [he]
  exact isOpen_iInter_of_finite fun a =>
    hV.preimage (rotation m (a * (N : ZMod (m * N)))).continuous

omit [NeZero N] [NeZero m] in
theorem invariantNeighborhood_subset (V : Set (ZMod (m * N) → Sphere n)) :
    invariantNeighborhood m V ⊆ V := by
  intro x hx
  simpa [rotation] using hx 0

theorem invariantNeighborhood_mem (V : Set (ZMod (m * N) → Sphere n))
    (hp : (P.iterated m).point ∈ V) : (P.iterated m).point ∈ invariantNeighborhood m V := by
  intro a
  have he : rotation m (a * (N : ZMod (m * N))) (P.iterated m).point = (P.iterated m).point := by
    funext i
    change P.point (red m N (i + a * N)) = P.point (red m N i)
    rw [map_add, map_mul, red_natCast, ZMod.natCast_self, mul_zero, add_zero]
  rwa [he]

omit [NeZero N] [NeZero m] in
theorem invariantNeighborhood_rotation_iff (V : Set (ZMod (m * N) → Sphere n))
    (x : ZMod (m * N) → Sphere n) :
    periodRotation (N := N) m x ∈ invariantNeighborhood m V ↔ x ∈ invariantNeighborhood m V := by
  constructor
  · intro hx a
    have h := hx (a - 1)
    have he : rotation m ((a - 1) * (N : ZMod (m * N))) (periodRotation (N := N) m x) =
        rotation m (a * (N : ZMod (m * N))) x := by
      funext i
      change x (i + (a - 1) * N + N) = x (i + a * N)
      congr 1
      ring
    rwa [he] at h
  · intro hx a
    have h := hx (a + 1)
    have he : rotation m (a * (N : ZMod (m * N))) (periodRotation (N := N) m x) =
        rotation m ((a + 1) * (N : ZMod (m * N))) x := by
      funext i
      change x (i + a * N + N) = x (i + (a + 1) * N)
      congr 1
      ring
    rwa [he]

/-- Restrict the actual base-period rotation to an invariant neighborhood. -/
def localPeriodRotation (V : Set (ZMod (m * N) → Sphere n))
    (hV : ∀ x, periodRotation (N := N) m x ∈ V ↔ x ∈ V) : V ≃ₜ V :=
  (rotation (n := n) m (N : ZMod (m * N))).subtype (fun x => (hV x).symm)

/-- The fibre map of the local critical-pair mapping torus. The monodromy
is the actual vertex rotation, not an unspecified action on homology. -/
def polygonTorusFibrePair (V : Set (ZMod (m * N) → Sphere n))
    (hpV : (P.iterated m).point ∈ V)
    (hV : ∀ x, periodRotation (N := N) m x ∈ V ↔ x ∈ V) :=
  fibrePair
    (criticalHomeomorph (fun x : V => PolygonDescent.energy F (m * N) x.val)
      ⟨(P.iterated m).point, hpV⟩ (localPeriodRotation m V hV)
      (fun x => periodRotation_energy m x.val)
      (Subtype.ext (periodRotation_iterate m P.point)))
    {x | PolygonDescent.energy F (m * N) x.val.val <
      PolygonDescent.energy F (m * N) (P.iterated m).point}

/-- Index/nullity preservation supplies a concrete invariant neighborhood
whose entire point-critical homology injects into its period-rotation
mapping torus. The invariant detector and its injectivity are constructed;
no nonzero class, exact sequence, or orbit injection is assumed. -/
theorem exists_polygon_torus_injection (hn : 1 ≤ n)
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric) :
    ∃ (W : Set (ZMod (m * N) → Sphere n)), IsOpen W ∧
      ∃ (hpW : (P.iterated m).point ∈ W)
        (hW : ∀ x, periodRotation (N := N) m x ∈ W ↔ x ∈ W),
      ∀ (K : Type) [Field K] (q : ℕ), Function.Injective
        (TopPair.singularHomologyMap (polygonTorusFibrePair P m W hpW hW) (ModuleCat.of K K) q) := by
  obtain ⟨V, hpV, hV, r, hrp, hrE, hrformula, H, h₀, h₁, hp, hE⟩ :=
    exists_polygon_deformation_with_projection P m hnull hidx
  let W := invariantNeighborhood m V
  have hWV : W ⊆ V := invariantNeighborhood_subset m V
  have hWo : IsOpen W := invariantNeighborhood_isOpen m V hV
  have hpW : (P.iterated m).point ∈ W := invariantNeighborhood_mem P m V hpV
  have hW : ∀ x, periodRotation (N := N) m x ∈ W ↔ x ∈ W :=
    invariantNeighborhood_rotation_iff m V
  let j : C(W, V) := ⟨fun x => ⟨x.val, hWV x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let rW := r.comp j
  let HW : C(_root_.unitInterval × W, (ZMod (m * N) → Sphere n)) :=
    ⟨fun z => H (z.1, j z.2), H.continuous.comp
      (continuous_fst.prodMk (j.continuous.comp continuous_snd))⟩
  have hrWp : rW ⟨(P.iterated m).point, hpW⟩ = P.point := hrp
  have hrotate : ∀ x : W, rW (localPeriodRotation m W hW x) = rW x := by
    intro x
    change r (j (localPeriodRotation m W hW x)) = r (j x)
    rw [hrformula, hrformula]
    change (centeredPolygonChart P.point).symm
      (resL m N (tanProj (iterSpace m N)
        (centeredPolygonChart (P.iterated m).point (periodRotation (N := N) m x.val)))) = _
    rw [centeredPolygonChart_periodRotation, tanProj_shiftL]
    rfl
  have hrlo : ∀ x : W, PolygonDescent.energy F (m * N) x.val <
      PolygonDescent.energy F (m * N) (P.iterated m).point →
        PolygonDescent.energy F N (rW x) < PolygonDescent.energy F N P.point := by
    intro x hx
    have hscale := polygonIteration_energy (F := F) m P.point
    change PolygonDescent.energy F (m * N) (P.iterated m).point = _ at hscale
    rw [hscale] at hx
    have he := hrE (j x)
    have hm : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m)))
    change (m : ℝ) ^ 2 * PolygonDescent.energy F N (rW x) ≤
      PolygonDescent.energy F (m * N) x.val at he
    nlinarith
  let EW : W → ℝ := fun x => PolygonDescent.energy F (m * N) x.val
  let pW : W := ⟨(P.iterated m).point, hpW⟩
  let E₀ := PolygonDescent.energy F N
  let detector : C(criticalCarrier EW pW, criticalCarrier E₀ P.point) :=
    (TopPair.Hom.fst (criticalMap EW E₀ pW P.point rW hrWp hrlo)).hom
  let A : Set (criticalCarrier EW pW) := {x | EW x.val < EW pW}
  let B : Set (criticalCarrier E₀ P.point) := {x | E₀ x.val < E₀ P.point}
  have hAB : ∀ x ∈ A, detector x ∈ B := fun x hx => hrlo x.val hx
  let φ := criticalHomeomorph EW pW (localPeriodRotation m W hW)
    (fun x => periodRotation_energy (F := F) m x.val)
    (Subtype.ext (periodRotation_iterate m P.point))
  have hdet : ∀ x, detector (φ x) = detector x := fun x => Subtype.ext (hrotate x.val)
  refine ⟨W, hWo, hpW, hW, fun K _ q => ?_⟩
  apply fibrePair_homology_injective φ A B detector hdet hAB K q
  change Function.Injective (TopPair.singularHomologyMap
    (criticalMap EW E₀ pW P.point rW hrWp hrlo) (ModuleCat.of K K) q)
  apply criticalRetraction_homology_injective E₀ (PolygonDescent.energy F (m * N))
    P.point (P.iterated m).point (polygonIteration m) rfl
    (fun x hx => by
      change PolygonDescent.energy F (m * N) (polygonIteration m x) <
        PolygonDescent.energy F (m * N) (polygonIteration m P.point)
      rw [polygonIteration_energy, polygonIteration_energy]
      exact mul_lt_mul_of_pos_left hx (sq_pos_of_pos
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m)))))
    W hpW rW hrWp hrlo HW (fun x => h₀ (j x)) (fun x => h₁ (j x))
    (fun t => hp t) (fun t x => hE t (j x))
    (PolygonDescent.energy_continuous F hn (m * N)) hWo K q

end Polygon

section ZeroMean
open Finsler.Geometry Finsler.GeodesicFrames Finsler.SurfacePhaseGeometry
open Finsler.SurfaceIteration Finsler.SurfaceZeroMeanIndex

variable {n : ℕ} {F : ReversibleMetric n} {g : Geodesics.ClosedGeodesic F}
  (D : IterData g)

/-- Every iterate in an odd bounded-gap progression of a given zero-mean
geodesic has the proved mapping-torus injection. The original geodesic is
retained, and there are no additional index, nullity or homology hypotheses.
This still concerns the explicit polygon mapping torus, not an asserted
identification with the Sobolev critical-orbit pair. -/
theorem exists_original_torus_injections (hn : 1 ≤ n) (hzero : D.Δ = 0)
    {a : ℝ} (ha : SobolevEnergy.energy F (SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    ∃ G : GeodesicPhaseModel F g a, ∃ L : ℕ, 1 ≤ L ∧ ∀ j : ℕ,
      ∃ (W : Set (ZMod ((2 * L * j + 1) * G.vertices) → Finsler.SphereGeometry.Sphere n)),
        IsOpen W ∧
        ∃ (hpW : ((PolygonSlice.ofGeodesic G).iterated (2 * L * j + 1)).point ∈ W)
          (hW : ∀ x, periodRotation (N := G.vertices) (2 * L * j + 1) x ∈ W ↔ x ∈ W),
          ∀ (K : Type) [Field K] (q : ℕ), Function.Injective
            (TopPair.singularHomologyMap
              (polygonTorusFibrePair (PolygonSlice.ofGeodesic G) (2 * L * j + 1) W hpW hW)
              (ModuleCat.of K K) q) := by
  obtain ⟨G, L, hL, hstable⟩ := exists_original_stable_progression D hzero ha
  exact ⟨G, L, hL, fun j => exists_polygon_torus_injection (PolygonSlice.ofGeodesic G)
    (2 * L * j + 1) hn (hstable j).1.le (hstable j).2⟩

end ZeroMean

end
end Finsler.SurfaceOrbitModel
