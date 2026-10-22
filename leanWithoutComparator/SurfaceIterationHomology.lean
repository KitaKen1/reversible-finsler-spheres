import SurfaceIteration
import Finsler.Geometry.PolygonEnergyGlobal
import Finsler.Geometry.GeodesicFrames

/-!
# Local homology under index-preserving iteration

The normal form along repeated polygons supplies an energy-nonincreasing
local retraction when both index and nullity are preserved. Excision then
proves injectivity for the actual iteration map of critical pairs. This
compares the strict lower sublevel with one critical point adjoined; it
does not assert injection into an entire critical orbit or an upper cut.
-/

namespace Finsler.SurfaceIterationHomology

open CategoryTheory Set Filter
open Finsler.SurfaceLocalHomology
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

section CriticalMaps
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (E : X → ℝ) (H : Y → ℝ) (p : X) (p' : Y)

/-- A map taking the distinguished point to the distinguished point and
preserving strict lower energy induces a map of actual critical pairs. -/
def criticalMap (f : C(X, Y)) (hp : f p = p')
    (hf : ∀ x, E x < E p → H (f x) < H p') :
    criticalPair E p ⟶ criticalPair H p' := by
  let fc : C(criticalCarrier E p, criticalCarrier H p') :=
    ⟨fun x => ⟨f x.val, x.property.elim (fun hx => Or.inl (hf x.val hx))
      (fun hx => Or.inr (by rw [hx, hp]))⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  exact TopPair.ofSubsetMap (TopCat.ofHom fc) (fun x hx => hf x.val hx)

variable {E H p p'}

/-- A local left inverse preserving the lower part suffices for injection
on global point-critical homology. The two localization maps are proved
isomorphisms by excision. No injection on homology is an input. -/
theorem criticalMap_injective_of_local_retraction
    (hE : Continuous E) (hH : Continuous H) (f : C(X, Y)) (hp : f p = p')
    (hf : ∀ x, E x < E p → H (f x) < H p')
    (V : Set Y) (hV : IsOpen V) (hpV : p' ∈ V) (r : C(V, X))
    (hr : ∀ x (hx : f x ∈ V), r ⟨f x, hx⟩ = x)
    (hlo : ∀ y : V, H y.val < H p' → E (r y) < E p)
    (K : Type) [Field K] (j : ℕ) :
    Function.Injective (TopPair.singularHomologyMap
      (criticalMap E H p p' f hp hf) (ModuleCat.of K K) j) := by
  let U := f ⁻¹' V
  have hpU : p ∈ U := by change f p ∈ V; rw [hp]; exact hpV
  let pU : U := ⟨p, hpU⟩
  let pV : V := ⟨p', hpV⟩
  let fU : C(U, V) := ⟨fun x => ⟨f x.val, x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hfp : fU pU = pV := Subtype.ext hp
  have hrp : r pV = p := by
    have h := hr p hpU
    have he : (⟨f p, hpU⟩ : V) = pV := Subtype.ext hp
    rwa [he] at h
  let iU := criticalInclusion E U pU
  let iV := criticalInclusion H V pV
  let u := criticalMap (fun x : U => E x.val) (fun y : V => H y.val) pU pV fU hfp
    (fun x hx => hf x.val hx)
  let v := criticalMap (fun y : V => H y.val) E pV p r hrp hlo
  have hur : u ≫ v = iU := by
    ext : 1
    · ext x
      apply Subtype.ext
      apply Subtype.ext
      exact hr x.val.val.val x.val.val.property
    · ext x
      apply Subtype.ext
      exact hr x.val.val x.val.property
  have hcomm : u ≫ iV = iU ≫ criticalMap E H p p' f hp hf := by
    ext : 1 <;> rfl
  have hUi := isIso_criticalInclusion E hE U (hV.preimage f.continuous) pU K j
  have hVi := isIso_criticalInclusion H hH V hV pV K j
  have hUb := ConcreteCategory.bijective_of_isIso
    (TopPair.singularHomologyMap iU (ModuleCat.of K K) j)
  have hVb := ConcreteCategory.bijective_of_isIso
    (TopPair.singularHomologyMap iV (ModuleCat.of K K) j)
  have h₁ := congrArg (fun g => TopPair.singularHomologyMap g (ModuleCat.of K K) j) hur
  have h₂ := congrArg (fun g => TopPair.singularHomologyMap g (ModuleCat.of K K) j) hcomm
  rw [TopPair.singularHomologyMap_comp] at h₁
  rw [TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp] at h₂
  intro x y hxy
  obtain ⟨a, rfl⟩ := hUb.2 x
  obtain ⟨b, rfl⟩ := hUb.2 y
  have hu : TopPair.singularHomologyMap u (ModuleCat.of K K) j a =
      TopPair.singularHomologyMap u (ModuleCat.of K K) j b := by
    apply hVb.1
    exact (ConcreteCategory.congr_hom h₂ a).trans (hxy.trans
      (ConcreteCategory.congr_hom h₂ b).symm)
  exact (ConcreteCategory.congr_hom h₁ a).symm.trans
    ((congrArg (fun z => TopPair.singularHomologyMap v (ModuleCat.of K K) j z) hu).trans
      (ConcreteCategory.congr_hom h₁ b))

end CriticalMaps

section Polygon
open Finsler.Geometry Finsler.SphereGeometry Finsler.PolygonChart
open Finsler.PolygonHessian Finsler.PolygonIterate Finsler.PolygonNormal
open Finsler.MorseBott Finsler.OperatorIndex Finsler.SurfaceIteration

variable {n N : ℕ} [NeZero N] {F : ReversibleMetric n}
  (P : PolygonSlice F N) (m : ℕ) [NeZero m]

/-- Index preservation makes the additional normal quadratic form
nonnegative. This is the sign needed for the energy retraction. -/
theorem normal_nonneg_of_index_eq
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric)
    (v : Model n (m * N)) (hv : v ∈ (iterSpace m N)ᗮ) :
    0 ≤ ⟪hessian F (P.iterated m).point v, v⟫ := by
  have he := PolygonNormal.index_iterate_eq m N F P.segments.smooth P.short P.nonzero_edges
    P.symmetric (P.iterated m).symmetric
  have hz : sigNeg ((quad (hessian F (P.iterated m).point)).restrict (iterSpace m N)ᗮ) = 0 := by
    change index F (P.iterated m).point (P.iterated m).symmetric =
      index F P.point P.symmetric +
        sigNeg ((quad (hessian F (P.iterated m).point)).restrict (iterSpace m N)ᗮ) at he
    rw [hidx] at he
    omega
  exact (QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero _).mpr hz ⟨v, hv⟩

/-- Near the repeated polygon, projection onto the repeated directions
does not increase energy after the exact squared scaling. -/
theorem eventually_energy_projection_le
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric) :
    ∀ᶠ z in 𝓝 (0 : Model n (m * N)),
      (m : ℝ) ^ 2 * PolygonChart.energy F P.point
        (base P.point + resL m N (tanProj (iterSpace m N) z)) ≤
      PolygonChart.energy F (P.iterated m).point (base (P.iterated m).point + z) := by
  obtain ⟨Ξ, _, _, _, _, hE⟩ := PolygonNormal.hasNormalForm m N F
    P.segments.smooth P.short P.nonzero_edges hnull
  filter_upwards [hE] with z hz
  have hv : norProj (iterSpace (n := n) m N) (Ξ z) ∈ (iterSpace m N)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal _
  have hpos := normal_nonneg_of_index_eq P m hidx _ hv
  change 0 ≤ ⟪hessian F (PolygonIterate.iterate m N P.point)
    (norProj (iterSpace m N) (Ξ z)), norProj (iterSpace m N) (Ξ z)⟫ at hpos
  change PolygonChart.energy F (P.iterated m).point (base (P.iterated m).point + z) = _ at hz
  rw [hz]
  linarith

/-- The actual repeated-vertex map on sphere polygons. -/
def polygonIteration : C((ZMod N → Sphere n), (ZMod (m * N) → Sphere n)) :=
  ⟨PolygonIterate.iterate m N, continuous_pi fun i => continuous_apply (red m N i)⟩

omit [NeZero N] [NeZero m] in
theorem polygonIteration_energy (x : ZMod N → Sphere n) :
    PolygonDescent.energy F (m * N) (polygonIteration (n := n) m x) =
      (m : ℝ) ^ 2 * PolygonDescent.energy F N x := by
  rw [PolygonDescent.energy_eq, PolygonDescent.energy_eq]
  exact polyEnergyN_iterate m N F (PolygonDescent.amb x)

/-- Center the genuine product sphere chart at the zero coordinate. -/
def centeredPolygonChart (q : ZMod N → Sphere n) :
    OpenPartialHomeomorph (ZMod N → Sphere n) (Model n N) :=
  (PolygonChart.chart q).trans (Homeomorph.addRight (-base q)).toOpenPartialHomeomorph

theorem centeredPolygonChart_mem (q : ZMod N → Sphere n) : q ∈ (centeredPolygonChart q).source := by
  refine ⟨?_, Set.mem_univ _⟩
  change q ∈ (PolygonChart.chart q).source
  rw [PolygonChart.mem_chart_source]
  intro i
  exact mem_extChartAt_source (q i)

theorem centeredPolygonChart_zero (q : ZMod N → Sphere n) : centeredPolygonChart q q = 0 := by
  change base q + -base q = 0
  exact add_neg_cancel _

theorem centeredPolygonChart_energy (q x : ZMod N → Sphere n)
    (hx : x ∈ (centeredPolygonChart q).source) :
    PolygonDescent.energy F N x = PolygonChart.energy F q (base q + centeredPolygonChart q x) := by
  have he : base q + centeredPolygonChart q x = PolygonChart.chart q x := by
    change base q + (PolygonChart.chart q x + -base q) = PolygonChart.chart q x
    abel
  rw [he, PolygonChart.energy_eq, decode_chart q x hx.1]
  rfl

theorem centeredPolygonChart_iterate (x : ZMod N → Sphere n) :
    centeredPolygonChart (P.iterated m).point (polygonIteration (n := n) m x) =
      iterL m N (centeredPolygonChart P.point x) := by
  change PolygonChart.chart (PolygonIterate.iterate m N P.point) (PolygonIterate.iterate m N x) +
    -base (PolygonIterate.iterate m N P.point) = iterL m N (PolygonChart.chart P.point x + -base P.point)
  rw [map_add, map_neg, base_iterate]
  rfl

theorem mem_centeredPolygonChart_of_iterate (x : ZMod N → Sphere n)
    (hx : polygonIteration (n := n) m x ∈ (centeredPolygonChart (P.iterated m).point).source) :
    x ∈ (centeredPolygonChart P.point).source := by
  refine ⟨?_, Set.mem_univ _⟩
  change x ∈ (PolygonChart.chart P.point).source
  rw [PolygonChart.mem_chart_source]
  intro i
  have hsrc : PolygonIterate.iterate m N x ∈
      (PolygonChart.chart (PolygonIterate.iterate m N P.point)).source := hx.1
  have h := (PolygonChart.mem_chart_source _ _).mp hsrc (i.val : ZMod (m * N))
  simpa only [PolygonIterate.iterate_natCast, ZMod.natCast_zmod_val] using h

/-- A genuine local retraction of sphere polygons along iteration. The
map is obtained from the product sphere charts and orthogonal projection,
and satisfies the energy inequality on its entire open domain. -/
theorem exists_polygon_retraction
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric) :
    ∃ (V : Set (ZMod (m * N) → Sphere n)), IsOpen V ∧ (P.iterated m).point ∈ V ∧
      ∃ r : C(V, (ZMod N → Sphere n)),
        (∀ x (hx : polygonIteration (n := n) m x ∈ V), r ⟨polygonIteration m x, hx⟩ = x) ∧
        ∀ y : V, (m : ℝ) ^ 2 * PolygonDescent.energy F N (r y) ≤
          PolygonDescent.energy F (m * N) y.val := by
  let e := centeredPolygonChart (P.iterated m).point
  let e₀ := centeredPolygonChart P.point
  let π : Model n (m * N) →L[ℝ] Model n N := (resL m N).comp (tanProj (iterSpace m N))
  have hzero : (0 : Model n N) ∈ e₀.target := by
    rw [← centeredPolygonChart_zero P.point]
    exact e₀.map_source (centeredPolygonChart_mem P.point)
  have ht : Tendsto π (𝓝 0) (𝓝 (0 : Model n N)) := by
    simpa only [map_zero] using π.continuous.continuousAt.tendsto (x := 0)
  have hnear := (eventually_energy_projection_le P m hnull hidx).and
    (ht.eventually (e₀.open_target.mem_nhds hzero))
  obtain ⟨W, hW, hWo, hW0⟩ := eventually_nhds_iff.mp hnear
  let V := e.source ∩ e ⁻¹' W
  have hpV : (P.iterated m).point ∈ V := by
    refine ⟨centeredPolygonChart_mem _, ?_⟩
    change centeredPolygonChart (P.iterated m).point (P.iterated m).point ∈ W
    rwa [centeredPolygonChart_zero]
  have hc : Continuous (fun y : V => π (e y.val)) :=
    π.continuous.comp (e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property.1))
  have hmem : ∀ y : V, π (e y.val) ∈ e₀.target := fun y => (hW _ y.property.2).2
  let r : C(V, (ZMod N → Sphere n)) :=
    ⟨fun y => e₀.symm (π (e y.val)), e₀.continuousOn_symm.comp_continuous hc hmem⟩
  refine ⟨V, e.isOpen_inter_preimage hWo, hpV, r, ?_, ?_⟩
  · intro x hx
    have hπ : π (e (polygonIteration (n := n) m x)) = e₀ x := by
      change resL m N (tanProj (iterSpace m N)
        (centeredPolygonChart (P.iterated m).point (polygonIteration m x))) = _
      rw [centeredPolygonChart_iterate, tanProj_of_mem _ (iterL_mem m N _), resL_iterL]
    change e₀.symm (π (e (polygonIteration m x))) = x
    rw [hπ]
    exact e₀.left_inv (mem_centeredPolygonChart_of_iterate P m x hx.1)
  · intro y
    have hr : r y ∈ e₀.source := e₀.map_target (hmem y)
    rw [centeredPolygonChart_energy P.point (r y) hr,
      centeredPolygonChart_energy (P.iterated m).point y.val y.property.1]
    have he : e₀ (r y) = π (e y.val) := e₀.right_inv (hmem y)
    change (m : ℝ) ^ 2 * PolygonChart.energy F P.point (base P.point + e₀ (r y)) ≤ _
    rw [he]
    exact (hW _ y.property.2).1

/-- Iteration preserves the strict lower part by its exact positive
energy scaling. This is the actual map whose homology is compared below. -/
def polygonIterationPair :
    criticalPair (PolygonDescent.energy F N) P.point ⟶
      criticalPair (PolygonDescent.energy F (m * N)) (P.iterated m).point :=
  criticalMap _ _ _ _ (polygonIteration m) rfl (fun x hx => by
    change PolygonDescent.energy F (m * N) (polygonIteration m x) <
      PolygonDescent.energy F (m * N) (polygonIteration m P.point)
    rw [polygonIteration_energy, polygonIteration_energy]
    exact mul_lt_mul_of_pos_left hx (sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m)))))

/-- Actual polygon iteration is injective on point-critical homology in
every degree whenever index and nullity are preserved. The proof constructs
the local energy retraction and uses excision on both critical pairs. -/
theorem polygonIterationPair_homology_injective (hn : 1 ≤ n)
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric)
    (K : Type) [Field K] (j : ℕ) :
    Function.Injective (TopPair.singularHomologyMap (polygonIterationPair P m) (ModuleCat.of K K) j) := by
  obtain ⟨V, hV, hpV, r, hr, henergy⟩ := exists_polygon_retraction P m hnull hidx
  apply criticalMap_injective_of_local_retraction
    (PolygonDescent.energy_continuous F hn N) (PolygonDescent.energy_continuous F hn (m * N))
    (polygonIteration m) rfl _ V hV hpV r hr _ K j
  intro y hy
  have hp : PolygonDescent.energy F (m * N) (P.iterated m).point =
      (m : ℝ) ^ 2 * PolygonDescent.energy F N P.point := polygonIteration_energy m P.point
  change PolygonDescent.energy F (m * N) y.val < PolygonDescent.energy F (m * N) (P.iterated m).point at hy
  rw [hp] at hy
  have hc : (0 : ℝ) < (m : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m)))
  nlinarith [henergy y]

/-- A nonzero point-critical class survives this actual iteration map. -/
theorem polygonIterationPair_class_ne_zero (hn : 1 ≤ n)
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric)
    (K : Type) [Field K] (j : ℕ)
    (z : ↥((criticalPair (PolygonDescent.energy F N) P.point).singularHomology (ModuleCat.of K K) j))
    (hz : z ≠ 0) :
    TopPair.singularHomologyMap (polygonIterationPair P m) (ModuleCat.of K K) j z ≠ 0 := by
  intro h
  apply hz
  exact polygonIterationPair_homology_injective P m hn hnull hidx K j
    (h.trans (map_zero _).symm)

end Polygon

section ZeroMean
open Finsler.Geometry Finsler.SphereGeometry Finsler.GeodesicFrames
open Finsler.PolygonHessian Finsler.PolygonIterate Finsler.PolygonSampling
open Finsler.PolygonNormal Finsler.PolygonLoop
open Finsler.PolygonIterateReduction

variable {n : ℕ} {F : ReversibleMetric n} {g : Geodesics.ClosedGeodesic F}
  (D : IterData g)

/-- The intrinsic index function of a closed geodesic is monotone under
divisibility. The comparison is proved on a common actual sampled model. -/
theorem iteration_index_mul_le (d m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) : D.I d ≤ D.I (d * m) := by
  let : NeZero d := ⟨by omega⟩
  let : NeZero m := ⟨by omega⟩
  obtain ⟨δ, hδ, hs⟩ := EnergySphereSmooth.exists_ambientMinEnergy_contDiffAt F
  obtain ⟨N₀, hN₀⟩ := D.data δ hδ
  let N := N₀ + 1
  let : NeZero N := ⟨by dsimp [N]; omega⟩
  have hf := hN₀ N (by dsimp [N]; omega) 0
  let q := samplePoly (2 * N) (SmoothSobolev.ofSmooth (Loops.shift g.loop 0))
  have hq : ShortPolygon δ (PolygonIterate.iterate d (2 * N) q) :=
    shortPolygon_iterate d (2 * N) hf.1
  have hn := iterate_ne d (2 * N) hf.2.1
  have hsd := hessian_isSymmetric F hs hq hn
  have hsm := hessian_isSymmetric F hs (shortPolygon_iterate m (d * (2 * N)) hq)
    (iterate_ne m (d * (2 * N)) hn)
  have h := index_le_iterate m (d * (2 * N)) F hs hq hn hsd hsm
  rw [(hf.2.2.2.1 d).2 hsd, (hf.2.2.2.2 d m).2 hsm] at h
  exact h

/-- Zero mean index bounds all positive-iterate indices by the dimension. -/
theorem index_le_dimension_of_zero_mean (hzero : D.Δ = 0) (m : ℕ) (hm : 1 ≤ m) : D.I m ≤ n := by
  have h := D.mean m hm
  rw [hzero, mul_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)] at h
  exact_mod_cast h

/-- A bounded natural-valued index that is monotone under divisibility
attains a value preserved by every further iterate. -/
theorem exists_stable_base_index (I : ℕ → ℕ) (B : ℕ)
    (hbound : ∀ m, 1 ≤ m → I m ≤ B)
    (hmono : ∀ d m, 1 ≤ d → 1 ≤ m → I d ≤ I (d * m)) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ m : ℕ, 1 ≤ m → I (d * m) = I d := by
  let S : Set ℕ := Set.range (fun k : ℕ => I (k + 1))
  have hb : BddAbove S := ⟨B, by rintro _ ⟨k, rfl⟩; exact hbound (k + 1) (by omega)⟩
  have hn : S.Nonempty := ⟨I 1, 0, rfl⟩
  obtain ⟨b, ⟨k, rfl⟩, hmax⟩ := hb.exists_isGreatest_of_nonempty hn
  refine ⟨k + 1, by omega, fun m hm => le_antisymm ?_ (hmono (k + 1) m (by omega) hm)⟩
  apply hmax
  refine ⟨(k + 1) * m - 1, ?_⟩
  change I ((k + 1) * m - 1 + 1) = I ((k + 1) * m)
  congr 1
  have hpos : 1 ≤ (k + 1) * m := Nat.mul_pos (by omega) hm
  omega

/-- For a zero-mean geodesic, a positive base iterate with stable index is
constructed. This does not assume the existence of a zero-mean geodesic. -/
theorem exists_stable_base_of_zero_mean (hzero : D.Δ = 0) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ m : ℕ, 1 ≤ m → D.I (d * m) = D.I d :=
  exists_stable_base_index D.I n (index_le_dimension_of_zero_mean D hzero)
    (iteration_index_mul_le D)

open Finsler.SurfacePhaseGeometry Finsler.SurfaceIteration Finsler.PolygonModel
open Finsler.SamplePhase Finsler.PhaseNullity

/-- A zero-mean geodesic supplies a common actual polygon model and a
positive base iterate for which all odd monodromy iterates induce
injections on point-critical homology. Neither stable indices, stable
nullities nor a homology comparison map are additional inputs. -/
theorem exists_zero_mean_iteration_injections (hn : 1 ≤ n) (hzero : D.Δ = 0)
    {a : ℝ} (ha : SobolevEnergy.energy F (SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    ∃ G : GeodesicPhaseModel F g a, ∃ d : ℕ+, ∃ L : ℕ, 1 ≤ L ∧
      ∀ (j : ℕ) (K : Type) [Field K] (q : ℕ),
        Function.Injective (TopPair.singularHomologyMap
          (polygonIterationPair ((PolygonSlice.ofGeodesic G).iterated (d : ℕ)) (2 * L * j + 1))
          (ModuleCat.of K K) q) := by
  obtain ⟨d, hd, hstable⟩ := exists_stable_base_of_zero_mean D hzero
  let d' : ℕ+ := ⟨d, hd⟩
  let : NeZero d := ⟨by omega⟩
  obtain ⟨S⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S.δ) (a := a) S.pos
  obtain ⟨N₁, hN₁⟩ := exists_sample_facts_all S g
  obtain ⟨N₂, hN₂⟩ := D.data S.δ S.pos
  let N := max (max N₀ N₁) N₂ + 1
  have hN : 0 < N := by dsimp [N]; omega
  let : NeZero N := ⟨by omega⟩
  let M : PolygonModelData F a (2 * N) := PolygonModelData.mk S
    (hN₀ (2 * N) (by dsimp [N]; omega) (by omega))
  let G : GeodesicPhaseModel F g a :=
    ⟨2 * N, M, fun t => hN₁ t (2 * N) (by dsimp [N]; omega), ha⟩
  let P := PolygonSlice.ofGeodesic G
  have hpoint : P.point = samplePoly (2 * N) (SmoothSobolev.ofSmooth (Loops.shift g.loop 0)) :=
    phasePolygon_eq_sample (2 * N) g.loop 0
  have hf := hN₂ N (by dsimp [N]; omega) 0
  have hbase : index F (P.iterated d).point (P.iterated d).symmetric = D.I d := by
    have h := (hf.2.2.2.1 d).2
    change ∀ hs, index F (PolygonIterate.iterate d (2 * N)
      (samplePoly (2 * N) (SmoothSobolev.ofSmooth (Loops.shift g.loop 0)))) hs = D.I d at h
    rw [← hpoint] at h
    exact h (P.iterated d).symmetric
  refine ⟨G, d', D.L, D.one_le, fun j K _ q => ?_⟩
  apply polygonIterationPair_homology_injective (P.iterated d) (2 * D.L * j + 1) hn
  · have h₁ := (hf.2.2.2.2 d (2 * D.L * j + 1)).1
    have h₂ := (hf.2.2.2.1 d).1
    rw [← hpoint] at h₁ h₂
    change nullity F ((P.iterated d).iterated (2 * D.L * j + 1)).point = _ at h₁
    change nullity F (P.iterated d).point = _ at h₂
    rw [h₁, h₂]
    have he : d * (2 * D.L * j + 1) = d + (2 * d * j) * D.L := by ring
    rw [he, Nat.gcd_add_mul_right_left]
  · have h := (hf.2.2.2.2 d (2 * D.L * j + 1)).2
    rw [← hpoint] at h
    rw [hbase]
    exact (h ((P.iterated d).iterated (2 * D.L * j + 1)).symmetric).trans (hstable _ (by omega))

end ZeroMean

end
end Finsler.SurfaceIterationHomology
