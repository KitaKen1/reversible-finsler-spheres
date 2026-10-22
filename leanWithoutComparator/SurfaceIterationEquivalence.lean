import SurfaceIterationHomology

/-!
# Energy-decreasing local deformation along repeated polygons

The nonnegative normal quadratic form permits a local deformation from the
identity to the actual repetition projection. Together with excision this
upgrades the point-critical iteration injection to an isomorphism. No
critical-orbit or upper-sublevel injection is postulated here.
-/

namespace Finsler.SurfaceIterationEquivalence

open CategoryTheory Set Filter Metric
open Finsler.SurfaceLocalHomology Finsler.SurfaceIterationHomology
open Finsler.MorseBott
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

section NormalDeformation
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A nonnegative quadratic form decreases along a segment ending at a
zero of the form. This also covers a degenerate form. -/
theorem quadratic_segment_le (A : E →L[ℝ] E) (K : Submodule ℝ E)
    (hpos : ∀ v ∈ K, 0 ≤ ⟪A v, v⟫) (x y : E) (hx : x ∈ K) (hy : y ∈ K)
    (hy0 : ⟪A y, y⟫ = 0) (t : _root_.unitInterval) :
    ⟪A ((1 - (t : ℝ)) • x + (t : ℝ) • y),
      (1 - (t : ℝ)) • x + (t : ℝ) • y⟫ ≤ ⟪A x, x⟫ := by
  have hxy := hpos (x - y) (K.sub_mem hx hy)
  have hx0 := hpos x hx
  have he : ⟪A ((1 - (t : ℝ)) • x + (t : ℝ) • y),
      (1 - (t : ℝ)) • x + (t : ℝ) • y⟫ =
      (1 - (t : ℝ)) * ⟪A x, x⟫ + (t : ℝ) * ⟪A y, y⟫ -
      ((t : ℝ) * (1 - (t : ℝ))) * ⟪A (x - y), x - y⟫ := by
    simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [he, hy0, mul_zero, add_zero]
  have ht := t.property
  have hprod := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) hxy
  have htx := mul_nonneg ht.1 hx0
  nlinarith

/-- A local normal-form chart gives a genuine energy-decreasing deformation
onto the projected directions, inside any prescribed open coordinate domain.
The endpoint is the original linear projection, even when the normal form
chart is not explicitly known to fix its image. -/
theorem exists_normal_deformation (f : E → ℝ) (K : Submodule ℝ E)
    (A : E →L[ℝ] E) (e : OpenPartialHomeomorph E E)
    (he0 : (0 : E) ∈ e.source) (hezero : e 0 = 0)
    (hproj : ∀ᶠ z in 𝓝 (0 : E), tanProj K (e z) = tanProj K z)
    (henergy : ∀ᶠ z in 𝓝 (0 : E),
      f z = f (tanProj K z) + 1 / 2 * ⟪A (norProj K (e z)), norProj K (e z)⟫)
    (hpos : ∀ v ∈ Kᗮ, 0 ≤ ⟪A v, v⟫)
    (Ω : Set E) (hΩ : IsOpen Ω) (hΩ0 : (0 : E) ∈ Ω) :
    ∃ (V : Set E) (hV0 : (0 : E) ∈ V), IsOpen V ∧ V ⊆ Ω ∧
      ∃ H : C(_root_.unitInterval × V, Ω),
        (∀ z : V, (H (0, z)).val = z.val) ∧
        (∀ z : V, (H (1, z)).val = tanProj K z.val) ∧
        (∀ t : _root_.unitInterval, (H (t, ⟨0, hV0⟩)).val = 0) ∧
        ∀ (t : _root_.unitInterval) (z : V), f (H (t, z)).val ≤ f z.val := by
  obtain ⟨U, hU, hUo, hU0⟩ := _root_.eventually_nhds_iff.mp
    (hproj.and (henergy.and (hΩ.mem_nhds hΩ0)))
  have htarget0 : (0 : E) ∈ e.target := hezero ▸ e.map_source he0
  have hinv0 : e.symm 0 = 0 := (congrArg e.symm hezero).symm.trans (e.left_inv he0)
  have hgood : (0 : E) ∈ e.target ∩ e.symm ⁻¹' U := ⟨htarget0, by change e.symm 0 ∈ U; rwa [hinv0]⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (e.symm.isOpen_inter_preimage hUo) 0 hgood
  let W := e.source ∩ e ⁻¹' ball (0 : E) r
  have hW : IsOpen W := e.isOpen_inter_preimage isOpen_ball
  have hW0 : (0 : E) ∈ W := ⟨he0, by change e 0 ∈ ball 0 r; rw [hezero]; exact mem_ball_self hr⟩
  let V := W ∩ (tanProj K) ⁻¹' W
  have hV0 : (0 : E) ∈ V := ⟨hW0, by simpa using hW0⟩
  have hVU : V ⊆ U := by
    intro z hz
    have h : e.symm (e z) ∈ U := (hball hz.1.2).2
    rwa [e.left_inv hz.1.1] at h
  let w (p : _root_.unitInterval × V) : E :=
    (1 - (p.1 : ℝ)) • e p.2.val + (p.1 : ℝ) • e (tanProj K p.2.val)
  have hwball : ∀ p, w p ∈ ball (0 : E) r := by
    intro p
    exact (convex_ball (0 : E) r) p.2.property.1.2 p.2.property.2.2
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (by ring)
  have hwc : Continuous w := by
    have hleft : Continuous (fun p : _root_.unitInterval × V => e p.2.val) :=
      e.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_snd)
        (fun p => p.2.property.1.1)
    have hright : Continuous (fun p : _root_.unitInterval × V => e (tanProj K p.2.val)) :=
      e.continuousOn.comp_continuous
        ((tanProj K).continuous.comp (continuous_subtype_val.comp continuous_snd))
        (fun p => p.2.property.2.1)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul hleft).add
      ((continuous_subtype_val.comp continuous_fst).smul hright)
  let H : C(_root_.unitInterval × V, Ω) :=
    ⟨fun p => ⟨e.symm (w p), (hU _ (hball (hwball p)).2).2.2⟩,
      (e.continuousOn_symm.comp_continuous hwc (fun p => (hball (hwball p)).1)).subtype_mk _⟩
  refine ⟨V, hV0, hW.inter (hW.preimage (tanProj K).continuous),
    fun z hz => (hU z (hVU hz)).2.2, H, ?_, ?_, ?_, ?_⟩
  · intro z
    change e.symm ((1 - (0 : ℝ)) • e z.val + (0 : ℝ) • e (tanProj K z.val)) = z.val
    simpa using e.left_inv z.property.1.1
  · intro z
    change e.symm ((1 - (1 : ℝ)) • e z.val + (1 : ℝ) • e (tanProj K z.val)) = tanProj K z.val
    simpa using e.left_inv z.property.2.1
  · intro t
    change e.symm ((1 - (t : ℝ)) • e 0 + (t : ℝ) • e (tanProj K 0)) = 0
    simp only [map_zero, hezero, smul_zero, add_zero, hinv0]
  · intro t z
    have hz := hU z.val (hVU z.property)
    have hpU : tanProj K z.val ∈ U := by
      have h : e.symm (e (tanProj K z.val)) ∈ U := (hball z.property.2.2).2
      rwa [e.left_inv z.property.2.1] at h
    have hp := hU _ hpU
    have hh : tanProj K (e (H (t,z)).val) = tanProj K (H (t,z)).val ∧
        f (H (t,z)).val = f (tanProj K (H (t,z)).val) +
          1 / 2 * ⟪A (norProj K (e (H (t,z)).val)), norProj K (e (H (t,z)).val)⟫ ∧
        (H (t,z)).val ∈ Ω := hU _ (hball (hwball (t,z))).2
    have he : e (H (t,z)).val = w (t,z) := e.right_inv (hball (hwball (t,z))).1
    have hπ : tanProj K (H (t,z)).val = tanProj K z.val := by
      rw [← hh.1, he]
      change tanProj K ((1 - (t : ℝ)) • e z.val + (t : ℝ) • e (tanProj K z.val)) = _
      rw [map_add, map_smul, map_smul, hz.1, hp.1, tanProj_tanProj, ← add_smul]
      simp
    have hnormal : norProj K (e (H (t,z)).val) =
        (1 - (t : ℝ)) • norProj K (e z.val) + (t : ℝ) • norProj K (e (tanProj K z.val)) := by
      rw [he]
      exact (norProj K).map_add _ _ |>.trans (congrArg₂ (· + ·) ((norProj K).map_smul _ _) ((norProj K).map_smul _ _))
    have hpzero : ⟪A (norProj K (e (tanProj K z.val))), norProj K (e (tanProj K z.val))⟫ = 0 := by
      have h := hp.2.1
      rw [tanProj_tanProj] at h
      linarith
    have hquad := quadratic_segment_le A Kᗮ hpos
      (norProj K (e z.val)) (norProj K (e (tanProj K z.val)))
      (Submodule.sub_starProjection_mem_orthogonal _) (Submodule.sub_starProjection_mem_orthogonal _)
      hpzero t
    change f (H (t,z)).val ≤ f z.val
    rw [hh.2.1, hπ, hnormal, hz.2.1]
    linarith

end NormalDeformation

section LocalHomotopy
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

/-- The local deformation restricts to the actual point-critical pairs,
including their strict lower subspaces. -/
def criticalDeformationHomotopy :
    TopPair.Homotopy (criticalInclusion G V ⟨p', hpV⟩)
      (criticalMap (fun y : V => G y.val) E ⟨p', hpV⟩ p r hrp hr ≫
        criticalMap E G p p' f hfp hf) where
  fst := {
    toFun z := ⟨H (z.1, z.2.val), z.2.property.elim
      (fun hz => Or.inl ((hE z.1 z.2.val).trans_lt hz))
      (fun hz => Or.inr ((congrArg (fun y => H (z.1, y)) hz).trans (hp z.1)))⟩
    continuous_toFun := (H.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left z := Subtype.ext (h₀ z.val)
    map_one_left z := Subtype.ext (h₁ z.val) }
  snd := {
    toFun z := ⟨⟨H (z.1, z.2.val.val), Or.inl ((hE z.1 z.2.val.val).trans_lt z.2.property)⟩,
      (hE z.1 z.2.val.val).trans_lt z.2.property⟩
    continuous_toFun := ((H.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd)))).subtype_mk _).subtype_mk _
    map_zero_left z := Subtype.ext (Subtype.ext (h₀ z.val.val))
    map_one_left z := Subtype.ext (Subtype.ext (h₁ z.val.val)) }

include hpV hrp hr h₀ h₁ hp hE in
/-- A local energy-decreasing homotopy to the image proves surjectivity
of the actual critical-pair map. Excision supplies the domain of the inverse
on homology; no surjectivity or inverse on homology is assumed. -/
theorem criticalMap_surjective_of_local_deformation (hGc : Continuous G) (hV : IsOpen V)
    (K : Type) [Field K] (q : ℕ) :
    Function.Surjective (TopPair.singularHomologyMap
      (criticalMap E G p p' f hfp hf) (ModuleCat.of K K) q) := by
  have hi := isIso_criticalInclusion G hGc V hV ⟨p', hpV⟩ K q
  have hsur := (ConcreteCategory.bijective_of_isIso
    (TopPair.singularHomologyMap (criticalInclusion G V ⟨p', hpV⟩) (ModuleCat.of K K) q)).2
  have he := (criticalDeformationHomotopy E G p p' f hfp hf V hpV r hrp hr H h₀ h₁ hp hE).congr_singularHomologyMap (ModuleCat.of K K) q
  rw [TopPair.singularHomologyMap_comp] at he
  intro z
  obtain ⟨y, hy⟩ := hsur z
  exact ⟨TopPair.singularHomologyMap
    (criticalMap (fun y : V => G y.val) E ⟨p', hpV⟩ p r hrp hr) (ModuleCat.of K K) q y,
    (ConcreteCategory.congr_hom he y).symm.trans hy⟩

end LocalHomotopy

section Polygon
open Finsler.Geometry Finsler.SphereGeometry Finsler.PolygonChart
open Finsler.PolygonHessian Finsler.PolygonIterate Finsler.PolygonNormal
open Finsler.SurfaceIteration Finsler.PolygonLoop

variable {n N : ℕ} [NeZero N] {F : ReversibleMetric n}
  (P : PolygonSlice F N) (m : ℕ) [NeZero m]

/-- Repetition takes the base sphere-chart domain into the iterated one. -/
theorem mem_centeredPolygonChart_iterate (x : ZMod N → Sphere n)
    (hx : x ∈ (centeredPolygonChart P.point).source) :
    polygonIteration (n := n) m x ∈ (centeredPolygonChart (P.iterated m).point).source := by
  refine ⟨?_, Set.mem_univ _⟩
  change PolygonIterate.iterate m N x ∈ (PolygonChart.chart (PolygonIterate.iterate m N P.point)).source
  rw [PolygonChart.mem_chart_source]
  intro i
  exact (PolygonChart.mem_chart_source P.point x).mp hx.1 (red m N i)

/-- Energy on the projected repeated directions has the exact squared
scaling of the original polygon energy. -/
theorem projected_energy (z : Model n (m * N)) :
    PolygonChart.energy F (P.iterated m).point
      (base (P.iterated m).point + tanProj (iterSpace m N) z) =
      (m : ℝ) ^ 2 * PolygonChart.energy F P.point
        (base P.point + resL m N (tanProj (iterSpace m N) z)) := by
  have he : base (P.iterated m).point + tanProj (iterSpace m N) z =
      iterL m N (base P.point + resL m N (tanProj (iterSpace m N) z)) := by
    rw [map_add, iterL_resL m N (tanProj_mem _ z)]
    rw [show base (P.iterated m).point = iterL m N (base P.point) from base_iterate m N P.point]
  rw [he]
  exact PolygonIterate.energy_iterate m N F P.point _

/-- A local deformation of actual sphere polygons onto the repeated ones.
It fixes the repeated critical point and never increases energy. Both its
endpoint and the local retraction use the original repeated-vertex map. -/
theorem exists_polygon_deformation_with_projection
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric) :
    ∃ (V : Set (ZMod (m * N) → Sphere n)) (hpV : (P.iterated m).point ∈ V), IsOpen V ∧
      ∃ r : C(V, (ZMod N → Sphere n)), r ⟨(P.iterated m).point, hpV⟩ = P.point ∧
        (∀ y : V, (m : ℝ) ^ 2 * PolygonDescent.energy F N (r y) ≤
          PolygonDescent.energy F (m * N) y.val) ∧
      (∀ y : V, r y = (centeredPolygonChart P.point).symm
        (resL m N (tanProj (iterSpace m N)
          (centeredPolygonChart (P.iterated m).point y.val)))) ∧
      ∃ H : C(_root_.unitInterval × V, (ZMod (m * N) → Sphere n)),
        (∀ y : V, H (0, y) = y.val) ∧
        (∀ y : V, H (1, y) = polygonIteration m (r y)) ∧
        (∀ t : _root_.unitInterval, H (t, ⟨(P.iterated m).point, hpV⟩) = (P.iterated m).point) ∧
        ∀ (t : _root_.unitInterval) (y : V),
          PolygonDescent.energy F (m * N) (H (t,y)) ≤ PolygonDescent.energy F (m * N) y.val := by
  let e₀ := centeredPolygonChart P.point
  let eₘ := centeredPolygonChart (P.iterated m).point
  let π : Model n (m * N) →L[ℝ] Model n N := (resL m N).comp (tanProj (iterSpace m N))
  let Ω := eₘ.target ∩ π ⁻¹' e₀.target
  have hΩ : IsOpen Ω := eₘ.open_target.inter (e₀.open_target.preimage π.continuous)
  have he₀0 : (0 : Model n N) ∈ e₀.target := by
    rw [← centeredPolygonChart_zero P.point]
    exact e₀.map_source (centeredPolygonChart_mem P.point)
  have heₘ0 : (0 : Model n (m * N)) ∈ eₘ.target := by
    rw [← centeredPolygonChart_zero (P.iterated m).point]
    exact eₘ.map_source (centeredPolygonChart_mem (P.iterated m).point)
  have hΩ0 : (0 : Model n (m * N)) ∈ Ω := ⟨heₘ0, by simpa using he₀0⟩
  let f : Model n (m * N) → ℝ := fun z =>
    PolygonChart.energy F (P.iterated m).point (base (P.iterated m).point + z)
  obtain ⟨Ξ, _, hΞ0, hΞd, hΞP, hΞE⟩ := PolygonNormal.hasNormalForm m N F
    P.segments.smooth P.short P.nonzero_edges hnull
  change HasStrictFDerivAt Ξ
    (ContinuousLinearEquiv.refl ℝ (Model n (m * N)) : Model n (m * N) →L[ℝ] Model n (m * N)) 0 at hΞd
  let e := hΞd.toOpenPartialHomeomorph Ξ
  have he0 : (0 : Model n (m * N)) ∈ e.source := hΞd.mem_toOpenPartialHomeomorph_source
  have hnormal : ∀ᶠ z in 𝓝 (0 : Model n (m * N)),
      f z = f (tanProj (iterSpace m N) z) +
        1 / 2 * ⟪hessian F (P.iterated m).point (norProj (iterSpace m N) (e z)),
          norProj (iterSpace m N) (e z)⟫ := by
    filter_upwards [hΞE] with z hz
    change f z = (m : ℝ) ^ 2 * PolygonChart.energy F P.point
      (base P.point + resL m N (tanProj (iterSpace m N) z)) + _ at hz
    change f z = PolygonChart.energy F (P.iterated m).point
      (base (P.iterated m).point + tanProj (iterSpace m N) z) + _
    rw [projected_energy]
    exact hz
  obtain ⟨W, hW0, hWo, hWΩ, Hc, h₀, h₁, hp, henergy⟩ :=
    exists_normal_deformation f (iterSpace m N) (hessian F (P.iterated m).point)
      e he0 hΞ0 hΞP hnormal (normal_nonneg_of_index_eq P m hidx) Ω hΩ hΩ0
  let V := eₘ.source ∩ eₘ ⁻¹' W
  have hpV : (P.iterated m).point ∈ V :=
    ⟨centeredPolygonChart_mem _, by change eₘ (P.iterated m).point ∈ W; rwa [centeredPolygonChart_zero]⟩
  let u : C(V, W) := ⟨fun y => ⟨eₘ y.val, y.property.2⟩,
    (eₘ.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property.1)).subtype_mk _⟩
  have hπmem : ∀ y : V, π (eₘ y.val) ∈ e₀.target := fun y => (hWΩ y.property.2).2
  let r : C(V, (ZMod N → Sphere n)) := ⟨fun y => e₀.symm (π (eₘ y.val)),
    e₀.continuousOn_symm.comp_continuous (π.continuous.comp
      (eₘ.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property.1))) hπmem⟩
  let H : C(_root_.unitInterval × V, (ZMod (m * N) → Sphere n)) :=
    ⟨fun z => eₘ.symm (Hc (z.1, u z.2)).val,
      eₘ.continuousOn_symm.comp_continuous
        (continuous_subtype_val.comp (Hc.continuous.comp
          (continuous_fst.prodMk (u.continuous.comp continuous_snd))))
        (fun z => (Hc (z.1, u z.2)).property.1)⟩
  have hH₀ : ∀ y : V, H (0,y) = y.val := by
    intro y
    change eₘ.symm (Hc (0,u y)).val = y.val
    rw [h₀]
    exact eₘ.left_inv y.property.1
  have hH₁ : ∀ y : V, H (1,y) = polygonIteration m (r y) := by
    intro y
    have hrsource : r y ∈ e₀.source := e₀.map_target (hπmem y)
    have hiter := mem_centeredPolygonChart_iterate P m (r y) hrsource
    have heiter : eₘ (polygonIteration m (r y)) = tanProj (iterSpace m N) (eₘ y.val) := by
      change centeredPolygonChart (P.iterated m).point (polygonIteration m (r y)) = _
      rw [centeredPolygonChart_iterate]
      have hrcoord : e₀ (r y) = π (eₘ y.val) := e₀.right_inv (hπmem y)
      change iterL m N (e₀ (r y)) = _
      rw [hrcoord]
      exact iterL_resL m N (tanProj_mem _ _)
    change eₘ.symm (Hc (1,u y)).val = _
    rw [h₁]
    change eₘ.symm (tanProj (iterSpace m N) (eₘ y.val)) = _
    rw [← heiter]
    exact eₘ.left_inv hiter
  have hHE : ∀ (t : _root_.unitInterval) (y : V),
      PolygonDescent.energy F (m * N) (H (t,y)) ≤ PolygonDescent.energy F (m * N) y.val := by
    intro t y
    have hsrc : H (t,y) ∈ eₘ.source := eₘ.map_target (Hc (t,u y)).property.1
    rw [centeredPolygonChart_energy _ (H (t,y)) hsrc,
      centeredPolygonChart_energy _ y.val y.property.1]
    have heH : eₘ (H (t,y)) = (Hc (t,u y)).val := eₘ.right_inv (Hc (t,u y)).property.1
    change f (eₘ (H (t,y))) ≤ f (eₘ y.val)
    rw [heH]
    exact henergy t (u y)
  refine ⟨V, hpV, eₘ.isOpen_inter_preimage hWo, r, ?_, ?_, (fun _ => rfl), H, hH₀, hH₁, ?_, hHE⟩
  · change e₀.symm (π (eₘ (P.iterated m).point)) = P.point
    rw [centeredPolygonChart_zero, map_zero]
    rw [← centeredPolygonChart_zero P.point]
    exact e₀.left_inv (centeredPolygonChart_mem _)
  · intro y
    have he := hHE 1 y
    rw [hH₁, polygonIteration_energy] at he
    exact he
  · intro t
    have hu : u ⟨(P.iterated m).point, hpV⟩ = ⟨0, hW0⟩ :=
      Subtype.ext (centeredPolygonChart_zero _)
    change eₘ.symm (Hc (t,u ⟨(P.iterated m).point, hpV⟩)).val = _
    rw [hu, hp, ← centeredPolygonChart_zero (P.iterated m).point]
    exact eₘ.left_inv (centeredPolygonChart_mem _)

/-- A local deformation of actual sphere polygons onto the repeated ones.
It fixes the repeated critical point and never increases energy. Both its
endpoint and the local retraction use the original repeated-vertex map. -/
theorem exists_polygon_deformation
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric) :
    ∃ (V : Set (ZMod (m * N) → Sphere n)) (hpV : (P.iterated m).point ∈ V), IsOpen V ∧
      ∃ r : C(V, (ZMod N → Sphere n)), r ⟨(P.iterated m).point, hpV⟩ = P.point ∧
        (∀ y : V, (m : ℝ) ^ 2 * PolygonDescent.energy F N (r y) ≤
          PolygonDescent.energy F (m * N) y.val) ∧
      ∃ H : C(_root_.unitInterval × V, (ZMod (m * N) → Sphere n)),
        (∀ y : V, H (0, y) = y.val) ∧
        (∀ y : V, H (1, y) = polygonIteration m (r y)) ∧
        (∀ t : _root_.unitInterval, H (t, ⟨(P.iterated m).point, hpV⟩) = (P.iterated m).point) ∧
        ∀ (t : _root_.unitInterval) (y : V),
          PolygonDescent.energy F (m * N) (H (t,y)) ≤ PolygonDescent.energy F (m * N) y.val := by
  obtain ⟨V, hpV, hV, r, hrp, hrE, _, H, h₀, h₁, hp, hE⟩ :=
    exists_polygon_deformation_with_projection P m hnull hidx
  exact ⟨V, hpV, hV, r, hrp, hrE, H, h₀, h₁, hp, hE⟩

/-- Index and nullity preserving iteration is surjective on the actual
point-critical homology, by the constructed energy-decreasing deformation. -/
theorem polygonIterationPair_homology_surjective (hn : 1 ≤ n)
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric)
    (K : Type) [Field K] (q : ℕ) :
    Function.Surjective (TopPair.singularHomologyMap (polygonIterationPair P m) (ModuleCat.of K K) q) := by
  obtain ⟨V, hpV, hV, r, hrp, hrE, H, h₀, h₁, hp, hE⟩ := exists_polygon_deformation P m hnull hidx
  have hr : ∀ y : V, PolygonDescent.energy F (m * N) y.val <
      PolygonDescent.energy F (m * N) (P.iterated m).point →
        PolygonDescent.energy F N (r y) < PolygonDescent.energy F N P.point := by
    intro y hy
    have he : PolygonDescent.energy F (m * N) (P.iterated m).point =
        (m : ℝ)^2 * PolygonDescent.energy F N P.point := polygonIteration_energy m P.point
    rw [he] at hy
    have hc : 0 < (m : ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m)))
    nlinarith [hrE y]
  exact criticalMap_surjective_of_local_deformation
    (PolygonDescent.energy F N) (PolygonDescent.energy F (m * N)) P.point (P.iterated m).point
    (polygonIteration m) rfl _ V hpV r hrp hr H h₀ h₁ hp hE
    (PolygonDescent.energy_continuous F hn (m * N)) hV K q

/-- The actual iteration map is an isomorphism on point-critical homology.
Both injectivity and surjectivity are proved from the geometric normal form. -/
theorem polygonIterationPair_homology_bijective (hn : 1 ≤ n)
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric)
    (K : Type) [Field K] (q : ℕ) :
    Function.Bijective (TopPair.singularHomologyMap (polygonIterationPair P m) (ModuleCat.of K K) q) :=
  ⟨polygonIterationPair_homology_injective P m hn hnull hidx K q,
    polygonIterationPair_homology_surjective P m hn hnull hidx K q⟩


/-- Category-theoretic form of the actual homology isomorphism. -/
theorem isIso_polygonIterationPair (hn : 1 ≤ n)
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric)
    (K : Type) [Field K] (q : ℕ) :
    IsIso (TopPair.singularHomologyMap (polygonIterationPair P m) (ModuleCat.of K K) q) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (polygonIterationPair_homology_bijective P m hn hnull hidx K q)

/-- Rotate the repeated polygon by one base period, namely N vertices. -/
def periodRotation : C((ZMod (m * N) → Sphere n), (ZMod (m * N) → Sphere n)) :=
  ⟨fun x i => x (i + (N : ZMod (m * N))),
    continuous_pi fun i => continuous_apply (i + (N : ZMod (m * N)))⟩

omit [NeZero N] [NeZero m] in
theorem periodRotation_iterate (x : ZMod N → Sphere n) :
    periodRotation (n := n) (N := N) m (polygonIteration m x) = polygonIteration m x := by
  funext i
  change x (red m N (i + (N : ZMod (m * N)))) = x (red m N i)
  rw [map_add, red_natCast, ZMod.natCast_self, add_zero]

theorem periodRotation_energy (x : ZMod (m * N) → Sphere n) :
    PolygonDescent.energy F (m * N) (periodRotation (N := N) m x) =
      PolygonDescent.energy F (m * N) x := by
  rw [PolygonDescent.energy_eq, PolygonDescent.energy_eq]
  exact polyEnergyN_add F (PolygonDescent.amb x) (N : ZMod (m * N))

/-- The actual period rotation on the point-critical pair. -/
def periodRotationPair :
    criticalPair (PolygonDescent.energy F (m * N)) (P.iterated m).point ⟶
      criticalPair (PolygonDescent.energy F (m * N)) (P.iterated m).point :=
  criticalMap _ _ _ _ (periodRotation (N := N) m)
    (periodRotation_iterate m P.point) (fun x hx => by
      simpa only [periodRotation_energy] using hx)

/-- The rotation fixes the entire repeated image before taking homology. -/
theorem polygonIterationPair_periodRotationPair :
    polygonIterationPair P m ≫ periodRotationPair P m = polygonIterationPair P m := by
  ext : 1
  · ext x
    apply Subtype.ext
    apply Subtype.ext
    exact periodRotation_iterate m x.val.val
  · ext x
    apply Subtype.ext
    exact periodRotation_iterate m x.val

/-- When index and nullity are preserved, rotation by a base period acts
as the identity on the whole point-critical homology. Surjectivity of the
actual iteration map proves this directly, without an orientation formula. -/
theorem periodRotationPair_homology_eq_id (hn : 1 ≤ n)
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hidx : index F (P.iterated m).point (P.iterated m).symmetric = index F P.point P.symmetric)
    (K : Type) [Field K] (q : ℕ) :
    TopPair.singularHomologyMap (periodRotationPair P m) (ModuleCat.of K K) q = 𝟙 _ := by
  have hs := polygonIterationPair_homology_surjective P m hn hnull hidx K q
  have he := congrArg (fun f => TopPair.singularHomologyMap f (ModuleCat.of K K) q)
    (polygonIterationPair_periodRotationPair P m)
  rw [TopPair.singularHomologyMap_comp] at he
  ext z
  obtain ⟨x, rfl⟩ := hs z
  exact ConcreteCategory.congr_hom he x

end Polygon

section ZeroMean
open Finsler.Geometry Finsler.SphereGeometry Finsler.GeodesicFrames
open Finsler.PolygonHessian Finsler.PolygonIterate Finsler.PolygonSampling
open Finsler.PolygonNormal Finsler.PolygonLoop Finsler.PolygonIterateReduction
open Finsler.SurfacePhaseGeometry Finsler.SurfaceIteration Finsler.PolygonModel
open Finsler.SamplePhase Finsler.PhaseNullity

variable {n : ℕ} {F : ReversibleMetric n} {g : Geodesics.ClosedGeodesic F}
  (D : IterData g)

/-- A given zero-mean geodesic supplies a stable base iterate and actual
point-critical homology isomorphisms along an odd monodromy progression.
The base index stability is constructed, not an additional hypothesis. -/
theorem exists_zero_mean_iteration_equivalences (hn : 1 ≤ n) (hzero : D.Δ = 0)
    {a : ℝ} (ha : SobolevEnergy.energy F (SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    ∃ G : GeodesicPhaseModel F g a, ∃ d : ℕ+, ∃ L : ℕ, 1 ≤ L ∧
      ∀ (j : ℕ) (K : Type) [Field K] (q : ℕ),
        Function.Bijective (TopPair.singularHomologyMap
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
  apply polygonIterationPair_homology_bijective (P.iterated d) (2 * D.L * j + 1) hn
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
end Finsler.SurfaceIterationEquivalence
