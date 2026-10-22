module

public import Finsler.Geometry.SegmentSmooth
public import Finsler.Geometry.PolygonRefine
public import Finsler.Geometry.PolygonModel
public import Finsler.Geometry.PolygonIndex
public import Finsler.Analysis.IndexComparison
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-! The index of a polygon and of its refinement. For a family of short minimizing segments, the
vertices of the refinement of a short polygon are the points of its edges at the times s/r. In
the Hilbert coordinates centred at a short polygon q without zero edges and at its refinement
q', the refinement is expressed by a map which is differentiable at the centre (segment points
are differentiable in the endpoints) and takes the centre to the centre; forgetting the inserted
vertices is a linear map. Near the centres the coordinate energy of q' at the refinement of x
is the coordinate energy of q at x, and the coordinate energy of q at the coarse part of y is
at most the coordinate energy of q' at y. Hence, if q is a critical point of its coordinate
energy, so is q', and the two Hessians have the same index: the index does not depend on the
number of vertices under refinement. The nullity is not treated. -/

@[expose] public section

namespace Finsler.PolygonRefineIndex

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.SphereCoordinateEuler Finsler.AmbientEnergyRegularity Finsler.AmbientCalibrator
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SobolevEnergy
open Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling Finsler.PiecewiseC1
open Finsler.PolygonRefine Finsler.PolygonChart Finsler.PolygonSmooth Finsler.PolygonModel
open Finsler.SegmentAtlas Finsler.SegmentSmooth Finsler.PolygonTwist
open Finsler.EnergySphereSmooth Finsler.PolygonHessian
open Finsler.SphereDistance (minEnergy)
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ}

/-! ### The vertices of the refinement -/

section Vertices

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F (sc P Q t, sv P Q t) =
      minEnergy F P Q)
  (r N : ℕ) [NeZero r] [NeZero N]

/-- The vertex r j + s of the refinement is the point at the time s/r of the edge j. -/
theorem refine_coe {P : ZMod N → Sphere n} (hP : ShortPolygon δ P) {j s : ℕ} (hj : j < N)
    (hs : s < r) :
    (refine r N F hseg hP ((r * j + s : ℕ) : ZMod (r * N)) : Ambient n) =
      sc (P (j : ZMod N)) (P ((j : ZMod N) + 1)) ((s : ℝ) / r) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hr' : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_neZero r
  have hlt : r * j + s < r * N :=
    calc r * j + s < r * j + r := by omega
      _ = r * (j + 1) := by ring
      _ ≤ r * N := Nat.mul_le_mul_left r hj
  have hsr : (s : ℝ) / r < 1 := (div_lt_one hr').mpr (by exact_mod_cast hs)
  have hsr0 : (0 : ℝ) ≤ (s : ℝ) / r := by positivity
  have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
  change sampleN (r * N) (polySphereLoop F hseg hP) ((r * j + s : ℕ) : ZMod (r * N)) = _
  rw [sampleN_natCast _ hlt]
  change continuousRepresentative (polyLoop F hseg hP)
    (((r * j + s : ℕ) : ℝ) / ((r * N : ℕ) : ℝ)) = _
  have ht : ((r * j + s : ℕ) : ℝ) / ((r * N : ℕ) : ℝ) = ((j : ℝ) + (s : ℝ) / r) / N := by
    push_cast
    field_simp
  rw [ht]
  have hpiece : ((j : ℝ) + (s : ℝ) / r) / N ∈ Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N) :=
    ⟨div_le_div_of_nonneg_right (by linarith) hN'.le,
      div_lt_div_of_pos_right (by linarith) hN'⟩
  have hmem : ((j : ℝ) + (s : ℝ) / r) / N ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hN']
    linarith
  rw [representative_polyLoop F hseg hP hmem]
  unfold polyCurve
  rw [glue_eq_of_mem_Ico hj _ hpiece]
  have h0 : (N : ℝ) * (((j : ℝ) + (s : ℝ) / r) / N) - (j : ℝ) = (s : ℝ) / r := by
    field_simp
    ring
  rw [h0]
  rfl

end Vertices

/-! ### Polygons in the Hilbert coordinates -/

section Coordinates

variable {N : ℕ} [NeZero N]

/-- The polygon with given coordinates in the charts centred at the vertices of q. -/
def poly (q : ZMod N → Sphere n) (x : Model n N) : ZMod N → Sphere n :=
  fun j => inverseSphere (q j) (x j)

omit [NeZero N] in
theorem poly_base (q : ZMod N → Sphere n) : poly q (base q) = q := by
  funext j
  exact (extChartAt (𝓡 n) (q j)).left_inv (mem_extChartAt_source (q j))

omit [NeZero N] in
/-- The vertices of the coordinate polygon depend continuously on the coordinates, at the
centre. -/
theorem poly_continuousAt (q : ZMod N → Sphere n) (j : ZMod N) :
    ContinuousAt (fun x : Model n N => poly q x j) (base q) := by
  have h1 : ContinuousAt (fun x : Model n N => x j) (base q) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ZMod N => Coordinates n) j).continuous.continuousAt
  have h2 : ContinuousAt (inverseSphere (q j)) (base q j) :=
    continuousAt_extChartAt_symm (I := 𝓡 n) (q j)
  exact ContinuousAt.comp (g := inverseSphere (q j)) (f := fun x : Model n N => x j) h2 h1

omit [NeZero N] in
/-- An edge of the polygon with coordinates near the centre is shorter than a bound for the
edge of the central polygon. -/
theorem eventually_edge_lt {δ : ℝ} {q : ZMod N → Sphere n} (i : ZMod N)
    (hi : ‖(q (i + 1) : Ambient n) - q i‖ < δ) :
    ∀ᶠ x in 𝓝 (base q), ‖(poly q x (i + 1) : Ambient n) - poly q x i‖ < δ := by
  have hc : ContinuousAt (fun x : Model n N =>
      ‖(poly q x (i + 1) : Ambient n) - poly q x i‖) (base q) :=
    ((continuous_subtype_val.continuousAt.comp (poly_continuousAt q (i + 1))).sub
      (continuous_subtype_val.continuousAt.comp (poly_continuousAt q i))).norm
  have h0 : ‖(poly q (base q) (i + 1) : Ambient n) - poly q (base q) i‖ < δ := by
    rw [poly_base]
    exact hi
  exact hc.eventually (gt_mem_nhds h0)

/-- Polygons with coordinates near the centre are short. -/
theorem eventually_short {δ : ℝ} {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    ∀ᶠ x in 𝓝 (base q), ShortPolygon δ (poly q x) :=
  (Filter.eventually_all.mpr fun i => eventually_edge_lt i (hq i)).mono fun _ hx i => hx i

end Coordinates

/-! ### The refinement in the Hilbert coordinates -/

section Refinement

variable {F : ReversibleMetric n} (M : SegmentData F) (r N : ℕ) [NeZero r] [NeZero N]

/-- The vertex i of the refinement, as a function of the coordinates of the coarse polygon. -/
def vert (q : ZMod N → Sphere n) (i : ZMod (r * N)) (x : Model n N) : Ambient n :=
  M.sc (poly q x ((i.val / r : ℕ) : ZMod N)) (poly q x (((i.val / r : ℕ) : ZMod N) + 1))
    (((i.val % r : ℕ) : ℝ) / r)

/-- For coordinates of a short polygon, this is the vertex of its refinement. -/
theorem vert_eq_refine {q : ZMod N → Sphere n} {x : Model n N}
    (hP : ShortPolygon M.δ (poly q x)) (i : ZMod (r * N)) :
    vert M r N q i x = (refine r N F M.seg hP i : Ambient n) := by
  have hr := Nat.pos_of_neZero r
  have hj : i.val / r < N := Nat.div_lt_of_lt_mul (ZMod.val_lt i)
  have h := refine_coe F M.seg r N hP hj (Nat.mod_lt i.val hr)
  rw [Nat.div_add_mod, ZMod.natCast_zmod_val] at h
  exact h.symm

/-- At the centre it is the vertex of the refinement of the central polygon. -/
theorem vert_base {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q) (i : ZMod (r * N)) :
    vert M r N q i (base q) = (refine r N F M.seg hq i : Ambient n) := by
  have hr := Nat.pos_of_neZero r
  have hj : i.val / r < N := Nat.div_lt_of_lt_mul (ZMod.val_lt i)
  have h := refine_coe F M.seg r N hq hj (Nat.mod_lt i.val hr)
  rw [Nat.div_add_mod, ZMod.natCast_zmod_val] at h
  unfold vert
  rw [poly_base]
  exact h.symm

/-- **The vertices of the refinement are differentiable in the coordinates of the polygon**, at
the centre. -/
theorem vert_differentiableAt {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q)
    (hne : ∀ j, q (j + 1) ≠ q j)
    (hpk : ∀ j : ZMod N, ∃ T : SegChart F, q j ∈ segDom T ∧
      ‖(q (j + 1) : Ambient n) - q j‖ < T.δ) (i : ZMod (r * N)) :
    DifferentiableAt ℝ (vert M r N q i) (base q) := by
  have hr := Nat.pos_of_neZero r
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set j : ZMod N := ((i.val / r : ℕ) : ZMod N) with hjdef
  set τ : ℝ := ((i.val % r : ℕ) : ℝ) / r with hτdef
  have hτ : τ ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [hτdef, div_le_one hr']
    exact_mod_cast (Nat.mod_lt i.val hr).le
  obtain ⟨T, hT, hTδ⟩ := hpk j
  -- near the centre the edge is a segment of the package
  have hdom : ∀ᶠ x in 𝓝 (base q), poly q x j ∈ segDom T := by
    have h0 : poly q (base q) j ∈ segDom T := by rw [poly_base]; exact hT
    exact (poly_continuousAt q j).eventually ((segDom_isOpen F T).mem_nhds h0)
  have hev : vert M r N q i =ᶠ[𝓝 (base q)]
      fun x => segCurve T (poly q x j) (poly q x (j + 1)) τ := by
    filter_upwards [hdom, eventually_edge_lt j (hq j), eventually_edge_lt j hTδ]
      with x h1 h2 h3
    exact M.pkg T _ _ h1 h2 h3 τ hτ
  have hB := segCurve_differentiableAt T hT hTδ (hne j) hτ
  have hcomp : DifferentiableAt ℝ (fun x : Model n N =>
      segCurve T (poly q x j) (poly q x (j + 1)) τ) (base q) :=
    DifferentiableAt.comp (g := fun w : Coordinates n × Coordinates n =>
        segCurve T (inverseSphere (q j) w.1) (inverseSphere (q (j + 1)) w.2) τ)
      (f := fun x : Model n N => PolygonNullity.edgeL j x) (base q) hB
      (PolygonNullity.edgeL j).differentiableAt
  exact hcomp.congr_of_eventuallyEq hev

/-- The coordinate expression of the refinement, in the charts centred at the vertices of q'. -/
def refineCoord (q : ZMod N → Sphere n) (q' : ZMod (r * N) → Sphere n) (x : Model n N) :
    Model n (r * N) :=
  WithLp.toLp 2 (fun i => chartNormalize (q' i) (vert M r N q i x))

/-- The refinement map takes the centre to the centre. -/
theorem refineCoord_base {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q) :
    refineCoord M r N q (refine r N F M.seg hq) (base q) = base (refine r N F M.seg hq) := by
  refine PiLp.ext fun i => ?_
  change chartNormalize (refine r N F M.seg hq i) (vert M r N q i (base q)) =
    extChartAt (𝓡 n) (refine r N F M.seg hq i) (refine r N F M.seg hq i)
  rw [vert_base M r N hq i]
  unfold chartNormalize
  rw [normalize_inclusion]

/-- The refinement map is differentiable at the centre. -/
theorem refineCoord_differentiableAt {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q)
    (hne : ∀ j, q (j + 1) ≠ q j)
    (hpk : ∀ j : ZMod N, ∃ T : SegChart F, q j ∈ segDom T ∧
      ‖(q (j + 1) : Ambient n) - q j‖ < T.δ) :
    DifferentiableAt ℝ (refineCoord M r N q (refine r N F M.seg hq)) (base q) := by
  rw [differentiableAt_piLp]
  intro i
  have h1 := vert_differentiableAt M r N hq hne hpk i
  have h2 : DifferentiableAt ℝ (chartNormalize (refine r N F M.seg hq i))
      (vert M r N q i (base q)) := by
    rw [vert_base M r N hq i]
    exact (chartNormalize_smoothAt (refine r N F M.seg hq i) (sphere_ne_zero _)
      (by rw [normalize_inclusion]; exact mem_extChartAt_source _)).differentiableAt (by simp)
  exact DifferentiableAt.comp (g := chartNormalize (refine r N F M.seg hq i))
    (f := vert M r N q i) (base q) h2 h1

/-- Forgetting the inserted vertices, in the Hilbert coordinates. -/
def coarseL : Model n (r * N) →L[ℝ] Model n N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (coarse r N (fun i => y i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Forgetting vertices takes the centre of a polygon to the centre of its coarse polygon. -/
theorem coarseL_base {q : ZMod N → Sphere n} {q' : ZMod (r * N) → Sphere n}
    (hc : coarse r N q' = q) : coarseL r N (base q') = base q := by
  refine PiLp.ext fun j => ?_
  have hcj : q' ((r * j.val : ℕ) : ZMod (r * N)) = q j := congrFun hc j
  change extChartAt (𝓡 n) (q' ((r * j.val : ℕ) : ZMod (r * N)))
    (q' ((r * j.val : ℕ) : ZMod (r * N))) = extChartAt (𝓡 n) (q j) (q j)
  rw [hcj]

/-- The coordinate energy of the coarse polygon is at most the coordinate energy of a short fine
polygon. -/
theorem energy_coarse_le {q : ZMod N → Sphere n} {q' : ZMod (r * N) → Sphere n}
    (hc : coarse r N q' = q) {y : Model n (r * N)} (hP : ShortPolygon M.δ (poly q' y)) :
    energy F q (coarseL r N y) ≤ energy F q' y := by
  have h := polyEnergy_coarse_le r N F M.seg hP
  have e1 : decode q (coarseL r N y) =
      fun j => ((coarse r N (poly q' y) j : Sphere n) : Ambient n) := by
    funext j
    have hcj : q' ((r * j.val : ℕ) : ZMod (r * N)) = q j := congrFun hc j
    change inverseAmbient (q j) (y ((r * j.val : ℕ) : ZMod (r * N))) = _
    rw [← hcj]
    rfl
  have e2 : decode q' y = fun i => (poly q' y i : Ambient n) := rfl
  change polyEnergyN F N (decode q (coarseL r N y)) ≤ polyEnergyN F (r * N) (decode q' y)
  rw [e1, e2, polyEnergyN_eq F N (fun j => mem_sphere_zero_iff_norm.mp (coarse r N (poly q' y) j).2),
    polyEnergyN_eq F (r * N) (fun i => mem_sphere_zero_iff_norm.mp (poly q' y i).2)]
  exact h

/-- The coordinate energy of the refinement, for coordinates of a short polygon whose
refinement is short and lies in the charts. -/
theorem energy_refine {q : ZMod N → Sphere n} {q' : ZMod (r * N) → Sphere n} {x : Model n N}
    (hP : ShortPolygon M.δ (poly q x)) (hR : ShortPolygon M.δ (refine r N F M.seg hP))
    (hsrc : ∀ i, refine r N F M.seg hP i ∈ (extChartAt (𝓡 n) (q' i)).source) :
    energy F q' (refineCoord M r N q q' x) = energy F q x := by
  have h := polyEnergy_refine r N F M.seg hP hR
  have e1 : decode q' (refineCoord M r N q q' x) =
      fun i => (refine r N F M.seg hP i : Ambient n) := by
    funext i
    change inverseAmbient (q' i) (chartNormalize (q' i) (vert M r N q i x)) = _
    rw [vert_eq_refine M r N hP i]
    exact inverseAmbient_chartNormalize (hsrc i)
  have e2 : decode q x = fun j => (poly q x j : Ambient n) := rfl
  change polyEnergyN F (r * N) (decode q' (refineCoord M r N q q' x)) =
    polyEnergyN F N (decode q x)
  rw [e1, e2,
    polyEnergyN_eq F (r * N) (fun i => mem_sphere_zero_iff_norm.mp (refine r N F M.seg hP i).2),
    polyEnergyN_eq F N (fun j => mem_sphere_zero_iff_norm.mp (poly q x j).2)]
  exact h

/-- Near the centre, the coordinate energy of the refinement at the refined coordinates is the
coordinate energy of the polygon. -/
theorem eventually_energy_refine {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q)
    (hne : ∀ j, q (j + 1) ≠ q j)
    (hpk : ∀ j : ZMod N, ∃ T : SegChart F, q j ∈ segDom T ∧
      ‖(q (j + 1) : Ambient n) - q j‖ < T.δ)
    (hq' : ShortPolygon M.δ (refine r N F M.seg hq)) :
    ∀ᶠ x in 𝓝 (base q), energy F (refine r N F M.seg hq)
      (refineCoord M r N q (refine r N F M.seg hq) x) = energy F q x := by
  have hcont : ∀ i, ContinuousAt (vert M r N q i) (base q) := fun i =>
    (vert_differentiableAt M r N hq hne hpk i).continuousAt
  have he2 : ∀ᶠ x in 𝓝 (base q), ∀ i : ZMod (r * N),
      ‖vert M r N q (i + 1) x - vert M r N q i x‖ < M.δ := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun x => ‖vert M r N q (i + 1) x - vert M r N q i x‖) (base q) :=
      ((hcont (i + 1)).sub (hcont i)).norm
    have h0 : ‖vert M r N q (i + 1) (base q) - vert M r N q i (base q)‖ < M.δ := by
      rw [vert_base M r N hq, vert_base M r N hq]
      exact hq' i
    exact hc.eventually (gt_mem_nhds h0)
  have he3 : ∀ᶠ x in 𝓝 (base q), ∀ i : ZMod (r * N), ∀ Z : Sphere n,
      (Z : Ambient n) = vert M r N q i x →
        Z ∈ (extChartAt (𝓡 n) (refine r N F M.seg hq i)).source := by
    rw [Filter.eventually_all]
    intro i
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
      (isOpen_extChartAt_source (I := 𝓡 n) (refine r N F M.seg hq i))
      (refine r N F M.seg hq i) (mem_extChartAt_source _)
    have hc : ContinuousAt (fun x =>
        ‖vert M r N q i x - (refine r N F M.seg hq i : Ambient n)‖) (base q) :=
      ((hcont i).sub continuousAt_const).norm
    have h0 : ‖vert M r N q i (base q) - (refine r N F M.seg hq i : Ambient n)‖ < ε := by
      rw [vert_base M r N hq i, sub_self, norm_zero]
      exact hε
    filter_upwards [hc.eventually (gt_mem_nhds h0)] with x hx Z hZ
    apply hball
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, hZ]
    exact hx
  filter_upwards [eventually_short hq, he2, he3] with x hP h2 h3
  have hv := fun i => vert_eq_refine M r N hP i
  refine energy_refine M r N hP (fun i => ?_) (fun i => h3 i _ (hv i).symm)
  rw [← hv (i + 1), ← hv i]
  exact h2 i

/-- If a short polygon without zero edges is a critical point of its coordinate energy, so is
its refinement. -/
theorem fderiv_refine_eq_zero {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q)
    (hne : ∀ j, q (j + 1) ≠ q j)
    (hpk : ∀ j : ZMod N, ∃ T : SegChart F, q j ∈ segDom T ∧
      ‖(q (j + 1) : Ambient n) - q j‖ < T.δ)
    (hq' : ShortPolygon M.δ (refine r N F M.seg hq))
    (hne' : ∀ i, refine r N F M.seg hq (i + 1) ≠ refine r N F M.seg hq i)
    (hcrit : fderiv ℝ (energy F q) (base q) = 0) :
    fderiv ℝ (energy F (refine r N F M.seg hq)) (base (refine r N F M.seg hq)) = 0 := by
  have hc := coarse_refine r N F M.seg hq
  have hf₁ : DifferentiableAt ℝ (energy F q) (base q) :=
    (energy_contDiffAt F M.smooth hq hne).differentiableAt (by norm_num)
  have hf₂ : DifferentiableAt ℝ (energy F (refine r N F M.seg hq))
      (base (refine r N F M.seg hq)) :=
    (energy_contDiffAt F M.smooth hq' hne').differentiableAt (by norm_num)
  have heq : energy F q (base q) =
      energy F (refine r N F M.seg hq) (base (refine r N F M.seg hq)) := by
    have h := (eventually_energy_refine M r N hq hne hpk hq').self_of_nhds
    rw [refineCoord_base M r N hq] at h
    exact h.symm
  exact IndexComparison.fderiv_eq_zero_of_le (coarseL_base r N hc) hf₁ hf₂ hcrit
    (coarseL r N).hasFDerivAt
    ((eventually_short hq').mono fun y hy => energy_coarse_le M r N hc hy) heq

/-- **The index is invariant under refinement.** For a short polygon without zero edges which
is a critical point of its coordinate energy, whose refinement is short and has no zero edges,
the index of the refinement is the index of the polygon. -/
theorem index_refine {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q)
    (hne : ∀ j, q (j + 1) ≠ q j)
    (hpk : ∀ j : ZMod N, ∃ T : SegChart F, q j ∈ segDom T ∧
      ‖(q (j + 1) : Ambient n) - q j‖ < T.δ)
    (hq' : ShortPolygon M.δ (refine r N F M.seg hq))
    (hne' : ∀ i, refine r N F M.seg hq (i + 1) ≠ refine r N F M.seg hq i)
    (hcrit : fderiv ℝ (energy F q) (base q) = 0)
    (hs : (hessian F q).toLinearMap.IsSymmetric)
    (hs' : (hessian F (refine r N F M.seg hq)).toLinearMap.IsSymmetric) :
    index F (refine r N F M.seg hq) hs' = index F q hs := by
  have hc := coarse_refine r N F M.seg hq
  have hf₁ : ContDiffAt ℝ 2 (energy F q) (base q) :=
    (energy_contDiffAt F M.smooth hq hne).of_le (by norm_num)
  have hf₂ : ContDiffAt ℝ 2 (energy F (refine r N F M.seg hq))
      (base (refine r N F M.seg hq)) :=
    (energy_contDiffAt F M.smooth hq' hne').of_le (by norm_num)
  have h := IndexComparison.sigNeg_eq_of_retraction (refineCoord_base M r N hq)
    (coarseL_base r N hc) hf₁ hf₂ hcrit
    (refineCoord_differentiableAt M r N hq hne hpk).hasFDerivAt (coarseL r N).hasFDerivAt
    (eventually_energy_refine M r N hq hne hpk hq')
    ((eventually_short hq').mono fun y hy => energy_coarse_le M r N hc hy)
  rw [index, index, OperatorIndex.finrank_negative, OperatorIndex.finrank_negative]
  exact h.symm

/-- The same, for any polygon equal to the refinement. -/
theorem index_eq_of_refine {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q)
    (hne : ∀ j, q (j + 1) ≠ q j)
    (hpk : ∀ j : ZMod N, ∃ T : SegChart F, q j ∈ segDom T ∧
      ‖(q (j + 1) : Ambient n) - q j‖ < T.δ)
    {q' : ZMod (r * N) → Sphere n} (he : refine r N F M.seg hq = q')
    (hq' : ShortPolygon M.δ q') (hne' : ∀ i, q' (i + 1) ≠ q' i)
    (hcrit : fderiv ℝ (energy F q) (base q) = 0)
    (hs : (hessian F q).toLinearMap.IsSymmetric)
    (hs' : (hessian F q').toLinearMap.IsSymmetric) : index F q' hs' = index F q hs := by
  subst he
  exact index_refine M r N hq hne hpk hq' hne' hcrit hs hs'

end Refinement

/-! ### Samples of a closed geodesic -/

section Samples

open Finsler.SmoothSobolev Finsler.PolygonGeodesic Finsler.GeodesicArcs

variable {F : ReversibleMetric n} (M : SegmentData F)

/-- The index of the polygon of samples only depends on the number of samples. -/
theorem index_sample_congr (u : SphereLoop n) {K K' : ℕ} [NeZero K] [NeZero K'] (h : K = K')
    (hs : (hessian F (samplePoly K u)).toLinearMap.IsSymmetric)
    (hs' : (hessian F (samplePoly K' u)).toLinearMap.IsSymmetric) :
    index F (samplePoly K u) hs = index F (samplePoly K' u) hs' := by
  subst h
  rfl

/-- **The index of the samples of a closed geodesic is invariant under refinement.** For N
large, the polygon of the N samples of a closed geodesic is short, has no zero edges, and the
polygon of the r N samples has the same index, for every r ≥ 1. -/
theorem exists_index_sample_mul (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      ShortPolygon M.δ (samplePoly N (ofSmooth g.loop)) ∧
      (∀ i, samplePoly N (ofSmooth g.loop) (i + 1) ≠ samplePoly N (ofSmooth g.loop) i) ∧
      ∀ (r : ℕ) [NeZero r]
        (hs : (hessian F (samplePoly N (ofSmooth g.loop))).toLinearMap.IsSymmetric)
        (hs' : (hessian F (samplePoly (r * N) (ofSmooth g.loop))).toLinearMap.IsSymmetric),
        index F (samplePoly (r * N) (ofSmooth g.loop)) hs' =
          index F (samplePoly N (ofSmooth g.loop)) hs := by
  obtain ⟨δa, hδa, ι, S, hcover, hδS, -⟩ := exists_segment_atlas F
  obtain ⟨N₁, hN₁⟩ := polyCritical_of_closedGeodesic F (lt_min M.pos hδa)
    (fun P Q hne h => M.smooth P Q hne (h.trans_le (min_le_left _ _))) g
  obtain ⟨N₂, hN₂⟩ := broken_sample_closedGeodesic M g
  obtain ⟨h₀, hh₀, hscale⟩ := exists_arc_scale (F := F) (γ := g.loop)
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (1 / h₀)
  -- the facts for every large number of samples
  have hfacts : ∀ K : ℕ, max N₁ (max N₂ (N₃ + 1)) ≤ K → ∀ [NeZero K],
      ShortPolygon M.δ (samplePoly K (ofSmooth g.loop)) ∧
      ShortPolygon δa (samplePoly K (ofSmooth g.loop)) ∧
      (∀ i, samplePoly K (ofSmooth g.loop) (i + 1) ≠ samplePoly K (ofSmooth g.loop) i) ∧
      PolyCritical F K (samplePoly K (ofSmooth g.loop)) := by
    intro K hK _
    have hK1 : N₁ ≤ K := (le_max_left _ _).trans hK
    have hK3 : N₃ + 1 ≤ K := ((le_max_right _ _).trans (le_max_right _ _)).trans hK
    obtain ⟨hshort, hc, -⟩ := hN₁ K hK1
    have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_neZero K
    have hlt : 1 / (K : ℝ) < h₀ := by
      have h1 : 1 / h₀ < K := hN₃.trans (by exact_mod_cast hK3)
      rw [div_lt_iff₀ hKpos]
      rw [div_lt_iff₀ hh₀] at h1
      linarith
    exact ⟨fun i => (hshort i).trans_le (min_le_left _ _),
      fun i => (hshort i).trans_le (min_le_right _ _),
      fun i => samplePoly_ofSmooth_ne g hscale hlt i, hc⟩
  refine ⟨max N₁ (max N₂ (N₃ + 1)), fun N hN _ => ?_⟩
  obtain ⟨hq, hqa, hne, hc⟩ := hfacts N hN
  refine ⟨hq, hne, fun r _ hs hs' => ?_⟩
  have hrN : max N₁ (max N₂ (N₃ + 1)) ≤ r * N :=
    hN.trans (Nat.le_mul_of_pos_left N (Nat.pos_of_neZero r))
  obtain ⟨hq', -, hne', -⟩ := hfacts (r * N) hrN
  have hN2 : N₂ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have he : refine r N F M.seg hq = samplePoly (r * N) (ofSmooth g.loop) := by
    unfold refine
    rw [hN₂ N hN2 hq]
  have hpk : ∀ j : ZMod N, ∃ T : SegChart F, samplePoly N (ofSmooth g.loop) j ∈ segDom T ∧
      ‖(samplePoly N (ofSmooth g.loop) (j + 1) : Ambient n) -
        samplePoly N (ofSmooth g.loop) j‖ < T.δ := by
    intro j
    obtain ⟨P₀, hP₀, hP⟩ := hcover (samplePoly N (ofSmooth g.loop) j)
    exact ⟨S P₀, hP, (hqa j).trans_le (hδS P₀ hP₀)⟩
  exact index_eq_of_refine M r N hq hne hpk he hq' hne'
    (fderiv_energy_eq_zero_of_polyCritical F M.smooth hq hne hc) hs hs'

/-- **The index of the samples of a closed geodesic does not depend on the number of samples.**
There is N₀ such that the polygons of N and of N' samples have the same index for all
N, N' ≥ N₀. -/
theorem exists_index_sample_eq (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ N₀ : ℕ, ∀ N N' : ℕ, N₀ ≤ N → N₀ ≤ N' → ∀ [NeZero N] [NeZero N']
      (hs : (hessian F (samplePoly N (ofSmooth g.loop))).toLinearMap.IsSymmetric)
      (hs' : (hessian F (samplePoly N' (ofSmooth g.loop))).toLinearMap.IsSymmetric),
      index F (samplePoly N' (ofSmooth g.loop)) hs' =
        index F (samplePoly N (ofSmooth g.loop)) hs := by
  obtain ⟨M⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_index_sample_mul M g
  refine ⟨N₀, fun N N' hN hN' _ _ hs hs' => ?_⟩
  obtain ⟨-, -, h1⟩ := hN₀ N hN
  obtain ⟨-, -, h2⟩ := hN₀ N' hN'
  have hNN' : N₀ ≤ N' * N := hN.trans (Nat.le_mul_of_pos_left N (Nat.pos_of_neZero N'))
  obtain ⟨hq3, hne3, -⟩ := hN₀ (N' * N) hNN'
  have hs3 := hessian_isSymmetric F M.smooth hq3 hne3
  have hN'N : N₀ ≤ N * N' := hN'.trans (Nat.le_mul_of_pos_left N' (Nat.pos_of_neZero N))
  obtain ⟨hq4, hne4, -⟩ := hN₀ (N * N') hN'N
  have hs4 := hessian_isSymmetric F M.smooth hq4 hne4
  rw [← h2 N hs' hs4, ← h1 N' hs hs3]
  exact index_sample_congr (ofSmooth g.loop) (Nat.mul_comm N N') hs4 hs3

end Samples

end

end Finsler.PolygonRefineIndex
