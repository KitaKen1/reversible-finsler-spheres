module

public import Finsler.Geometry.PolygonSmooth
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! Finite-dimensional Hilbert coordinates for sphere polygons. The chart is the actual product
of the standard sphere charts, transported to the L2 product of their coordinate spaces. Its
ambient inverse has unit vertices everywhere and is smooth on the chart target. The coordinate
energy is the actual polygon energy, is C3 near short polygons without zero edges, and has zero
first derivative at a polygon that is stationary along all actual sphere-polygon curves. -/

@[expose] public section

namespace Finsler.PolygonChart

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.EnergySphereSmooth
open Set Filter
open scoped Topology ContDiff Manifold

noncomputable section

variable {n N : ℕ} [NeZero N]

/-- The finite L2 product of the genuine sphere coordinate spaces. -/
abbrev Model (n N : ℕ) := PiLp 2 (fun _ : ZMod N => Coordinates n)

/-- The actual product sphere chart, with a Hilbert coordinate space. -/
def chart (q : ZMod N → Sphere n) : OpenPartialHomeomorph (ZMod N → Sphere n) (Model n N) :=
  (OpenPartialHomeomorph.pi fun i => chartAt (Coordinates n) (q i)).trans
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : ZMod N => Coordinates n)).symm.toHomeomorph.toOpenPartialHomeomorph

/-- The coordinate of the central polygon. -/
def base (q : ZMod N → Sphere n) : Model n N :=
  WithLp.toLp 2 (fun i => extChartAt (𝓡 n) (q i) (q i))

/-- The ambient inverse coordinate map, defined at every coordinate vector. -/
def decode (q : ZMod N → Sphere n) (x : Model n N) : ZMod N → Ambient n :=
  fun i => inverseAmbient (q i) (x i)

theorem chart_apply (q P : ZMod N → Sphere n) :
    chart q P = WithLp.toLp 2 (fun i => extChartAt (𝓡 n) (q i) (P i)) := rfl

theorem chart_symm_apply (q : ZMod N → Sphere n) (x : Model n N) (i : ZMod N) :
    (chart q).symm x i = inverseSphere (q i) (x i) := rfl

theorem mem_chart_source (q P : ZMod N → Sphere n) :
    P ∈ (chart q).source ↔ ∀ i, P i ∈ (extChartAt (𝓡 n) (q i)).source := by
  simp [chart, OpenPartialHomeomorph.pi, extChartAt]

theorem mem_chart_target (q : ZMod N → Sphere n) (x : Model n N) :
    x ∈ (chart q).target ↔ ∀ i, x i ∈ (extChartAt (𝓡 n) (q i)).target := by
  simp [chart, OpenPartialHomeomorph.pi, extChartAt]

theorem base_mem_target (q : ZMod N → Sphere n) : base q ∈ (chart q).target := by
  rw [mem_chart_target]
  intro i
  exact (extChartAt (𝓡 n) (q i)).map_source (mem_extChartAt_source (q i))

omit [NeZero N] in
theorem decode_base (q : ZMod N → Sphere n) :
    decode q (base q) = fun i => (q i : Ambient n) := by
  funext i
  exact congrArg Subtype.val ((extChartAt (𝓡 n) (q i)).left_inv (mem_extChartAt_source (q i)))

omit [NeZero N] in
theorem norm_decode (q : ZMod N → Sphere n) (x : Model n N) (i : ZMod N) :
    ‖decode q x i‖ = 1 := mem_sphere_zero_iff_norm.mp (inverseSphere (q i) (x i)).2

theorem decode_chart (q P : ZMod N → Sphere n) (hP : P ∈ (chart q).source) :
    decode q (chart q P) = fun i => (P i : Ambient n) := by
  funext i
  exact congrArg Subtype.val ((extChartAt (𝓡 n) (q i)).left_inv ((mem_chart_source q P).mp hP i))

theorem decode_contDiffAt (q : ZMod N → Sphere n) {x : Model n N}
    (hx : x ∈ (chart q).target) : ContDiffAt ℝ ∞ (decode q) x := by
  apply contDiffAt_pi.mpr
  intro i
  exact (inverseAmbient_smoothAt (q i) ((mem_chart_target q x).mp hx i)).comp x
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ZMod N => Coordinates n) i).contDiff.contDiffAt

/-- The genuine polygon energy in finite-dimensional local coordinates. -/
def energy (F : ReversibleMetric n) (q : ZMod N → Sphere n) (x : Model n N) : ℝ :=
  polyEnergyN F N (decode q x)

omit [NeZero N] in
theorem energy_eq (F : ReversibleMetric n) (q : ZMod N → Sphere n) (x : Model n N) :
    energy F q x = polyEnergy F N (decode q x) := polyEnergyN_eq F N (norm_decode q x)

omit [NeZero N] in
theorem energy_base (F : ReversibleMetric n) (q : ZMod N → Sphere n) :
    energy F q (base q) = polyEnergy F N (fun i => (q i : Ambient n)) := by
  rw [energy_eq, decode_base]

/-- C3 regularity at a short central polygon with no zero edges. -/
theorem energy_contDiffAt (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i) :
    ContDiffAt ℝ 3 (energy F q) (base q) := by
  have hE := polyEnergyN_contDiffAt F hδ hq hne
  rw [← decode_base q] at hE
  exact hE.comp (base q) ((decode_contDiffAt q (base_mem_target q)).of_le (by simp))

/-- Actual polygon stationarity implies zero derivative of the coordinate energy. The affine
coordinate curves give globally defined sphere-polygon curves via the inverse chart. -/
theorem fderiv_energy_eq_zero_of_polyCritical (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)
    (hc : PolyCritical F N q) : fderiv ℝ (energy F q) (base q) = 0 := by
  have hE := (energy_contDiffAt F hδ hq hne).differentiableAt (by norm_num)
  have hd := (decode_contDiffAt q (base_mem_target q)).differentiableAt (by simp)
  apply ContinuousLinearMap.ext
  intro v
  have hline : HasDerivAt (fun s : ℝ => base q + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (base q)
  have hcurve : HasDerivAt (fun s : ℝ => decode q (base q + s • v))
      (fderiv ℝ (decode q) (base q) v) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hstationary := hc _ _ (by simpa using decode_base q) (fun s i => norm_decode q _ i) hcurve
  have hderiv : HasDerivAt (fun s : ℝ => energy F q (base q + s • v))
      (fderiv ℝ (energy F q) (base q) v) 0 :=
    hE.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have he : (fun s : ℝ => energy F q (base q + s • v)) =
      fun s => polyEnergy F N (decode q (base q + s • v)) :=
    funext fun s => energy_eq F q _
  rw [he] at hderiv
  exact hderiv.unique hstationary

/-- Uniform short-segment regularity supplies actual C3 coordinate energy near every nonzero-edge
polygon below one positive radius. -/
theorem exists_energy_contDiffAt (F : ReversibleMetric n) :
    ∃ δ > 0, ∀ q : ZMod N → Sphere n, ShortPolygon δ q → (∀ i, q (i + 1) ≠ q i) →
      ContDiffAt ℝ 3 (energy F q) (base q) := by
  obtain ⟨δ, hδ, hs⟩ := exists_ambientMinEnergy_contDiffAt F
  exact ⟨δ, hδ, fun q hq hn => energy_contDiffAt F hs hq hn⟩

end

end Finsler.PolygonChart
