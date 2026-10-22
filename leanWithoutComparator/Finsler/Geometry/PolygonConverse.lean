module

public import Finsler.Geometry.PolygonSmooth
public import Finsler.Geometry.PolygonSampling
public import Finsler.Analysis.IntervalH1ChartSmooth
public import Finsler.Analysis.IntervalH1RadialRetraction
public import Finsler.Analysis.IntervalH1CurveRealization

/-! The converse direction of the critical point correspondence, abstract form. The linear
interpolation of a polygon of vectors is an H¹ loop depending linearly on the vertices. Adding the
interpolation of the vertex displacements to a loop and normalizing radially gives a curve of sphere
loops through it whose samples are the displaced vertices. If a tangent critical loop u has short
samples without zero edges and the polygon energy of its samples equals its energy, then along
every differentiable curve of sphere polygons the polygon energy is at most the energy of these
loops, with equality at the start, so the polygon of samples is critical. -/

@[expose] public section

namespace Finsler.PolygonConverse

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevEnergy Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.PolygonSmooth Finsler.PiecewiseC1 Finsler.SobolevOfPrimitive
open Finsler.SobolevRadialRetraction Finsler.SobolevChartSmooth Finsler.SobolevCurveRealization
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

/-- The k-th piece of the linear interpolation of a polygon of vectors. -/
def linPiece {N : ℕ} (d : ZMod N → Ambient n) (k : ℕ) (s : ℝ) : Ambient n :=
  (1 - s) • d k + s • d ((k : ZMod N) + 1)

/-- Its velocity. -/
def linVel {N : ℕ} (d : ZMod N → Ambient n) (k : ℕ) (_s : ℝ) : Ambient n :=
  d ((k : ZMod N) + 1) - d k

theorem linPiece_hasDerivAt {N : ℕ} (d : ZMod N → Ambient n) (k : ℕ) (s : ℝ) :
    HasDerivAt (linPiece d k) (linVel d k s) s := by
  have h1 : HasDerivAt (fun s : ℝ => (1 - s) • d k) ((-1 : ℝ) • d k) s :=
    ((hasDerivAt_id' s).const_sub 1).smul_const (d k)
  have h2 : HasDerivAt (fun s : ℝ => s • d ((k : ZMod N) + 1)) ((1 : ℝ) • d ((k : ZMod N) + 1)) s :=
    (hasDerivAt_id' s).smul_const _
  have h := h1.add h2
  unfold linPiece linVel
  convert h using 1
  rw [neg_one_smul, one_smul]
  abel

theorem linPiece_match {N : ℕ} (d : ZMod N → Ambient n) (j : ℕ) :
    linPiece d j 1 = linPiece d (j + 1) 0 := by
  unfold linPiece
  push_cast
  simp

/-- The linear interpolation as a curve. -/
def interpCurve (N : ℕ) (d : ZMod N → Ambient n) : ℝ → Ambient n := glue N (linPiece d)

/-- Its velocity. -/
def interpVel (N : ℕ) (d : ZMod N → Ambient n) : ℝ → Ambient n := glueVel N (linVel d)

section Interp

variable {N : ℕ} [NeZero N]

theorem interpCurve_continuousOn (d : ZMod N → Ambient n) :
    ContinuousOn (interpCurve N d) (Icc 0 1) :=
  glue_continuousOn (Nat.pos_of_neZero N)
    (fun k _ => fun s _ => (linPiece_hasDerivAt d k s).continuousAt.continuousWithinAt)
    (fun j _ => linPiece_match d j)

theorem interpCurve_eq_add_integral (d : ZMod N → Ambient n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    interpCurve N d t = interpCurve N d 0 + ∫ s in (0 : ℝ)..t, interpVel N d s :=
  glue_eq_add_integral (Nat.pos_of_neZero N)
    (fun k _ => fun s _ => (linPiece_hasDerivAt d k s).continuousAt.continuousWithinAt)
    (fun k _ s _ => linPiece_hasDerivAt d k s) (fun _ _ => continuousOn_const)
    (fun j _ => linPiece_match d j) ht

theorem interpVel_memLp (d : ZMod N → Ambient n) : MemLp (interpVel N d) 2 intervalMeasure := by
  have hN := Nat.pos_of_neZero N
  have hII := glueVel_intervalIntegrable hN (γ' := linVel d) (fun k _ => continuousOn_const)
  have hmeas : AEStronglyMeasurable (interpVel N d) intervalMeasure :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hII).aestronglyMeasurable
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ i : ZMod N, (‖d (i + 1)‖ + ‖d i‖) := ⟨_, rfl⟩
  have hbound : ∀ k < N, ∀ s ∈ Icc (0 : ℝ) 1, ‖linVel d k s‖ ≤ C := by
    intro k _ s _
    rw [hC]
    unfold linVel
    calc ‖d ((k : ZMod N) + 1) - d k‖ ≤ ‖d ((k : ZMod N) + 1)‖ + ‖d k‖ := norm_sub_le _ _
      _ ≤ ∑ i : ZMod N, (‖d (i + 1)‖ + ‖d i‖) :=
        Finset.single_le_sum (f := fun i : ZMod N => ‖d (i + 1)‖ + ‖d i‖)
          (fun _ _ => by positivity) (Finset.mem_univ _)
  apply MemLp.of_bound hmeas (N * C)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact norm_glueVel_le hN hbound (Ioo_subset_Icc_self ht)

/-- The linear interpolation as an H¹ graph element. -/
def interpLoop (N : ℕ) [NeZero N] (d : ZMod N → Ambient n) : Space n :=
  ofPrimitive (interpCurve_continuousOn d) (interpVel_memLp d)
    (fun _ ht => interpCurve_eq_add_integral d ht)

theorem representative_interpLoop (d : ZMod N → Ambient n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (interpLoop N d) t = interpCurve N d t :=
  representative_ofPrimitive _ _ _ ht

theorem interpCurve_sample (d : ZMod N → Ambient n) (i : ZMod N) :
    interpCurve N d ((i.val : ℝ) / N) = d i := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : i.val < N := ZMod.val_lt i
  have hmem : (i.val : ℝ) / N ∈ Ico ((i.val : ℝ) / N) (((i.val : ℝ) + 1) / N) :=
    ⟨le_rfl, div_lt_div_of_pos_right (by linarith) hN'⟩
  unfold interpCurve
  rw [glue_eq_of_mem_Ico hk _ hmem, mul_div_cancel₀ _ hN'.ne', sub_self]
  unfold linPiece
  simp

theorem interpLoop_add (d e : ZMod N → Ambient n) :
    interpLoop N (d + e) = interpLoop N d + interpLoop N e := by
  apply eq_of_representative_eqOn
  intro t ht
  rw [continuousRepresentative_add _ _ ht, representative_interpLoop _ ht,
    representative_interpLoop _ ht, representative_interpLoop _ ht]
  unfold interpCurve glue linPiece
  simp only [Pi.add_apply, smul_add]
  abel

theorem interpLoop_smul (a : ℝ) (d : ZMod N → Ambient n) :
    interpLoop N (a • d) = a • interpLoop N d := by
  apply eq_of_representative_eqOn
  intro t ht
  rw [continuousRepresentative_smul _ _ ht, representative_interpLoop _ ht,
    representative_interpLoop _ ht]
  unfold interpCurve glue linPiece
  simp only [Pi.smul_apply, smul_add, smul_comm a]

/-- The linear interpolation as a continuous linear map. -/
def interpCLM (N : ℕ) [NeZero N] : (ZMod N → Ambient n) →L[ℝ] Space n :=
  LinearMap.toContinuousLinearMap
    { toFun := interpLoop N
      map_add' := interpLoop_add
      map_smul' := interpLoop_smul }

theorem interpCLM_apply (d : ZMod N → Ambient n) : interpCLM N d = interpLoop N d := rfl

theorem interpCurve_one (d : ZMod N → Ambient n) : interpCurve N d 1 = d 0 := by
  have hN := Nat.pos_of_neZero N
  have hloc : pieceLoc N 1 = 1 := by
    unfold pieceLoc
    rw [pieceIdx_one, natCast_pred hN]
    ring
  unfold interpCurve glue
  rw [pieceIdx_one, hloc]
  unfold linPiece
  have hz : ((N - 1 : ℕ) : ZMod N) + 1 = 0 := by
    have h : ((N - 1 + 1 : ℕ) : ZMod N) = 0 := by
      rw [Nat.sub_add_cancel hN, ZMod.natCast_self]
    rw [Nat.cast_add, Nat.cast_one] at h
    exact h
  rw [hz]
  simp

theorem interpLoop_periodic (d : ZMod N → Ambient n) : interpLoop N d ∈ periodicSubmodule n := by
  have h0 : interpCurve N d 0 = d 0 := by
    have h := interpCurve_sample d 0
    simpa using h
  exact ofPrimitive_periodic _ _ _ ((interpCurve_one d).trans h0.symm)

end Interp

section Converse

variable {N : ℕ} [NeZero N]

/-- The loop u with the interpolated displacement d of its samples added. -/
def displaced (u : SphereLoop n) (d : ZMod N → Ambient n) : periodicSubmodule n :=
  ⟨(u.data : Space n) + interpLoop (n := n) N d, add_mem u.data.2 (interpLoop_periodic d)⟩

theorem displaced_eq {u : SphereLoop n} {d : ZMod N → Ambient n} (hd : ∀ i, d i = 0) :
    displaced u d = u.data := by
  apply Subtype.ext
  change (u.data : Space n) + interpLoop (n := n) N d = u.data
  apply eq_of_representative_eqOn
  intro t ht
  rw [continuousRepresentative_add _ _ ht, representative_interpLoop _ ht]
  have h : interpCurve N d t = 0 := by
    unfold interpCurve glue linPiece
    rw [hd, hd, smul_zero, smul_zero, add_zero]
  rw [h]
  exact add_zero _

theorem displaced_zero (u : SphereLoop n) : displaced (N := N) u 0 = u.data :=
  displaced_eq fun _ => rfl

theorem displaced_continuous (u : SphereLoop n) : Continuous (displaced (N := N) u) := by
  apply Continuous.subtype_mk
  exact continuous_const.add ((interpCLM (n := n) N).continuous.congr fun d => interpCLM_apply d)

open Classical in
/-- The displaced loop normalized onto the sphere (the loop itself far from it). -/
def varLoop (u : SphereLoop n) (d : ZMod N → Ambient n) : SphereLoop n :=
  if h : displaced u d ∈ radialDomain n then retraction ⟨displaced u d, h⟩ else u

theorem varLoop_eq {u : SphereLoop n} {d : ZMod N → Ambient n} (hd : ∀ i, d i = 0) :
    varLoop u d = u := by
  have h : displaced u d ∈ radialDomain n := by
    rw [displaced_eq hd]
    exact mem_radialDomain u
  unfold varLoop
  rw [dite_eq_left h]
  have e : (⟨displaced u d, h⟩ : radialDomain n) = ⟨u.data, mem_radialDomain u⟩ :=
    Subtype.ext (displaced_eq hd)
  rw [e]
  exact retraction_sphereLoop u

theorem varLoop_data (u : SphereLoop n) {d : ZMod N → Ambient n}
    (h : displaced u d ∈ radialDomain n) :
    ((varLoop u d).data : Space n) = radialData ((u.data : Space n) + interpLoop (n := n) N d) := by
  unfold varLoop
  rw [dite_eq_left h]
  rfl

theorem sampleN_varLoop (u : SphereLoop n) {d : ZMod N → Ambient n}
    (h : displaced u d ∈ radialDomain n) (hd : ∀ i, ‖sampleN N u i + d i‖ = 1) :
    sampleN N (varLoop u d) = sampleN N u + d := by
  funext i
  have hs : (sampleTime N i : ℝ) ∈ Icc (0 : ℝ) 1 := (sampleTime N i).2
  change continuousRepresentative ((varLoop u d).data : Space n) (sampleTime N i) = _
  rw [varLoop_data u h, representative_radialData _ hs, continuousRepresentative_add _ _ hs,
    representative_interpLoop _ hs]
  change radial (sampleN N u i + interpCurve N d ((i.val : ℝ) / N)) = _
  rw [interpCurve_sample]
  exact radial_of_norm_one (hd i)

end Converse

section Main

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (Finsler.EnergySphereSmooth.ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {N : ℕ} [NeZero N]

include hδ in
/-- A tangent critical loop whose samples form a short polygon without zero edges and whose energy
equals the polygon energy of its samples has a critical polygon of samples. -/
theorem polyCritical_of_tangentCritical {u : SphereLoop n}
    (hu : Finsler.SobolevCurveVariation.TangentCritical F u)
    (hq : ShortPolygon δ (samplePoly N u)) (hne : ∀ i, samplePoly N u (i + 1) ≠ samplePoly N u i)
    (hE : polyEnergy F N (sampleN N u) = energy F u) : PolyCritical F N (samplePoly N u) := by
  intro c c' hc0 hcn hcd
  have hf := polyEnergy_hasDerivAt_curve F hδ hq hne hc0 hcn hcd
  have hc0' : c 0 = sampleN N u := hc0
  have hcont : ContinuousAt (fun r => displaced (N := N) u (c r - sampleN N u)) 0 :=
    (displaced_continuous u).continuousAt.comp (hcd.continuousAt.sub continuousAt_const)
  have hz : ∀ i, (c 0 - sampleN N u) i = 0 := fun i => by
    rw [Pi.sub_apply, hc0', sub_self]
  have hdom0 : displaced (N := N) u (c 0 - sampleN N u) ∈ radialDomain n := by
    rw [displaced_eq hz]
    exact mem_radialDomain u
  have hdom : ∀ᶠ r in 𝓝 (0 : ℝ), displaced (N := N) u (c r - sampleN N u) ∈ radialDomain n :=
    hcont.preimage_mem_nhds (radialDomain_open.mem_nhds hdom0)
  have hw0 : varLoop u (c 0 - sampleN N u) = u := varLoop_eq hz
  have hdata : (fun r => ((varLoop u (c r - sampleN N u)).data : Space n)) =ᶠ[𝓝 0]
      fun r => radialData ((u.data : Space n) + interpLoop (n := n) N (c r - sampleN N u)) := by
    filter_upwards [hdom] with r hr
    exact varLoop_data u hr
  have hv : HasDerivAt (fun r => (u.data : Space n) + interpLoop (n := n) N (c r - sampleN N u))
      (interpCLM N c') 0 := by
    have h1 : HasDerivAt (fun r => interpCLM (n := n) N (c r - sampleN N u)) (interpCLM N c') 0 :=
      (interpCLM N).hasFDerivAt.comp_hasDerivAt 0 (hcd.sub_const (sampleN N u))
    exact h1.const_add _
  have hrad := (radialData_hasFDerivAt ((u.data : Space n) +
    interpLoop (n := n) N (c 0 - sampleN N u))).comp_hasDerivAt 0 hv
  have hwd := hrad.congr_of_eventuallyEq hdata
  have hE' := (tangentCritical_iff_curve_stationary F u).mp hu
    (fun r => varLoop u (c r - sampleN N u)) _ hw0 hwd
  have hg := hE'.sub hf
  have hsamp : ∀ᶠ r in 𝓝 (0 : ℝ), sampleN N (varLoop u (c r - sampleN N u)) = c r := by
    filter_upwards [hdom] with r hr
    have hn : ∀ i, ‖sampleN N u i + (c r - sampleN N u) i‖ = 1 := by
      intro i
      rw [Pi.sub_apply, add_sub_cancel]
      exact hcn r i
    rw [sampleN_varLoop u hr hn]
    funext i
    rw [Pi.add_apply, Pi.sub_apply, add_sub_cancel]
  have hmin : IsLocalMin (fun r => energy F (varLoop u (c r - sampleN N u)) -
      polyEnergy F N (c r)) 0 := by
    filter_upwards [hsamp] with r hr
    have h1 := polyEnergy_sample_le F (N := N) (varLoop u (c r - sampleN N u))
    rw [hr] at h1
    have h0 : energy F (varLoop u (c 0 - sampleN N u)) - polyEnergy F N (c 0) = 0 := by
      rw [hw0, hc0', hE, sub_self]
    linarith
  have hA := hmin.hasDerivAt_eq_zero hg
  rw [zero_sub, neg_eq_zero] at hA
  rw [hA] at hf
  exact hf

end Main

end

end Finsler.PolygonConverse
