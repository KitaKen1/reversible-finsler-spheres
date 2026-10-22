module

public import Finsler.Analysis.IntervalH1EnergyContinuity
public import Finsler.Analysis.IntervalH1HalfRootCuts

/-! Topology of actual Finsler energy cuts in the original strong H¹ metric.
The energy continuity theorem gives open cuts and closed zero/sublevel sets.
The half-period fixed set uses the genuine continuous circle action. -/

@[expose] public section

namespace Finsler.SobolevCutTopology

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevHalfRoot Finsler.SobolevReflectionAction Set
open Finsler.Geometry (ReversibleMetric)
open scoped Topology

noncomputable section

theorem energyCut_isOpen {n : ℕ} (F : ReversibleMetric n) (b : ℝ) :
    IsOpen (energyCut F b) := by
  change IsOpen {u : SphereLoop n | Real.sqrt (energy F u) < b}
  exact isOpen_lt (sqrt_energy_continuous F) continuous_const

theorem energyCut_mem_nhds {n : ℕ} (F : ReversibleMetric n) {b : ℝ}
    {u : SphereLoop n} (hu : u ∈ energyCut F b) : energyCut F b ∈ 𝓝 u :=
  (energyCut_isOpen F b).mem_nhds hu

theorem exists_ball_subset_energyCut {n : ℕ} (F : ReversibleMetric n) {b : ℝ}
    {u : SphereLoop n} (hu : u ∈ energyCut F b) :
    ∃ ε > 0, Metric.ball u ε ⊆ energyCut F b :=
  Metric.mem_nhds_iff.mp (energyCut_mem_nhds F hu)

theorem jointEnergyCut_isOpen {n : ℕ} (F : ReversibleMetric n) :
    IsOpen {p : ℝ × SphereLoop n | Real.sqrt (energy F p.2) < p.1} :=
  isOpen_lt ((sqrt_energy_continuous F).comp continuous_snd) continuous_fst

def closedEnergyCut {n : ℕ} (F : ReversibleMetric n) (b : ℝ) : Set (SphereLoop n) :=
  {u | Real.sqrt (energy F u) ≤ b}

theorem closedEnergyCut_isClosed {n : ℕ} (F : ReversibleMetric n) (b : ℝ) :
    IsClosed (closedEnergyCut F b) :=
  isClosed_le (sqrt_energy_continuous F) continuous_const

theorem closure_energyCut_subset {n : ℕ} (F : ReversibleMetric n) (b : ℝ) :
    closure (energyCut F b) ⊆ closedEnergyCut F b := by
  apply (closedEnergyCut_isClosed F b).closure_subset_iff.mpr
  intro u hu
  exact (mem_energyCut F b u).mp hu |>.le

theorem range_constantSphereLoop_isClosed {n : ℕ} (F : ReversibleMetric n) :
    IsClosed (range (constantSphereLoop : Sphere n → SphereLoop n)) := by
  have heq : range (constantSphereLoop : Sphere n → SphereLoop n) =
      {u | energy F u = 0} := by
    ext u
    simpa only [mem_range, mem_ofPred_eq, eq_comm] using
      (energy_eq_zero_iff_constant F u).symm
  rw [heq]
  exact isClosed_eq (energy_continuous F) continuous_const

theorem nonconstantSphereSet_isOpen {n : ℕ} (F : ReversibleMetric n) :
    IsOpen {u : SphereLoop n | ¬ ∃ x : Sphere n, u = constantSphereLoop x} := by
  have heq : {u : SphereLoop n | ¬ ∃ x : Sphere n, u = constantSphereLoop x} =
      {u | 0 < energy F u} := by
    ext u
    exact (energy_pos_iff_nonconstant F u).symm
  rw [heq]
  exact isOpen_lt continuous_const (energy_continuous F)

theorem halfFixedSet_isClosed (n : ℕ) : IsClosed (halfFixedSet n) := by
  change IsClosed {u : SphereLoop n | halfPhase +ᵥ u = u}
  have h : Continuous (fun u : SphereLoop n => halfPhase +ᵥ u) :=
    Continuous.vadd
      (continuous_const : Continuous (fun _ : SphereLoop n => halfPhase))
      (continuous_id : Continuous (fun u : SphereLoop n => u))
  exact isClosed_eq h continuous_id

instance halfFixed_completeSpace (n : ℕ) : CompleteSpace (HalfFixed n) :=
  (halfFixedSet_isClosed n).isComplete.completeSpace_coe

theorem halfFixedCut_isOpen {n : ℕ} (F : ReversibleMetric n) (b : ℝ) :
    IsOpen (halfFixedCut F b) := by
  change IsOpen (Subtype.val ⁻¹' energyCut F b : Set (HalfFixed n))
  exact (energyCut_isOpen F b).preimage continuous_subtype_val

end

end Finsler.SobolevCutTopology
