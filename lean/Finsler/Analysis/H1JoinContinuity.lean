module

public import Finsler.Analysis.H1LoopJoin
public import Finsler.Analysis.H1ConcatContinuity
public import Finsler.Topology.Birkhoff

/-! Actual joint strong-H¹ continuity and a filtered based-loop join map.
This is a continuous map on matching pairs, not a Thom/cut-join chain operation. -/

@[expose] public section

namespace Finsler.H1JoinContinuity

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1LoopJoin Finsler.H1ConcatContinuity
open Finsler.BorelLoop Set
open scoped Topology

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000

def composable (n : ℕ) : Set (SphereLoop n × SphereLoop n) :=
  {p | basepoint p.1 = basepoint p.2}

def weakPair (p : composable n) : matching n :=
  ⟨((p.val.1.data : Space n), (p.val.2.data : Space n)), by
    change continuousRepresentative (p.val.1.data : Space n) 1 -
      continuousRepresentative (p.val.2.data : Space n) 0 = 0
    exact sub_eq_zero.mpr (end_match p.val.1 p.val.2 p.property)⟩

theorem continuous_weakPair : Continuous (weakPair : composable n → matching n) := by
  have hp : Continuous (fun p : composable n =>
      ((p.val.1.data : Space n), (p.val.2.data : Space n))) :=
    ((sphereLoop_data_isometry n).continuous.comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
    ((sphereLoop_data_isometry n).continuous.comp
      (continuous_snd.comp continuous_subtype_val))
  exact hp.subtype_mk _

theorem continuous_join (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Continuous (fun p : composable n => join a ha0 ha1 p.val.1 p.val.2 p.property) := by
  have hdata : Continuous (fun p : composable n =>
      ((join a ha0 ha1 p.val.1 p.val.2 p.property).data : Space n)) :=
    ((concatenationCLM (n := n) a ha0 ha1).continuous.comp
      (continuous_weakPair (n := n))).congr (fun p => rfl)
  apply continuous_iff_continuousAt.mpr
  intro p
  apply sphereLoop_tendsto_iff.mpr
  exact hdata.continuousAt

def joinMap (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) : C(composable n, SphereLoop n) :=
  ⟨fun p => join a ha0 ha1 p.val.1 p.val.2 p.property, continuous_join a ha0 ha1⟩

def filteredPair (F : ReversibleMetric n) (p q : ℝ) : Set (lev F p × lev F q) :=
  {z | basepoint z.1.val = basepoint z.2.val}

def levelPair (F : ReversibleMetric n) (p q : ℝ) (z : filteredPair F p q) : composable n :=
  ⟨(z.val.1.val, z.val.2.val), z.property⟩

theorem continuous_levelPair (F : ReversibleMetric n) (p q : ℝ) :
    Continuous (levelPair F p q) := by
  have h1 : Continuous (fun z : filteredPair F p q => z.val.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  have h2 : Continuous (fun z : filteredPair F p q => z.val.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  exact (h1.prodMk h2).subtype_mk _

/-- A genuine continuous map into the original project cut t_(p+q). -/
def filteredJoin (F : ReversibleMetric n) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    C(filteredPair F p q, lev F (p + q)) := by
  let a : ℝ := p / (p + q)
  have ha0 : 0 < a := div_pos hp (add_pos hp hq)
  have ha1 : a < 1 := (div_lt_one (add_pos hp hq)).mpr (by linarith)
  refine ⟨fun z => ⟨join a ha0 ha1 z.val.1.val z.val.2.val z.property, ?_⟩, ?_⟩
  · apply (Finsler.Birkhoff.mem_lev_iff (add_pos hp hq) _).mpr
    exact energy_join_cut F hp hq z.val.1.val z.val.2.val z.property
      ((Finsler.Birkhoff.mem_lev_iff hp _).mp z.val.1.property)
      ((Finsler.Birkhoff.mem_lev_iff hq _).mp z.val.2.property)
  · exact ((continuous_join (n := n) a ha0 ha1).comp
      (continuous_levelPair F p q)).subtype_mk _


end
end Finsler.H1JoinContinuity
