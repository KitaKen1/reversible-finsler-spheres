module

public import Finsler.Analysis.IntervalH1Concat
public import Finsler.Analysis.CompactH1Alignment

/-! Pointwise concatenation in the actual H¹ sphere-loop space and its exact
energy filtration. Continuity and a singular-chain product are separate tasks. -/

@[expose] public section

namespace Finsler.H1LoopJoin

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevConcat Finsler.SobolevSpherePath
open Finsler.CompactH1Alignment Finsler.SobolevEnergy
open Set

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000

theorem periodic_trace (u : SphereLoop n) :
    continuousRepresentative (u.data : Space n) 1 = basepoint u :=
  (mem_periodicSubmodule_iff (u.data : Space n)).mp u.data.property

theorem end_match (u w : SphereLoop n) (h : basepoint u = basepoint w) :
    continuousRepresentative (u.data : Space n) 1 =
      continuousRepresentative (w.data : Space n) 0 :=
  (periodic_trace u).trans h

def join (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (u w : SphereLoop n)
    (h : basepoint u = basepoint w) : SphereLoop n where
  data := ⟨concat (u.data : Space n) (w.data : Space n) ha0 ha1, by
    apply (mem_periodicSubmodule_iff
      (concat (u.data : Space n) (w.data : Space n) ha0 ha1)).mpr
    change continuousRepresentative (concat (u.data : Space n) (w.data : Space n) ha0 ha1) 1 =
      continuousRepresentative (concat (u.data : Space n) (w.data : Space n) ha0 ha1) 0
    exact (representative_concat_one _ _ ha0 ha1 (end_match u w h)).trans
      ((periodic_trace w).trans (h.symm.trans
        (representative_concat_zero (u.data : Space n) (w.data : Space n) ha0 ha1).symm))⟩
  sphere_constraint t := concat_mem (u.data : Space n) (w.data : Space n) ha0 ha1
    (sphereLoop_mem u) (sphereLoop_mem w) (end_match u w h) t t.property

theorem basepoint_join (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (u w : SphereLoop n)
    (h : basepoint u = basepoint w) : basepoint (join a ha0 ha1 u w h) = basepoint u :=
  representative_concat_zero (u.data : Space n) (w.data : Space n) ha0 ha1

theorem energy_join (F : ReversibleMetric n) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (u w : SphereLoop n) (h : basepoint u = basepoint w) :
    energy F (join a ha0 ha1 u w h) = energy F u / a + energy F w / (1 - a) :=
  pathEnergy_concat (u := (u.data : Space n)) (w := (w.data : Space n))
    (ha0 := ha0) (ha1 := ha1) (F := F)
    (hu := sphereLoop_mem u) (hw := sphereLoop_mem w) (hmatch := end_match u w h)

theorem budget_identity {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p ^ 2 / (p / (p + q)) + q ^ 2 / (1 - p / (p + q)) = (p + q) ^ 2 := by
  have hs : p + q ≠ 0 := (add_pos hp hq).ne'
  have he : 1 - p / (p + q) = q / (p + q) := by field_simp; ring
  rw [he]
  field_simp

/-- Fixed positive input cut bounds determine the split, with no multiplicative loss. -/
theorem energy_join_cut (F : ReversibleMetric n) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (u w : SphereLoop n) (h : basepoint u = basepoint w)
    (hu : energy F u < p ^ 2) (hw : energy F w < q ^ 2) :
    energy F (join (p / (p + q)) (div_pos hp (add_pos hp hq))
      ((div_lt_one (add_pos hp hq)).mpr (by linarith)) u w h) < (p + q) ^ 2 := by
  have ha0 : 0 < p / (p + q) := div_pos hp (add_pos hp hq)
  have ha1 : p / (p + q) < 1 := (div_lt_one (add_pos hp hq)).mpr (by linarith)
  rw [energy_join]
  calc
    _ < p ^ 2 / (p / (p + q)) + q ^ 2 / (1 - p / (p + q)) :=
      add_lt_add ((div_lt_div_iff_of_pos_right ha0).mpr hu)
        ((div_lt_div_iff_of_pos_right (sub_pos.mpr ha1)).mpr hw)
    _ = (p + q) ^ 2 := budget_identity hp hq


end
end Finsler.H1LoopJoin
