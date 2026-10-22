import HingstonBlocks
import Finsler.Geometry.SegmentContinuity
import Finsler.Analysis.H1FiberBase

/-!
# Connecting two groups of loop blocks

Actual H¹ loops at different basepoints are joined by a sphere path and its
reverse. Positive durations `a, c, b, c` are assigned to the first loop,
connector, second loop and return connector. The energy identity retains
the original loop energies and the connector cost separately.

This is a construction for the enlarged-domain step of the surface proof.
The connector duration is positive, even on the diagonal. Removing the
resulting pauses and proving the required relative homotopy are separate
obligations; this module does not assert a completed homological filling.
-/

namespace Finsler.HingstonConnectors

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevSpherePath Finsler.SobolevConcat Finsler.SobolevReverse
open Finsler.CompactH1Alignment Finsler.H1LoopJoin Finsler.SphereDistance
open Finsler.SobolevEnergy Finsler.H1ConcatContinuity

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

/-- Two actual loops and a sphere path from the first basepoint to the second. -/
def Data (n : ℕ) :=
  {z : SphereLoop n × SphereLoop n × Space n //
    z.2.2 ∈ pathsBetween n (basepoint z.1) (basepoint z.2.1)}

instance : TopologicalSpace (Data n) := inferInstanceAs
  (TopologicalSpace {z : SphereLoop n × SphereLoop n × Space n //
    z.2.2 ∈ pathsBetween n (basepoint z.1) (basepoint z.2.1)})

private def append {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u v : Space n) : Space n :=
  SobolevConcat.concat u v (div_pos ha (add_pos ha hb))
    ((div_lt_one (add_pos ha hb)).mpr (by linarith))

private theorem append_between {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u v : Space n} {P Q R : Ambient n}
    (hu : u ∈ pathsBetween n P Q) (hv : v ∈ pathsBetween n Q R) :
    append ha hb u v ∈ pathsBetween n P R := by
  have hm := hu.2.2.trans hv.2.1.symm
  exact ⟨concat_mem u v _ _ hu.1 hv.1 hm,
    (representative_concat_zero u v _ _).trans hu.2.1,
    (representative_concat_one u v _ _ hm).trans hv.2.2⟩

private theorem energy_append (F : ReversibleMetric n) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {u v : Space n} {P Q R : Ambient n}
    (hu : u ∈ pathsBetween n P Q) (hv : v ∈ pathsBetween n Q R) :
    pathEnergy F (append ha hb u v) =
      (a + b) * (pathEnergy F u / a + pathEnergy F v / b) := by
  unfold append
  rw [pathEnergy_concat (u := u) (w := v) _ _ F hu.1 hv.1
    (hu.2.2.trans hv.2.1.symm)]
  have hs : 1 - a / (a + b) = b / (a + b) := by field_simp; ring
  rw [hs]
  field_simp

private theorem continuous_append {Z : Type*} [TopologicalSpace Z]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {u v : Z → Space n}
    (hu : Continuous u) (hv : Continuous v)
    (hm : ∀ z, continuousRepresentative (u z) 1 = continuousRepresentative (v z) 0) :
    Continuous (fun z => append ha hb (u z) (v z)) := by
  let f : Z → matching n := fun z => ⟨(u z, v z), by
    change continuousRepresentative (u z) 1 - continuousRepresentative (v z) 0 = 0
    exact sub_eq_zero.mpr (hm z)⟩
  have hf : Continuous f := (hu.prodMk hv).subtype_mk _
  let T : matching n →L[ℝ] Space n := concatenationCLM (n := n)
    (a / (a + b)) (div_pos ha (add_pos ha hb))
      ((div_lt_one (add_pos ha hb)).mpr (by linarith))
  have ht : Continuous (fun z : Z => T (f z)) := T.continuous.comp hf
  exact ht.congr (fun z => rfl)

private theorem loop_between (u : SphereLoop n) :
    (u.data : Space n) ∈ pathsBetween n (basepoint u) (basepoint u) :=
  ⟨sphereLoop_mem u, rfl, periodic_trace u⟩

variable {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)

private def firstPath (p : Data n) : Space n := append ha hc p.val.1.data p.val.2.2
private def secondPath (p : Data n) : Space n :=
  append hb hc p.val.2.1.data (reverseData p.val.2.2)

private theorem firstPath_between (p : Data n) :
    firstPath ha hc p ∈ pathsBetween n (basepoint p.val.1) (basepoint p.val.2.1) :=
  append_between ha hc (loop_between p.val.1) p.property

private theorem secondPath_between (p : Data n) :
    secondPath hb hc p ∈ pathsBetween n (basepoint p.val.2.1) (basepoint p.val.1) :=
  append_between hb hc (loop_between p.val.2.1) (reverseData_mem_pathsBetween p.property)

private def joinedData (p : Data n) : Space n :=
  append (add_pos ha hc) (add_pos hb hc) (firstPath ha hc p) (secondPath hb hc p)

private theorem joinedData_between (p : Data n) :
    joinedData ha hb hc p ∈ pathsBetween n (basepoint p.val.1) (basepoint p.val.1) :=
  append_between (add_pos ha hc) (add_pos hb hc)
    (firstPath_between ha hc p) (secondPath_between hb hc p)

/-- First loop, outward connector, second loop, return connector, rescaled
from durations `a, c, b, c` to one period. -/
def loop (p : Data n) : SphereLoop n where
  data := ⟨joinedData ha hb hc p, (mem_periodicSubmodule_iff _).mpr
    ((joinedData_between ha hb hc p).2.2.trans (joinedData_between ha hb hc p).2.1.symm)⟩
  sphere_constraint t := (joinedData_between ha hb hc p).1 t t.property

theorem basepoint_loop (p : Data n) :
    basepoint (loop ha hb hc p) = basepoint p.val.1 := (joinedData_between ha hb hc p).2.1

private theorem four_piece_identity (A B C : ℝ) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + c + (b + c)) *
      ((a + c) * (A / a + C / c) / (a + c) +
        (b + c) * (B / b + C / c) / (b + c)) =
      (a + b + 2 * c) * (A / a + B / b + 2 * C / c) := by
  have hac := (add_pos ha hc).ne'
  have hbc := (add_pos hb hc).ne'
  field_simp
  ring

/-- Reversibility makes the outward and return connector costs equal. -/
theorem energy_loop (F : ReversibleMetric n) (p : Data n) :
    energy F (loop ha hb hc p) = (a + b + 2 * c) *
      (energy F p.val.1 / a + energy F p.val.2.1 / b + 2 * pathEnergy F p.val.2.2 / c) := by
  have hrev : reverseData p.val.2.2 ∈ pathsBetween n
      (basepoint p.val.2.1) (basepoint p.val.1) := reverseData_mem_pathsBetween p.property
  have he1 := energy_append F ha hc (u := (p.val.1.data : Space n)) (v := p.val.2.2)
    (loop_between p.val.1) p.property
  have he2 := energy_append F hb hc (u := (p.val.2.1.data : Space n))
    (v := reverseData p.val.2.2) (loop_between p.val.2.1) hrev
  rw [pathEnergy_reverseData F p.val.2.2] at he2
  have he := energy_append F (add_pos ha hc) (add_pos hb hc)
    (u := firstPath ha hc p) (v := secondPath hb hc p)
    (firstPath_between ha hc p) (secondPath_between hb hc p)
  change pathEnergy F (firstPath ha hc p) = _ at he1
  change pathEnergy F (secondPath hb hc p) = _ at he2
  rw [he1, he2] at he
  exact he.trans (four_piece_identity (energy F p.val.1) (energy F p.val.2.1)
    (pathEnergy F p.val.2.2) ha hb hc)

/-- Joint strong H¹ continuity for a fixed positive duration allocation. -/
theorem continuous_loop : Continuous (loop (n := n) ha hb hc) := by
  have hu : Continuous (fun p : Data n => (p.val.1.data : Space n)) :=
    (sphereLoop_data_isometry n).continuous.comp (continuous_fst.comp continuous_subtype_val)
  have hv : Continuous (fun p : Data n => (p.val.2.1.data : Space n)) :=
    (sphereLoop_data_isometry n).continuous.comp
      (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
  have hw : Continuous (fun p : Data n => p.val.2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_subtype_val)
  have hfirst : Continuous (firstPath ha hc : Data n → Space n) :=
    continuous_append ha hc hu hw (fun p => (periodic_trace p.val.1).trans p.property.2.1.symm)
  have hsecond : Continuous (secondPath hb hc : Data n → Space n) :=
    continuous_append hb hc hv ((reverseData_isometry n).continuous.comp hw)
      (fun p => (periodic_trace p.val.2.1).trans
        (reverseData_mem_pathsBetween p.property).2.1.symm)
  have hwhole : Continuous (joinedData ha hb hc : Data n → Space n) :=
    continuous_append (add_pos ha hc) (add_pos hb hc) hfirst hsecond
      (fun p => (firstPath_between ha hc p).2.2.trans (secondPath_between hb hc p).2.1.symm)
  exact continuous_iff_continuousAt.mpr fun p => sphereLoop_tendsto_iff.mpr hwhole.continuousAt

omit ha hb hc in
/-- A uniform neighborhood where the existing minimal-segment construction applies. -/
def shortRadius (F : ReversibleMetric n) : ℝ :=
  (SegmentContinuity.exists_segment_path F).choose

omit ha hb hc in
theorem shortRadius_pos (F : ReversibleMetric n) : 0 < shortRadius F :=
  (SegmentContinuity.exists_segment_path F).choose_spec.1

omit ha hb hc in
/-- The actual minimal H¹ segment chosen from the existing geometric construction. -/
def shortPath (F : ReversibleMetric n) : Sphere n → Sphere n → Space n :=
  (SegmentContinuity.exists_segment_path F).choose_spec.2.choose

omit ha hb hc in
private theorem shortPath_spec (F : ReversibleMetric n) (P Q : Sphere n)
    (h : ‖(Q : Ambient n) - P‖ < shortRadius F) :
    shortPath F P Q ∈ pathsBetween n P Q ∧
      pathEnergy F (shortPath F P Q) = minEnergy F P Q :=
  (SegmentContinuity.exists_segment_path F).choose_spec.2.choose_spec.1 P Q h

omit ha hb hc in
private theorem shortPath_continuousAt (F : ReversibleMetric n) (P Q : Sphere n)
    (h : ‖(Q : Ambient n) - P‖ < shortRadius F) :
    ContinuousAt (fun z : Sphere n × Sphere n => shortPath F z.1 z.2) (P, Q) :=
  (SegmentContinuity.exists_segment_path F).choose_spec.2.choose_spec.2 P Q h

omit ha hb hc in
/-- The chosen minimal connector at equal endpoints is the actual constant
H¹ path, not just a path with the same energy. -/
theorem shortPath_self (F : ReversibleMetric n) (P : Sphere n) :
    shortPath F P P = constantData (P : Ambient n) := by
  have hs := shortPath_spec F P P (by simpa using shortRadius_pos F)
  let u : SphereLoop n := {
    data := ⟨shortPath F P P, (mem_periodicSubmodule_iff _).mpr
      (hs.1.2.2.trans hs.1.2.1.symm)⟩
    sphere_constraint := fun t => hs.1.1 t t.property }
  have he : energy F u = 0 := hs.2.trans
    (minEnergy_self F (by simpa using P.property))
  have hu := sphereLoop_eq_constant_of_velocity_eq_zero u
    (velocity_eq_zero_of_energy_eq_zero F u he)
  have hp : sphereRepresentative u ⟨0, by norm_num⟩ = P := Subtype.ext hs.1.2.1
  rw [hp] at hu
  exact congrArg (fun v : SphereLoop n => (v.data : Space n)) hu

omit ha hb hc in
/-- Loop pairs whose basepoints admit the chosen short connector. -/
def NearPairs (F : ReversibleMetric n) :=
  {z : SphereLoop n × SphereLoop n // ‖basepoint z.2 - basepoint z.1‖ < shortRadius F}

instance (F : ReversibleMetric n) : TopologicalSpace (NearPairs F) := inferInstanceAs
  (TopologicalSpace {z : SphereLoop n × SphereLoop n //
    ‖basepoint z.2 - basepoint z.1‖ < shortRadius F})

omit ha hb hc in
/-- The connector is constructed from the two basepoints, not supplied as a hypothesis. -/
def shortData (F : ReversibleMetric n) (p : NearPairs F) : Data n :=
  ⟨(p.val.1, p.val.2, shortPath F (H1FiberBase.point p.val.1) (H1FiberBase.point p.val.2)),
    (shortPath_spec F (H1FiberBase.point p.val.1) (H1FiberBase.point p.val.2) p.property).1⟩

omit ha hb hc in
theorem continuous_shortData (F : ReversibleMetric n) : Continuous (shortData F) := by
  have hu : Continuous (fun p : NearPairs F => p.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hv : Continuous (fun p : NearPairs F => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hp := (H1FiberBase.continuous_point.comp hu).prodMk
    (H1FiberBase.continuous_point.comp hv)
  have hw : Continuous (fun p : NearPairs F =>
      shortPath F (H1FiberBase.point p.val.1) (H1FiberBase.point p.val.2)) :=
    continuous_iff_continuousAt.mpr fun p =>
      ContinuousAt.comp (f := fun p : NearPairs F =>
        (H1FiberBase.point p.val.1, H1FiberBase.point p.val.2))
        (g := fun z : Sphere n × Sphere n => shortPath F z.1 z.2)
        (shortPath_continuousAt F (H1FiberBase.point p.val.1) (H1FiberBase.point p.val.2) p.property)
        hp.continuousAt
  exact (hu.prodMk (hv.prodMk hw)).subtype_mk _

/-- A genuine continuous loop family with two independently varying nearby basepoints. -/
def shortLoop (F : ReversibleMetric n) : C(NearPairs F, SphereLoop n) :=
  ⟨fun p => loop ha hb hc (shortData F p),
    (continuous_loop ha hb hc).comp (continuous_shortData F)⟩

omit ha hb hc in
/-- The equal-basepoint locus of the enlarged two-basepoint domain. -/
def diagonalPairs (F : ReversibleMetric n) :
    C(H1JoinContinuity.composable n, NearPairs F) :=
by
  let f : H1JoinContinuity.composable n → NearPairs F := fun p =>
    ⟨p.val, by
      rw [p.property, sub_self, norm_zero]
      exact shortRadius_pos F⟩
  exact ⟨f, continuous_subtype_val.subtype_mk _⟩

omit ha hb hc in
theorem shortData_diagonal_path (F : ReversibleMetric n) (p : H1JoinContinuity.composable n) :
    (shortData F (diagonalPairs F p)).val.2.2 =
      constantData (H1FiberBase.point p.val.1 : Ambient n) := by
  have hp : H1FiberBase.point p.val.2 = H1FiberBase.point p.val.1 :=
    Subtype.ext p.property.symm
  change shortPath F (H1FiberBase.point p.val.1) (H1FiberBase.point p.val.2) = _
  rw [hp, shortPath_self]

/-- The underlying H¹ path of the connector family, retaining its three
actual concatenations. This identity is used to compare parametrizations. -/
theorem loop_data (p : Data n) :
    ((loop ha hb hc p).data : Space n) =
      SobolevConcat.concat
        (SobolevConcat.concat (p.val.1.data : Space n) p.val.2.2
          (div_pos ha (add_pos ha hc))
          ((div_lt_one (add_pos ha hc)).mpr (by linarith)))
        (SobolevConcat.concat (p.val.2.1.data : Space n) (reverseData p.val.2.2)
          (div_pos hb (add_pos hb hc))
          ((div_lt_one (add_pos hb hc)).mpr (by linarith)))
        (div_pos (add_pos ha hc) (add_pos (add_pos ha hc) (add_pos hb hc)))
        ((div_lt_one (add_pos (add_pos ha hc) (add_pos hb hc))).mpr (by linarith)) := rfl

theorem energy_shortLoop (F : ReversibleMetric n) (p : NearPairs F) :
    energy F (shortLoop ha hb hc F p) = (a + b + 2 * c) *
      (energy F p.val.1 / a + energy F p.val.2 / b +
        2 * minEnergy F (basepoint p.val.1) (basepoint p.val.2) / c) := by
  rw [show energy F (shortLoop ha hb hc F p) = energy F (loop ha hb hc (shortData F p)) from rfl,
    energy_loop]
  change (a + b + 2 * c) * (energy F p.val.1 / a + energy F p.val.2 / b +
    2 * pathEnergy F (shortPath F (H1FiberBase.point p.val.1) (H1FiberBase.point p.val.2)) / c) = _
  rw [(shortPath_spec F (H1FiberBase.point p.val.1) (H1FiberBase.point p.val.2) p.property).2]
  rfl

include hc in
/-- Any positive connector-energy budget is realized by shrinking a uniform
neighborhood of the diagonal; no geometric small-energy assumption is added. -/
theorem exists_small_connector_radius (F : ReversibleMetric n) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ shortRadius F ∧ ∀ p : NearPairs F,
      ‖basepoint p.val.2 - basepoint p.val.1‖ < ρ →
        pathEnergy F (shortData F p).val.2.2 < c ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_minEnergy_upper F
  let ρ := min 1 (min (shortRadius F) (c / (C + 1)))
  have hCp : 0 < C + 1 := by positivity
  refine ⟨ρ, lt_min zero_lt_one (lt_min (shortRadius_pos F) (div_pos hc hCp)),
    (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro p hp
  let d := ‖basepoint p.val.2 - basepoint p.val.1‖
  have hd0 : 0 ≤ d := norm_nonneg _
  have hd1 : d ≤ 1 := hp.le.trans (min_le_left _ _)
  have hd : d < c / (C + 1) := hp.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hdc : (C + 1) * d < c := by
    have h := (lt_div_iff₀ hCp).mp hd
    nlinarith
  change pathEnergy F (shortPath F (H1FiberBase.point p.val.1) (H1FiberBase.point p.val.2)) < _
  rw [(shortPath_spec F (H1FiberBase.point p.val.1) (H1FiberBase.point p.val.2) p.property).2]
  calc
    _ ≤ C * d ^ 2 := (hbound _ _ (p.val.1.sphere_constraint 0)
      (p.val.2.sphere_constraint 0) hd1).2
    _ ≤ ((C + 1) * d) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg C]) (sq_nonneg d)
    _ < c ^ 2 := by nlinarith [mul_nonneg hCp.le hd0]

/-- A normalized energy deficit in either group pays for the two connectors. -/
theorem energy_loop_le (F : ReversibleMetric n) (p : Data n) {L D : ℝ}
    (hgroups : energy F p.val.1 / a + energy F p.val.2.1 / b ≤ (a + b) * L - D)
    (hpath : pathEnergy F p.val.2.2 ≤ c ^ 2) :
    energy F (loop ha hb hc p) ≤ (a + b + 2 * c) * ((a + b) * L - D + 2 * c) := by
  rw [energy_loop]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hw : 2 * pathEnergy F p.val.2.2 / c ≤ 2 * c := by
    apply (div_le_iff₀ hc).mpr
    nlinarith
  linarith

omit ha hb hc in
/-- The connector overhead after division by the total number of loop blocks. -/
def overhead (L c : ℝ) : ℝ := 2 * c * (1 + L + 2 * c)

omit ha hb hc in
private theorem budget_bound {k L c D : ℝ} (hk : 1 ≤ k) (hc : 0 ≤ c) (hD : 0 ≤ D) :
    (k + 2 * c) * (k * L - D + 2 * c) ≤ k ^ 2 * L + k * (overhead L c - D) := by
  have h := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg (2 * c))
  have h' := mul_nonneg hc hD
  dsimp [overhead]
  nlinarith

/-- Strict boundary control follows from a deficit exceeding the connector
overhead. The comparison is uniform in the number of loop blocks. -/
theorem energy_loop_lt (F : ReversibleMetric n) (p : Data n) {L D : ℝ}
    (hk : 1 ≤ a + b) (hD : 0 ≤ D) (hgap : overhead L c < D)
    (hgroups : energy F p.val.1 / a + energy F p.val.2.1 / b ≤ (a + b) * L - D)
    (hpath : pathEnergy F p.val.2.2 ≤ c ^ 2) :
    energy F (loop ha hb hc p) < (a + b) ^ 2 * L := by
  have h := (energy_loop_le ha hb hc F p hgroups hpath).trans (budget_bound hk hc.le hD)
  have hn := mul_neg_of_pos_of_neg (add_pos ha hb) (sub_neg.mpr hgap)
  linarith

/-- The enlarged family stays within an arbitrarily small additive length
cut once the connector overhead is sufficiently small. -/
theorem loop_mem_lev (F : ReversibleMetric n) (p : Data n) {l ε : ℝ}
    (hl : 0 < l) (hε : 0 < ε) (hk : 1 ≤ a + b)
    (hgap : overhead (l ^ 2) c < 2 * l * ε)
    (hgroups : energy F p.val.1 / a + energy F p.val.2.1 / b ≤ (a + b) * l ^ 2)
    (hpath : pathEnergy F p.val.2.2 ≤ c ^ 2) :
    loop ha hb hc p ∈ BorelLoop.lev F ((a + b) * l + ε) := by
  apply (Birkhoff.mem_lev_iff (add_pos (mul_pos (add_pos ha hb) hl) hε) _).mpr
  have h := (energy_loop_le ha hb hc F p (D := 0) (by simpa using hgroups) hpath).trans
    (budget_bound hk hc.le (le_refl 0))
  have hs := mul_lt_mul_of_pos_left hgap (add_pos ha hb)
  nlinarith [sq_nonneg ε]

omit ha hb hc in
/-- The overhead can be made smaller than any prescribed positive number. -/
theorem exists_small_overhead {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ overhead L c < ε := by
  let c := min (1 / 4 : ℝ) (ε / (4 * (L + 2)))
  have hp : 0 < 4 * (L + 2) := by positivity
  have hc : 0 < c := lt_min (by norm_num) (div_pos hε hp)
  have hc1 : c ≤ 1 / 4 := min_le_left _ _
  have hc2 : c ≤ ε / (4 * (L + 2)) := min_le_right _ _
  have hb := (le_div_iff₀ hp).mp hc2
  refine ⟨c, hc, ?_⟩
  have hh : overhead L c ≤ 2 * c * (L + 2) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

omit ha hb hc in
/-- Choose the connector duration and the geometric neighborhood before the
block counts, simultaneously meeting the boundary and upper-cut budgets. -/
theorem exists_uniform_budget (F : ReversibleMetric n) {l δ ε : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ ≤ shortRadius F ∧
      overhead (l ^ 2) c < δ ∧ overhead (l ^ 2) c < 2 * l * ε ∧
      ∀ p : NearPairs F, ‖basepoint p.val.2 - basepoint p.val.1‖ < ρ →
        pathEnergy F (shortData F p).val.2.2 < c ^ 2 := by
  obtain ⟨c, hc, hcost⟩ := exists_small_overhead (sq_nonneg l)
    (lt_min hδ (by positivity : 0 < 2 * l * ε))
  obtain ⟨ρ, hρ, hr, hpath⟩ := exists_small_connector_radius hc F
  exact ⟨c, ρ, hc, hρ, hr, hcost.trans_le (min_le_left _ _),
    hcost.trans_le (min_le_right _ _), hpath⟩

section Blocks

open HingstonBlocks

omit ha hb hc in
/-- Two independently based groups of actual loops with nearby basepoints. -/
def NearBlocks (F : ReversibleMetric n) (r s : ℕ) :=
  {z : Blocks n r × Blocks n s //
    ‖basepoint (z.2.val 0) - basepoint (z.1.val 0)‖ < shortRadius F}

instance (F : ReversibleMetric n) (r s : ℕ) : TopologicalSpace (NearBlocks F r s) :=
  inferInstanceAs (TopologicalSpace {z : Blocks n r × Blocks n s //
    ‖basepoint (z.2.val 0) - basepoint (z.1.val 0)‖ < shortRadius F})

omit ha hb hc in
/-- Collapse each group by the proved repeated-block construction, retaining
the two different basepoints. -/
def blockPair (F : ReversibleMetric n) (r s : ℕ) : C(NearBlocks F r s, NearPairs F) := by
  have hnear (z : NearBlocks F r s) :
      ‖basepoint (HingstonBlocks.concat z.val.2) - basepoint (HingstonBlocks.concat z.val.1)‖ <
        shortRadius F := by
    rw [basepoint_concat, basepoint_concat]
    exact z.property
  refine ⟨fun z => ⟨(HingstonBlocks.concat z.val.1, HingstonBlocks.concat z.val.2), hnear z⟩, ?_⟩
  have hfirst : Continuous (fun z : NearBlocks F r s => HingstonBlocks.concat z.val.1) :=
    (HingstonBlocks.continuous_concat n r).comp (continuous_fst.comp continuous_subtype_val)
  have hsecond : Continuous (fun z : NearBlocks F r s => HingstonBlocks.concat z.val.2) :=
    (HingstonBlocks.continuous_concat n s).comp (continuous_snd.comp continuous_subtype_val)
  exact (hfirst.prodMk hsecond).subtype_mk _

omit ha hb in
/-- The enlarged repeated-loop family, using actual shortest connectors.
Its two group durations are their respective numbers of blocks. -/
def blockLoop (F : ReversibleMetric n) (r s : ℕ) : C(NearBlocks F r s, SphereLoop n) :=
  (shortLoop (by positivity : 0 < (r : ℝ) + 1) (by positivity : 0 < (s : ℝ) + 1) hc F).comp
    (blockPair F r s)

omit ha hb in
theorem energy_blockLoop (F : ReversibleMetric n) {r s : ℕ} (z : NearBlocks F r s) :
    energy F (blockLoop hc F r s z) = ((r : ℝ) + 1 + ((s : ℝ) + 1) + 2 * c) *
      ((∑ i, energy F (z.val.1.val i)) + (∑ i, energy F (z.val.2.val i)) +
        2 * minEnergy F (basepoint (z.val.1.val 0)) (basepoint (z.val.2.val 0)) / c) := by
  change energy F (shortLoop _ _ hc F (blockPair F r s z)) = _
  rw [energy_shortLoop]
  change ((r : ℝ) + 1 + ((s : ℝ) + 1) + 2 * c) *
    (energy F (HingstonBlocks.concat z.val.1) / ((r : ℝ) + 1) +
      energy F (HingstonBlocks.concat z.val.2) / ((s : ℝ) + 1) +
      2 * minEnergy F (basepoint (HingstonBlocks.concat z.val.1))
        (basepoint (HingstonBlocks.concat z.val.2)) / c) = _
  rw [energy_concat, energy_concat, basepoint_concat, basepoint_concat]
  have hr : (r : ℝ) + 1 ≠ 0 := by positivity
  have hs : (s : ℝ) + 1 ≠ 0 := by positivity
  field_simp

omit ha hb in
/-- A single deficient loop block is enough to keep the connected family
strictly below the repeated critical energy, provided it pays the overhead. -/
theorem blockLoop_boundary_lt (F : ReversibleMetric n) {r s : ℕ} (z : NearBlocks F r s)
    {L δ : ℝ} (hδ : 0 ≤ δ) (hgap : overhead L c < δ)
    (hu : ∀ i, energy F (z.val.1.val i) ≤ L)
    (hv : ∀ i, energy F (z.val.2.val i) ≤ L)
    (hface : (∃ i, energy F (z.val.1.val i) ≤ L - δ) ∨
      (∃ i, energy F (z.val.2.val i) ≤ L - δ))
    (hpath : pathEnergy F (shortData F (blockPair F r s z)).val.2.2 ≤ c ^ 2) :
    energy F (blockLoop hc F r s z) < ((r : ℝ) + 1 + ((s : ℝ) + 1)) ^ 2 * L := by
  have hr : 0 < (r : ℝ) + 1 := by positivity
  have hs : 0 < (s : ℝ) + 1 := by positivity
  apply energy_loop_lt hr hs hc F (shortData F (blockPair F r s z))
    (by have := Nat.cast_nonneg (α := ℝ) r; have := Nat.cast_nonneg (α := ℝ) s; linarith)
    hδ hgap _ hpath
  change energy F (HingstonBlocks.concat z.val.1) / ((r : ℝ) + 1) +
    energy F (HingstonBlocks.concat z.val.2) / ((s : ℝ) + 1) ≤ _
  have hu' : energy F (HingstonBlocks.concat z.val.1) / ((r : ℝ) + 1) ≤
      ((r : ℝ) + 1) * L := (div_le_iff₀ hr).mpr (by
    nlinarith [energy_concat_le F z.val.1 hu])
  have hv' : energy F (HingstonBlocks.concat z.val.2) / ((s : ℝ) + 1) ≤
      ((s : ℝ) + 1) * L := (div_le_iff₀ hs).mpr (by
    nlinarith [energy_concat_le F z.val.2 hv])
  rcases hface with ⟨j, hj⟩ | ⟨j, hj⟩
  · have h : energy F (HingstonBlocks.concat z.val.1) / ((r : ℝ) + 1) ≤
        ((r : ℝ) + 1) * L - δ := (div_le_iff₀ hr).mpr (by
      nlinarith [energy_concat_deficit F z.val.1 j hu hj])
    nlinarith
  · have h : energy F (HingstonBlocks.concat z.val.2) / ((s : ℝ) + 1) ≤
        ((s : ℝ) + 1) * L - δ := (div_le_iff₀ hs).mpr (by
      nlinarith [energy_concat_deficit F z.val.2 j hv hj])
    nlinarith

omit ha hb in
/-- The whole connected block family lies in the prescribed additive length cut. -/
theorem blockLoop_mem_lev (F : ReversibleMetric n) {r s : ℕ} (z : NearBlocks F r s)
    {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε)
    (hgap : overhead (l ^ 2) c < 2 * l * ε)
    (hu : ∀ i, energy F (z.val.1.val i) ≤ l ^ 2)
    (hv : ∀ i, energy F (z.val.2.val i) ≤ l ^ 2)
    (hpath : pathEnergy F (shortData F (blockPair F r s z)).val.2.2 ≤ c ^ 2) :
    blockLoop hc F r s z ∈ BorelLoop.lev F ((((r : ℝ) + 1) + ((s : ℝ) + 1)) * l + ε) := by
  have hr : 0 < (r : ℝ) + 1 := by positivity
  have hs : 0 < (s : ℝ) + 1 := by positivity
  apply loop_mem_lev hr hs hc F (shortData F (blockPair F r s z)) hl hε
    (by have := Nat.cast_nonneg (α := ℝ) r; have := Nat.cast_nonneg (α := ℝ) s; linarith)
    hgap _ hpath
  change energy F (HingstonBlocks.concat z.val.1) / ((r : ℝ) + 1) +
    energy F (HingstonBlocks.concat z.val.2) / ((s : ℝ) + 1) ≤ _
  have hu' : energy F (HingstonBlocks.concat z.val.1) / ((r : ℝ) + 1) ≤
      ((r : ℝ) + 1) * l ^ 2 := (div_le_iff₀ hr).mpr (by
    nlinarith [energy_concat_le F z.val.1 hu])
  have hv' : energy F (HingstonBlocks.concat z.val.2) / ((s : ℝ) + 1) ≤
      ((s : ℝ) + 1) * l ^ 2 := (div_le_iff₀ hs).mpr (by
    nlinarith [energy_concat_le F z.val.2 hv])
  nlinarith

omit ha hb in
/-- If every block in either group loses δ, that group's size amplifies the
deficit. This is the estimate for the faces of the two base-parameter disks. -/
theorem blockLoop_base_boundary_lt (F : ReversibleMetric n) {r s : ℕ} (z : NearBlocks F r s)
    {L δ : ℝ} (hδ : 0 ≤ δ)
    (hrgap : overhead L c < ((r : ℝ) + 1) * δ)
    (hsgap : overhead L c < ((s : ℝ) + 1) * δ)
    (hu : ∀ i, energy F (z.val.1.val i) ≤ L)
    (hv : ∀ i, energy F (z.val.2.val i) ≤ L)
    (hface : (∀ i, energy F (z.val.1.val i) ≤ L - δ) ∨
      (∀ i, energy F (z.val.2.val i) ≤ L - δ))
    (hpath : pathEnergy F (shortData F (blockPair F r s z)).val.2.2 ≤ c ^ 2) :
    energy F (blockLoop hc F r s z) < ((r : ℝ) + 1 + ((s : ℝ) + 1)) ^ 2 * L := by
  have hr : 0 < (r : ℝ) + 1 := by positivity
  have hs : 0 < (s : ℝ) + 1 := by positivity
  have hk : 1 ≤ (r : ℝ) + 1 + ((s : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) r
    have := Nat.cast_nonneg (α := ℝ) s
    linarith
  have hnorm {t : ℕ} (u : Blocks n t) {B : ℝ}
      (h : ∀ i, energy F (u.val i) ≤ B) :
      energy F (HingstonBlocks.concat u) / ((t : ℝ) + 1) ≤ ((t : ℝ) + 1) * B :=
    (div_le_iff₀ (by positivity : 0 < (t : ℝ) + 1)).mpr (by
      nlinarith [energy_concat_le F u h])
  rcases hface with hleft | hright
  · apply energy_loop_lt hr hs hc F (shortData F (blockPair F r s z))
      hk (mul_nonneg hr.le hδ) hrgap _ hpath
    change energy F (HingstonBlocks.concat z.val.1) / ((r : ℝ) + 1) +
      energy F (HingstonBlocks.concat z.val.2) / ((s : ℝ) + 1) ≤ _
    nlinarith [hnorm z.val.1 hleft, hnorm z.val.2 hv]
  · apply energy_loop_lt hr hs hc F (shortData F (blockPair F r s z))
      hk (mul_nonneg hs.le hδ) hsgap _ hpath
    change energy F (HingstonBlocks.concat z.val.1) / ((r : ℝ) + 1) +
      energy F (HingstonBlocks.concat z.val.2) / ((s : ℝ) + 1) ≤ _
    nlinarith [hnorm z.val.1 hu, hnorm z.val.2 hright]

omit ha hb hc in
/-- A fixed positive base-boundary deficit eventually exceeds the connector
overhead. The bound is chosen before either group of blocks. -/
theorem exists_base_boundary_threshold {L c δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → overhead L c < ((r : ℝ) + 1) * δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (overhead L c / δ)
  refine ⟨N, fun r hr => ?_⟩
  have hNr : (N : ℝ) ≤ r := Nat.cast_le.mpr hr
  have h : overhead L c / δ < (r : ℝ) + 1 := by linarith
  exact (div_lt_iff₀ hδ).mp h

end Blocks

end
end Finsler.HingstonConnectors
