import HingstonConnectors
import Finsler.Analysis.H1RightPadding
import Finsler.Topology.VariableJoinContinuity
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# Removing the two diagonal connector pauses

For loops with a common basepoint, append a constant interval of duration `d`
to each loop and join the two resulting loops with durations `a+d` and `b+d`.
The construction is jointly continuous in the strong H¹ topology, including
`d = 0`. Shrinking `d` decreases the actual energy and preserves every positive
energy sublevel containing the starting loop.
-/

namespace Finsler.HingstonPause

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1LoopJoin Finsler.H1JoinContinuity
open Finsler.SobolevEnergy Finsler.H1FiberBase

noncomputable section
variable {n : ℕ} {a b c : ℝ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

abbrev Durations := {d : ℝ // 0 ≤ d}

private def fraction (ha : 0 < a) (d : Durations) : H1PaddingContinuity.Parameters :=
  ⟨d / (a + d), div_nonneg d.property (by linarith [d.property]),
    (div_lt_one (by linarith [d.property])).mpr (by linarith)⟩

private def pad (ha : 0 < a) (d : Durations) (u : SphereLoop n) : SphereLoop n :=
  H1RightPadding.padded (fraction ha d) (fraction ha d).property.1
    (fraction ha d).property.2 u

private theorem basepoint_pad (ha : 0 < a) (d : Durations) (u : SphereLoop n) :
    basepoint (pad ha d u) = basepoint u := by
  change continuousRepresentative ((pad ha d u).data : Space n) 0 = _
  have h := H1RightPadding.representative_padded (fraction ha d)
    (fraction ha d).property.1 (fraction ha d).property.2 u ⟨0, by norm_num⟩
  rw [H1RightPadding.reflected_time_left (fraction ha d).property.2
    (by linarith [(fraction ha d).property.2]), mul_zero] at h
  exact h

private def split (ha : 0 < a) (hb : 0 < b) (d : Durations) :
    VariableJoinContinuity.Splits :=
  ⟨(a + d) / (a + d + (b + d)),
    div_pos (by linarith [d.property]) (by linarith [d.property]),
    (div_lt_one (by linarith [d.property])).mpr (by linarith [d.property])⟩

private def paddedPair (ha : 0 < a) (hb : 0 < b) (d : Durations)
    (p : composable n) : composable n :=
  ⟨(pad ha d p.val.1, pad hb d p.val.2),
    (basepoint_pad ha d p.val.1).trans (p.property.trans (basepoint_pad hb d p.val.2).symm)⟩

/-- The actual two-loop family, with a pause of unnormalized duration `d`
after each loop. Durations zero are included. -/
def value (ha : 0 < a) (hb : 0 < b) (d : Durations) (p : composable n) : SphereLoop n :=
  VariableJoinContinuity.value (split ha hb d, paddedPair ha hb d p)

theorem basepoint_value (ha : 0 < a) (hb : 0 < b) (d : Durations) (p : composable n) :
    basepoint (value ha hb d p) = basepoint p.val.1 := by
  unfold value VariableJoinContinuity.value
  rw [basepoint_join]
  exact basepoint_pad ha d p.val.1

private theorem continuous_pad (ha : 0 < a) :
    Continuous (fun z : Durations × SphereLoop n => pad ha z.1 z.2) := by
  have hd : Continuous (fun z : Durations × SphereLoop n => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hf : Continuous (fun z : Durations × SphereLoop n => fraction ha z.1) :=
    (hd.div (continuous_const.add hd) (fun z => (by linarith [z.1.property] :
      (0 : ℝ) < a + z.1).ne')).subtype_mk _
  exact (H1RightPadding.continuous_padded (n := n)).comp (hf.prodMk continuous_snd)

/-- Strong H¹ continuity holds all the way to zero pause duration. -/
theorem continuous_value (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun z : Durations × composable n => value ha hb z.1 z.2) := by
  have hd : Continuous (fun z : Durations × composable n => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hs : Continuous (fun z : Durations × composable n => split ha hb z.1) :=
    ((continuous_const.add hd).div
      ((continuous_const.add hd).add (continuous_const.add hd))
      (fun z => (by linarith [z.1.property] : (0 : ℝ) < a + z.1 + (b + z.1)).ne')).subtype_mk _
  have hu : Continuous (fun z : Durations × composable n => z.2.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
  have hv : Continuous (fun z : Durations × composable n => z.2.val.2) :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
  have hp : Continuous (fun z : Durations × composable n => paddedPair ha hb z.1 z.2) :=
    (((continuous_pad ha).comp (continuous_fst.prodMk hu)).prodMk
      ((continuous_pad hb).comp (continuous_fst.prodMk hv))).subtype_mk _
  exact (VariableJoinContinuity.continuous_value (n := n)).comp (hs.prodMk hp)

theorem value_zero (ha : 0 < a) (hb : 0 < b) (p : composable n) :
    value ha hb ⟨0, le_rfl⟩ p =
      join (a / (a + b)) (div_pos ha (add_pos ha hb))
        ((div_lt_one (add_pos ha hb)).mpr (by linarith)) p.val.1 p.val.2 p.property := by
  simp [value, VariableJoinContinuity.value, split, paddedPair, pad, fraction,
    H1RightPadding.padded_zero]

private theorem energy_identity (A B : ℝ) (ha : 0 < a) (hb : 0 < b)
    {d : ℝ} (hd : 0 ≤ d) :
    (A / (1 - d / (a + d))) / ((a + d) / (a + d + (b + d))) +
      (B / (1 - d / (b + d))) / (1 - (a + d) / (a + d + (b + d))) =
      (a + b + 2 * d) * (A / a + B / b) := by
  have ha' : a + d ≠ 0 := (by linarith : 0 < a + d).ne'
  have hb' : b + d ≠ 0 := (by linarith : 0 < b + d).ne'
  have ht : a + d + (b + d) ≠ 0 := (by linarith : 0 < a + d + (b + d)).ne'
  have h1 : 1 - d / (a + d) = a / (a + d) := by field_simp; ring
  have h2 : 1 - d / (b + d) = b / (b + d) := by field_simp; ring
  have h3 : 1 - (a + d) / (a + d + (b + d)) =
      (b + d) / (a + d + (b + d)) := by field_simp; ring
  rw [h1, h2, h3]
  field_simp
  ring

/-- Removing pauses changes only the total-duration factor in the energy. -/
theorem energy_value (ha : 0 < a) (hb : 0 < b) (F : ReversibleMetric n)
    (d : Durations) (p : composable n) :
    energy F (value ha hb d p) =
      (a + b + 2 * (d : ℝ)) * (energy F p.val.1 / a + energy F p.val.2 / b) := by
  unfold value VariableJoinContinuity.value
  rw [energy_join]
  change energy F (pad ha d p.val.1) / (split ha hb d : ℝ) +
    energy F (pad hb d p.val.2) / (1 - (split ha hb d : ℝ)) = _
  unfold pad
  rw [H1RightPadding.energy_padded, H1RightPadding.energy_padded]
  exact energy_identity _ _ ha hb d.property

/-- Shortening the two pauses never increases the actual energy. -/
theorem energy_value_mono (ha : 0 < a) (hb : 0 < b) (F : ReversibleMetric n)
    (p : composable n) : Monotone (fun d : Durations => energy F (value ha hb d p)) := by
  intro d e hde
  change energy F (value ha hb d p) ≤ energy F (value ha hb e p)
  rw [energy_value, energy_value]
  apply mul_le_mul_of_nonneg_right
  · change (d : ℝ) ≤ (e : ℝ) at hde
    linarith
  · exact add_nonneg (div_nonneg (energy_nonneg F _) ha.le)
      (div_nonneg (energy_nonneg F _) hb.le)

private def duration (hc : 0 ≤ c) : C(_root_.unitInterval, Durations) :=
  ⟨fun t => ⟨(1 - (t : ℝ)) * c, mul_nonneg (sub_nonneg.mpr t.property.2) hc⟩,
    (((continuous_const.sub continuous_subtype_val).mul continuous_const)).subtype_mk _⟩

private def valueMap (ha : 0 < a) (hb : 0 < b) :
    C(Durations × composable n, SphereLoop n) :=
  ⟨fun z => value ha hb z.1 z.2, continuous_value ha hb⟩

private def fixedMap (ha : 0 < a) (hb : 0 < b) (d : Durations) :
    C(composable n, SphereLoop n) :=
  (valueMap (n := n) ha hb).comp
    ⟨fun p : composable n => (d, p), continuous_const.prodMk continuous_id⟩

/-- The pause-removal homotopy starts with two pauses of duration `c` and
ends with the weighted ordinary concatenation. -/
def homotopy (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) :
    (fixedMap (n := n) ha hb ⟨c, hc⟩).Homotopy
    (joinMap (a / (a + b)) (div_pos ha (add_pos ha hb))
      ((div_lt_one (add_pos ha hb)).mpr (by linarith))) where
  toFun z := value ha hb (duration hc z.1) z.2
  continuous_toFun := by
    let input : C(_root_.unitInterval × composable n, Durations × composable n) :=
      ⟨fun z => (duration hc z.1, z.2),
        (((duration hc).continuous.comp continuous_fst).prodMk continuous_snd)⟩
    exact ((valueMap (n := n) ha hb).comp input).continuous
  map_zero_left p := by simp [duration, fixedMap, valueMap]
  map_one_left p := by simpa [duration, joinMap] using value_zero ha hb p

theorem homotopy_energy_le (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (F : ReversibleMetric n) (t : _root_.unitInterval) (p : composable n) :
    energy F (homotopy ha hb hc (t, p)) ≤ energy F (value ha hb ⟨c, hc⟩ p) := by
  apply energy_value_mono ha hb F p
  change (1 - (t : ℝ)) * c ≤ c
  nlinarith [t.property.1]

/-- Every positive sublevel containing the start is preserved, including a
separate smaller cut used on the boundary of a parameter domain. -/
theorem homotopy_mem_lev (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (F : ReversibleMetric n) {l : ℝ} (hl : 0 < l) (t : _root_.unitInterval) (p : composable n)
    (hp : value ha hb ⟨c, hc⟩ p ∈ BorelLoop.lev F l) :
    homotopy ha hb hc (t, p) ∈ BorelLoop.lev F l := by
  apply (Birkhoff.mem_lev_iff hl _).mpr
  exact (homotopy_energy_le ha hb hc F t p).trans_lt ((Birkhoff.mem_lev_iff hl _).mp hp)

private theorem pad_positive (ha : 0 < a) (hc : 0 < c) (u : SphereLoop n) :
    pad ha ⟨c, hc.le⟩ u =
      join (a / (a + c)) (div_pos ha (add_pos ha hc))
        ((div_lt_one (add_pos ha hc)).mpr (by linarith))
        u (constantSphereLoop (point u)) (H1ConstantPadding.constant_matches u).symm := by
  apply H1RightPadding.padded_join_at
  · exact div_pos hc (add_pos ha hc)
  · change 1 - c / (a + c) = a / (a + c)
    field_simp
    ring

/-- Exact identification of the diagonal of the actual shortest-connector
family with the starting point of the pause-removal homotopy. -/
theorem shortLoop_diagonal_eq (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (F : ReversibleMetric n) (p : composable n) :
    HingstonConnectors.shortLoop ha hb hc F (HingstonConnectors.diagonalPairs F p) =
      value ha hb ⟨c, hc.le⟩ p := by
  have hp : point p.val.1 = point p.val.2 := Subtype.ext p.property
  have hr : SobolevReverse.reverseData (constantData (point p.val.1 : Ambient n)) =
      constantData (point p.val.2 : Ambient n) := by
    rw [hp]
    exact congrArg (fun u : SphereLoop n => (u.data : Space n))
      (SobolevReverse.reverseSphere_constant (point p.val.2))
  apply (sphereLoop_data_isometry n).injective
  change ((HingstonConnectors.loop ha hb hc
    (HingstonConnectors.shortData F (HingstonConnectors.diagonalPairs F p))).data : Space n) = _
  rw [HingstonConnectors.loop_data, HingstonConnectors.shortData_diagonal_path, hr]
  change _ = SobolevConcat.concat (a := (a + c) / (a + c + (b + c))) ((pad ha ⟨c, hc.le⟩ p.val.1).data : Space n)
    ((pad hb ⟨c, hc.le⟩ p.val.2).data : Space n)
    (split ha hb ⟨c, hc.le⟩).property.1 (split ha hb ⟨c, hc.le⟩).property.2
  have hu := congrArg (fun u : SphereLoop n => (u.data : Space n))
    (pad_positive ha hc p.val.1)
  have hv := congrArg (fun u : SphereLoop n => (u.data : Space n))
    (pad_positive hb hc p.val.2)
  exact congrArg₂ (fun U V : Space n => SobolevConcat.concat U V
    (split ha hb ⟨c, hc.le⟩).property.1 (split ha hb ⟨c, hc.le⟩).property.2) hu.symm hv.symm

/-- On the diagonal, the constructed connector loop is homotopic to the
ordinary weighted join, by an explicit H¹ homotopy. -/
def diagonalHomotopy (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (F : ReversibleMetric n) :
    ((HingstonConnectors.shortLoop ha hb hc F).comp
      (HingstonConnectors.diagonalPairs F)).Homotopy
    (joinMap (a / (a + b)) (div_pos ha (add_pos ha hb))
      ((div_lt_one (add_pos ha hb)).mpr (by linarith))) where
  toFun := homotopy ha hb hc.le
  continuous_toFun := (homotopy ha hb hc.le).continuous
  map_zero_left p := (homotopy ha hb hc.le).apply_zero p |>.trans
    (shortLoop_diagonal_eq ha hb hc F p).symm
  map_one_left p := (homotopy ha hb hc.le).apply_one p

theorem diagonalHomotopy_mem_lev (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (F : ReversibleMetric n) {l : ℝ} (hl : 0 < l)
    (t : _root_.unitInterval) (p : composable n)
    (hp : HingstonConnectors.shortLoop ha hb hc F (HingstonConnectors.diagonalPairs F p) ∈
      BorelLoop.lev F l) :
    diagonalHomotopy ha hb hc F (t, p) ∈ BorelLoop.lev F l := by
  rw [shortLoop_diagonal_eq ha hb hc F p] at hp
  exact homotopy_mem_lev ha hb hc.le F hl t p hp

/-- Two actual integer iterates, based at the original loop's basepoint. -/
def iteratePair (u : SphereLoop n) (k l : ℕ) (hk : k ≠ 0) (hl : l ≠ 0) : composable n :=
  ⟨(SobolevIteration.iterateSphere u k hk, SobolevIteration.iterateSphere u l hl),
    (HingstonBlocks.basepoint_iterate u k hk).trans (HingstonBlocks.basepoint_iterate u l hl).symm⟩

/-- At the repeated center, removing the actual connector pauses ends at
exactly the sum iterate, with no residual reparametrization. -/
theorem diagonalHomotopy_iterates_end (hc : 0 < c) (F : ReversibleMetric n)
    (u : SphereLoop n) (k l : ℕ) (hk : k ≠ 0) (hl : l ≠ 0) :
    diagonalHomotopy (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl)) hc F (1, iteratePair u k l hk hl) =
    SobolevIteration.iterateSphere u (k + l) (by omega) := by
  rw [ContinuousMap.Homotopy.apply_one]
  exact HingstonBlocks.join_iterates u k l hk hl

section Relative

open CategoryTheory

variable (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (F : ReversibleMetric n)
  {X : Type} [TopologicalSpace X] (φ : C(X, composable n)) {B : Set X}
  {l L : ℝ} (hl : 0 < l) (hL : 0 < L) (hlL : l ≤ L)
  (hφ : ∀ x, value ha hb ⟨c, hc⟩ (φ x) ∈ BorelLoop.lev F L)
  (hB : ∀ x ∈ B, value ha hb ⟨c, hc⟩ (φ x) ∈ BorelLoop.lev F l)

private theorem continuous_family :
    Continuous (fun z : _root_.unitInterval × X => homotopy ha hb hc (z.1, φ z.2)) := by
  let input : C(_root_.unitInterval × X, _root_.unitInterval × composable n) :=
    ⟨fun z => (z.1, φ z.2), continuous_fst.prodMk (φ.continuous.comp continuous_snd)⟩
  exact ((homotopy ha hb hc).toContinuousMap.comp input).continuous

/-- At each time the pause removal is a map of the actual parameter/boundary
pair into the prescribed upper/lower energy sublevels. -/
def familyPairMap (t : _root_.unitInterval) :
    TopPair.ofSubset (X := TopCat.of X) B ⟶
      BorelLoop.pairOf (BorelLoop.lev_mono F hlL) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun x => ⟨homotopy ha hb hc (t, φ x),
      homotopy_mem_lev ha hb hc F hL t (φ x) (hφ x)⟩,
      ((continuous_family ha hb hc φ).comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩)
    (TopCat.ofHom ⟨fun x : B => ⟨homotopy ha hb hc (t, φ x.val),
      homotopy_mem_lev ha hb hc F hl t (φ x.val) (hB x.val x.property)⟩,
      ((continuous_family ha hb hc φ).comp
        (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩)
    (by ext x; rfl)

/-- The two parameter maps are homotopic as maps of pairs: the lower cut
is preserved throughout, not only at the endpoints. -/
def pairHomotopy :
    TopPair.Homotopy (familyPairMap ha hb hc F φ hl hL hlL hφ hB 0)
      (familyPairMap ha hb hc F φ hl hL hlL hφ hB 1) where
  fst := {
    toFun z := ⟨homotopy ha hb hc (z.1, φ z.2),
      homotopy_mem_lev ha hb hc F hL z.1 (φ z.2) (hφ z.2)⟩
    continuous_toFun := (continuous_family ha hb hc φ).subtype_mk _
    map_zero_left _ := rfl
    map_one_left _ := rfl }
  snd := {
    toFun z := ⟨homotopy ha hb hc (z.1, φ z.2.val),
      homotopy_mem_lev ha hb hc F hl z.1 (φ z.2.val) (hB z.2.val z.2.property)⟩
    continuous_toFun := ((continuous_family ha hb hc φ).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left _ := rfl
    map_one_left _ := rfl }

/-- Pause removal induces exactly the same relative singular homology map
in every degree and over any field of coefficients. -/
theorem family_homology_eq (K : Type) [Field K] (q : ℕ) :
    TopPair.singularHomologyMap (familyPairMap ha hb hc F φ hl hL hlL hφ hB 0)
      (ModuleCat.of K K) q =
    TopPair.singularHomologyMap (familyPairMap ha hb hc F φ hl hL hlL hφ hB 1)
      (ModuleCat.of K K) q :=
  (pairHomotopy ha hb hc F φ hl hL hlL hφ hB).congr_singularHomologyMap (ModuleCat.of K K) q

theorem familyPairMap_zero (x : X) :
    (TopPair.Hom.fst (familyPairMap ha hb hc F φ hl hL hlL hφ hB 0) x).val =
      value ha hb ⟨c, hc⟩ (φ x) := (homotopy ha hb hc).apply_zero (φ x)

theorem familyPairMap_one (x : X) :
    (TopPair.Hom.fst (familyPairMap ha hb hc F φ hl hL hlL hφ hB 1) x).val =
      join (a / (a + b)) (div_pos ha (add_pos ha hb))
        ((div_lt_one (add_pos ha hb)).mpr (by linarith))
        (φ x).val.1 (φ x).val.2 (φ x).property := (homotopy ha hb hc).apply_one (φ x)

end Relative

end
end Finsler.HingstonPause
