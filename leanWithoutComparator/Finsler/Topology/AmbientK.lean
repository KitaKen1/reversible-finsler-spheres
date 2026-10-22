module

public import Finsler.Topology.RevLabel
public import Finsler.Topology.SampleK
public import Finsler.Geometry.AmbientSymmetry
public import Finsler.Analysis.EquivariantField

/-! The K-action on ambient polygons. On the ambient polygons with 2M nonzero vertices the
reversal of the vertices and the rotation by M vertices are two commuting continuous involutions
(a `KAct`), and the penalized polygon energy is invariant under both. The flow on the polygons
with nonzero vertices of a field commuting with the reversal and the rotation by M (as continuous
linear maps of the ambient space) commutes with both involutions; so the descents of the
penalized energy (and of deformations of it invariant under both) built from such fields are
equivariant, and the space-independent K-Borel lens machinery (`InvPairs`, `LensK`, `PolySplit`)
applies to them. -/

@[expose] public section

namespace Finsler.AmbientK

open Set Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.PolygonDescentK Finsler.AmbientDescent Finsler.InvPairs Finsler.RevLabel
open Finsler.EquivariantField Finsler.SampleK Finsler.FlowLens
open scoped NNReal

noncomputable section

variable {n : ℕ} (M : ℕ) [NeZero M]

/-- The reversal of the ambient polygons with nonzero vertices. -/
def revOmC : C(Om n (2 * M), Om n (2 * M)) :=
  ⟨fun Q => ⟨revA (2 * M) Q.1, revA_ne_zero Q.2⟩,
    ((revA (2 * M)).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The rotation by M of the ambient polygons with nonzero vertices. -/
def rotOmC : C(Om n (2 * M), Om n (2 * M)) :=
  ⟨fun Q => ⟨rotA (2 * M) (M : ZMod (2 * M)) Q.1, rotA_ne_zero (2 * M) _ Q.2⟩,
    ((rotA (2 * M) (M : ZMod (2 * M))).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The reversal and the rotation by M as two commuting involutions of the ambient polygons with
nonzero vertices. -/
def ambK : KAct (Om n (2 * M)) where
  ρ := revOmC M
  σ := rotOmC M
  ρρ Q := Subtype.ext (revA_revA _ Q.1)
  σσ Q := Subtype.ext (rotA_involutive (half_shift M) Q.1)
  ρσ Q := Subtype.ext (revA_rotA (half_shift M) Q.1)

/-- The penalized polygon energy is invariant under the reversal. -/
theorem pen_ρ (F : ReversibleMetric n) (lam : ℝ) (Q : Om n (2 * M)) :
    pen F (2 * M) lam ((ambK M).ρ Q).1 = pen F (2 * M) lam Q.1 :=
  pen_revA F lam Q.1

/-- The penalized polygon energy is invariant under the rotation by M. -/
theorem pen_σ (F : ReversibleMetric n) (lam : ℝ) (Q : Om n (2 * M)) :
    pen F (2 * M) lam ((ambK M).σ Q).1 = pen F (2 * M) lam Q.1 :=
  pen_rotA (2 * M) F lam _ Q.1

variable {M} {V : (ZMod (2 * M) → Ambient n) → ZMod (2 * M) → Ambient n} {K : ℝ≥0}
  (hL : LipschitzWith K V) (hV0 : ∀ P : ZMod (2 * M) → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)

include hL hV0 in
/-- The flow of a field commuting with the reversal commutes with the reversal. -/
theorem flowOm_ρ (hVr : ∀ y, V (revA (2 * M) y) = revA (2 * M) (V y)) (t : ℝ)
    (Q : Om n (2 * M)) :
    flowOm hL hV0 t ((ambK M).ρ Q) = (ambK M).ρ (flowOm hL hV0 t Q) := by
  apply Subtype.ext
  change ODE.globalSolution V hL (revA (2 * M) Q.1) (max t 0) =
    revA (2 * M) (ODE.globalSolution V hL Q.1 (max t 0))
  exact globalSolution_map V hL (revA (2 * M)) hVr Q.1 _

include hL hV0 in
/-- The flow of a field commuting with the rotation by M commutes with the rotation by M. -/
theorem flowOm_σ (hVh : ∀ y, V (rotA (2 * M) (M : ZMod (2 * M)) y) =
      rotA (2 * M) (M : ZMod (2 * M)) (V y)) (t : ℝ) (Q : Om n (2 * M)) :
    flowOm hL hV0 t ((ambK M).σ Q) = (ambK M).σ (flowOm hL hV0 t Q) := by
  apply Subtype.ext
  change ODE.globalSolution V hL (rotA (2 * M) (M : ZMod (2 * M)) Q.1) (max t 0) =
    rotA (2 * M) (M : ZMod (2 * M)) (ODE.globalSolution V hL Q.1 (max t 0))
  exact globalSolution_map V hL (rotA (2 * M) (M : ZMod (2 * M))) hVh Q.1 _

/-- **Equivariant descents of ambient polygons.** The descent of a function along a field
commuting with the reversal and the rotation by M commutes with both involutions. -/
theorem descentOf_equivariant {g : (ZMod (2 * M) → Ambient n) → ℝ}
    {O : Set (ZMod (2 * M) → Ambient n)} (hg : ∀ P ∈ O, DifferentiableAt ℝ g P)
    (hsupp : ∀ P, V P ≠ 0 → P ∈ O) (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0)
    (hVr : ∀ y, V (revA (2 * M) y) = revA (2 * M) (V y))
    (hVh : ∀ y, V (rotA (2 * M) (M : ZMod (2 * M)) y) = rotA (2 * M) (M : ZMod (2 * M)) (V y)) :
    (∀ t w, (descentOf hL hV0 hg hsupp hle).flow t ((ambK M).ρ w) =
      (ambK M).ρ ((descentOf hL hV0 hg hsupp hle).flow t w)) ∧
    (∀ t w, (descentOf hL hV0 hg hsupp hle).flow t ((ambK M).σ w) =
      (ambK M).σ ((descentOf hL hV0 hg hsupp hle).flow t w)) :=
  ⟨fun t w => flowOm_ρ hL hV0 hVr t w, fun t w => flowOm_σ hL hV0 hVh t w⟩

section Average

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r h : E →L[ℝ] E}

/-- **Averaging keeps equivariant label fields.** If a field V agrees on a set T invariant under
two commuting involutions r, h with a field W equivariant on T, the average of V over the group
generated by r and h agrees with W on T. -/
theorem avg_eq_of_equivariant (hr : ∀ x, r (r x) = x) (hh : ∀ x, h (h x) = x)
    (hrh : ∀ x, r (h x) = h (r x)) {V W : E → E} {T : Set E} (hTr : ∀ x ∈ T, r x ∈ T)
    (hTh : ∀ x ∈ T, h x ∈ T) (hVW : ∀ x ∈ T, V x = W x) (hWr : ∀ x ∈ T, W (r x) = r (W x))
    (hWh : ∀ x ∈ T, W (h x) = h (W x)) {x : E} (hx : x ∈ T) : avg r h V x = W x := by
  have h1 : r (V (r x)) = W x := by rw [hVW _ (hTr x hx), hWr x hx, hr]
  have h2 : h (V (h x)) = W x := by rw [hVW _ (hTh x hx), hWh x hx, hh]
  have h3 : r (h (V (r (h x)))) = W x := by
    rw [hVW _ (hTr _ (hTh x hx)), hWr _ (hTh x hx), hWh x hx, ← hrh, hr, hh]
  unfold avg
  rw [hVW x hx, h1, h2, h3]
  module

end Average

end

end Finsler.AmbientK
