module

public import Finsler.Geometry.RootHalfParity
public import Finsler.Geometry.AmbientDescent
public import Finsler.Analysis.EquivariantField

/-! The actual ambient ODE preserves every rotation-fixed root when its field is equivariant. -/

@[expose] public section

namespace Finsler.RootFlowFixed

open Set Finsler.Geometry Finsler.SphereGeometry Finsler.AmbientSymmetry
open Finsler.AmbientDescent Finsler.EquivariantField Finsler.PolygonIterate
open Finsler.CircleHalfRotation Finsler.AmbientPenalty
open scoped NNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n N : ℕ} [NeZero N]
variable {V : (ZMod N → Ambient n) → ZMod N → Ambient n} {K : ℝ≥0}
variable (hL : LipschitzWith K V) (hV0 : ∀ Q : ZMod N → Ambient n, V Q ≠ 0 → ∀ i, Q i ≠ 0)

theorem flowOm_rot (a : ZMod N) (hrot : ∀ Q, V (rotA N a Q) = rotA N a (V Q))
    (t : ℝ) (Q : Om n N) :
    (flowOm hL hV0 t ⟨rotA N a Q.1, rotA_ne_zero N a Q.2⟩).1 =
      rotA N a (flowOm hL hV0 t Q).1 :=
  globalSolution_map V hL (rotA N a) hrot Q.1 (max t 0)

theorem descent_fixed {g : (ZMod N → Ambient n) → ℝ} {O : Set (ZMod N → Ambient n)}
    (hg : ∀ Q ∈ O, DifferentiableAt ℝ g Q) (hsupp : ∀ Q, V Q ≠ 0 → Q ∈ O)
    (hle : ∀ Q ∈ O, fderiv ℝ g Q (V Q) ≤ 0)
    (a : ZMod N) (hrot : ∀ Q, V (rotA N a Q) = rotA N a (V Q)) :
    ∀ t (Q : Om n N), 0 ≤ t → rotA N a Q.1 = Q.1 →
      rotA N a ((descentOf hL hV0 hg hsupp hle).flow t Q).1 =
        ((descentOf hL hV0 hg hsupp hle).flow t Q).1 := by
  intro t Q _ hQ
  have he := globalSolution_map V hL (rotA N a) hrot Q.1 (max t 0)
  rw [hQ] at he
  exact he.symm

omit [NeZero N] in
theorem fixed_even (m s L : ℕ) [NeZero s] [NeZero L] (hm : Even m) :
    {z : Om n (s * (2 * L)) | rotA (s * (2 * L))
      (red m (s * (2 * L)) (halfIndex m s L)) z.1 = z.1} = univ := by
  rw [Finsler.RootHalfParity.reduced_even m s L hm]
  ext z
  simp only [rotA_zero, mem_ofPred_eq, mem_univ]

omit [NeZero N] in
theorem fixed_odd (m s L : ℕ) [NeZero s] [NeZero L] (hm : Odd m) :
    {z : Om n (s * (2 * L)) | rotA (s * (2 * L))
      (red m (s * (2 * L)) (halfIndex m s L)) z.1 = z.1} =
    {z : Om n (s * (2 * L)) | rotA (s * (2 * L)) (s * L : ℕ) z.1 = z.1} := by
  rw [Finsler.RootHalfParity.reduced_odd m s L hm]

end

end Finsler.RootFlowFixed
