module

public import Finsler.Geometry.CircleHalfRotation

/-! Closed negative and positive frames in the normal half-rotation eigenspaces along an actual even iterate circle, using the commuting prime-period holonomy. -/

@[expose] public section

namespace Finsler.CircleEigenFrames

open Set Module QuadraticForm QuadraticMap
open Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonDescent
open Finsler.PolygonIterate Finsler.AmbientSymmetry Finsler.AmbientNormalIndex
open Finsler.AmbientRotation Finsler.SymmetricBlocks Finsler.NormalFamily
open Finsler.GeodesicFrames Finsler.CircleFrameField Finsler.CircleHalfRotation
open Finsler.GeodesicNormalData Finsler.InvolutionIndex Finsler.DefiniteFrames
open scoped ContDiff

noncomputable section
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 600000

variable {n : ℕ} {F : ReversibleMetric n}

/-- The actual half-rotation endomorphism on the normal space. -/
def halfNormal (m s N : ℕ) : Module.End ℝ (normal (rotL (n := n) m (s * (2 * N))) m) :=
  (rotV m (s * (2 * N)) (halfIndex m s N)).toLinearMap

/-- Actual even-iterate negative frames in either eigenspace of the normal half-rotation.
The gcd condition gives nondegeneracy; the parity condition supplies holonomy without real
eigenvalues. No frame or holonomy is assumed as an additional input. -/
theorem exists_even_signed_eigen_frame (g : Finsler.Geodesics.ClosedGeodesic F)
    (s m : ℕ) [NeZero s] [NeZero m]
    (hgcd : Nat.gcd (s * m) (iterData g).L = Nat.gcd s (iterData g).L)
    (hpar : Even s ∨ Odd m) (heven : Even (m * s)) (ε : ℝ) (hε : ε ≠ 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N], ∀ e : ℝ, e * e = 1 →
      ∃ H : ℝ → Fin (sigNeg (LinearMap.BilinMap.toQuadraticMap
          (eigenForm (halfNormal (n := n) m s N) e
            (ε • formB m (s * (2 * N)) F (rootFamily g s N) 0)))) →
          (halfNormal (n := n) m s N).eigenspace e,
        Continuous H ∧ H 1 = H 0 ∧ ∀ a ∈ Icc (0 : ℝ) 1,
          Finsler.DefiniteFrames.Neg (eigenForm (halfNormal (n := n) m s N) e
            (ε • formB m (s * (2 * N)) F (rootFamily g s N) a)) (H a) := by
  obtain ⟨N₀, hN₀⟩ := exists_normal_families g s m hgcd
  refine ⟨N₀, fun N hN _ e he => ?_⟩
  obtain ⟨hsm, hB, -, hk⟩ := hN₀ N hN
  let T : Module.End ℝ (normal (rotL (n := n) m (s * (2 * N))) m) :=
    halfNormal m s N
  let R := rotV (n := n) m (s * (2 * N)) 1
  let B := fun a => ε • formB m (s * (2 * N)) F (rootFamily g s N) a
  have hkε : ∀ a, LinearMap.ker (B a) = ⊥ := by
    intro a
    rw [show B a = ε • formB m (s * (2 * N)) F (rootFamily g s N) a from rfl,
      LinearMap.ker_smul _ ε hε, hk a]
  have hsymε : ∀ a v w, B a v w = B a w v := by
    intro a v w
    change ε * formB m (s * (2 * N)) F (rootFamily g s N) a v w =
      ε * formB m (s * (2 * N)) F (rootFamily g s N) a w v
    rw [hB.symm a v w]
  have hTT : ∀ v, T (T v) = v := normal_half_involutive m s N
  have hinv : ∀ a v w, B a (T v) (T w) = B a v w := by
    intro a v w
    change ε * formB m (s * (2 * N)) F (rootFamily g s N) a (T v) (T w) =
      ε * formB m (s * (2 * N)) F (rootFamily g s N) a v w
    exact congrArg (fun x : ℝ => ε * x) (formB_half_even g m s N heven hsm a v w)
  have hcomm : ∀ v, T (R v) = R (T v) := by
    intro v
    change rotV m (s * (2 * N)) (halfIndex m s N) (rotV m (s * (2 * N)) 1 v) =
      rotV m (s * (2 * N)) 1 (rotV m (s * (2 * N)) (halfIndex m s N) v)
    rw [Finsler.RotationNatural.rotV_rotV, Finsler.RotationNatural.rotV_rotV]
    exact congrArg (fun a : ZMod (m * (s * (2 * N))) => rotV m (s * (2 * N)) a v)
      (add_comm _ _)
  have hsteps : ∀ j : ℕ, ∀ a v w,
      B (a + j * (1 / ((2 * N : ℕ) : ℝ))) ((R ^ j) v) ((R ^ j) w) = B a v w := by
    intro j a v w
    have hroot : amb (rootFamily g s N (a + j * (1 / ((2 * N : ℕ) : ℝ)))) =
        rotA (s * (2 * N)) (red m (s * (2 * N)) (j : ZMod (m * (s * (2 * N)))))
          (amb (rootFamily g s N a)) := by
      rw [rootFamily_add_steps, amb_rotP, red_natCast]
    have hR : ∀ v, (R ^ j) v = rotV m (s * (2 * N)) (j : ZMod (m * (s * (2 * N)))) v := by
      intro v
      apply Subtype.ext
      rw [rotV_pow_coe, rotV_coe, mul_one]
    change ε * normalForm m (s * (2 * N)) F
      (amb (rootFamily g s N (a + j * (1 / ((2 * N : ℕ) : ℝ))))) ((R ^ j) v) ((R ^ j) w) =
        ε * normalForm m (s * (2 * N)) F (amb (rootFamily g s N a)) v w
    apply congrArg (fun x : ℝ => ε * x)
    rw [hroot, hR v, hR w]
    apply normalForm_rot
    rw [← hroot]
    exact hsm _
  have hNpos : (0 : ℝ) < ((2 * N : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_neZero (2 * N)
  have hη : (0 : ℝ) < 1 / ((2 * N : ℕ) : ℝ) := div_pos one_pos hNpos
  have hone : ((2 * N : ℕ) : ℝ) * (1 / ((2 * N : ℕ) : ℝ)) = 1 := mul_one_div_cancel hNpos.ne'
  have hR : ∀ a v w, B (a + 1 / ((2 * N : ℕ) : ℝ)) (R v) (R w) = B a v w := by
    simpa only [Nat.cast_one, one_mul, pow_one] using hsteps 1
  have hper : ∀ v w, B 0 ((R ^ (2 * N)) v) ((R ^ (2 * N)) w) = B 0 v w := by
    intro v w
    have h := hsteps (2 * N) 0 v w
    rw [hone, zero_add] at h
    have hb : B 1 = B 0 := by
      apply congrArg (fun β => ε • β)
      apply formB_congr
      simpa only [zero_add] using rootFamily_add_one g s N 0
    rw [hb] at h
    exact h
  let γ := (vertexForm (n := n) (m * (s * (2 * N)))).compl₁₂
    (normal (rotL (n := n) m (s * (2 * N))) m).subtype
    (normal (rotL (n := n) m (s * (2 * N))) m).subtype
  have hγs : ∀ v w, γ v w = γ w v := fun v w => vertexForm_symm _ _ _
  have hγp : ∀ v, v ≠ 0 → 0 < γ v v := fun v hv =>
    vertexForm_pos _ fun hz => hv (Subtype.ext hz)
  have hγR : ∀ v w, γ ((R ^ (2 * N)) v) ((R ^ (2 * N)) w) = γ v w := by
    intro v w
    change vertexForm _ (((R ^ (2 * N)) v : normal (rotL m (s * (2 * N))) m) :
      ZMod (m * (s * (2 * N))) → Ambient n)
      (((R ^ (2 * N)) w : normal (rotL m (s * (2 * N))) m) :
        ZMod (m * (s * (2 * N))) → Ambient n) = _
    rw [rotV_pow_coe, rotV_pow_coe, vertexForm_rotA]
    rfl
  have hsa : (s : ZMod (m * (s * (2 * N)))) *
      (((2 * N : ℕ) : ZMod (m * (s * (2 * N)))) * 1) = (s * (2 * N) : ℕ) := by
    rw [mul_one, ← Nat.cast_mul]
  have heig : ∀ (μ : ℝ) (v : normal (rotL (n := n) m (s * (2 * N))) m),
      (R ^ (2 * N)) v = μ • v → v = 0 := by
    intro μ v hv
    have h := congrArg Subtype.val hv
    rw [rotV_pow_coe] at h
    exact Subtype.ext (eq_zero_of_eigen m (s * (2 * N)) hsa hpar v.2 h)
  have h := exists_eigen_closed_frame T hTT e he (continuous_const.smul hB.cont) hsymε hinv hkε R hcomm
    hη hR (Nat.pos_of_neZero N) hper γ hγs hγp hγR heig
  rw [hone] at h
  exact h


/-- Actual even-iterate negative frames in either eigenspace of the normal half-rotation.
The gcd condition gives nondegeneracy; the parity condition supplies holonomy without real
eigenvalues. No frame or holonomy is assumed as an additional input. -/
theorem exists_even_eigen_frame (g : Finsler.Geodesics.ClosedGeodesic F)
    (s m : ℕ) [NeZero s] [NeZero m]
    (hgcd : Nat.gcd (s * m) (iterData g).L = Nat.gcd s (iterData g).L)
    (hpar : Even s ∨ Odd m) (heven : Even (m * s)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N], ∀ e : ℝ, e * e = 1 →
      ∃ H : ℝ → Fin (sigNeg (LinearMap.BilinMap.toQuadraticMap
          (eigenForm (halfNormal (n := n) m s N) e
            (formB m (s * (2 * N)) F (rootFamily g s N) 0)))) →
          (halfNormal (n := n) m s N).eigenspace e,
        Continuous H ∧ H 1 = H 0 ∧ ∀ a ∈ Icc (0 : ℝ) 1,
          Finsler.DefiniteFrames.Neg (eigenForm (halfNormal (n := n) m s N) e
            (formB m (s * (2 * N)) F (rootFamily g s N) a)) (H a) := by
  obtain ⟨N₀, hN₀⟩ := exists_even_signed_eigen_frame g s m hgcd hpar heven 1 (by norm_num)
  refine ⟨N₀, fun N hN _ e he => ?_⟩
  have h := hN₀ N hN e he
  rw [one_smul] at h
  simpa only [one_smul] using h

end

end Finsler.CircleEigenFrames
