module

public import Finsler.Topology.BirkhoffNear
public import Finsler.Topology.BorelK

/-! Shortenings commuting with the half rotation. The straightening on the staggered grid of a
polygon model with N vertices commutes with the rotations by k/N. For an even number of vertices
the half rotation is such a rotation, so the curve shortening map of the model commutes with the
half rotation, and so does its restriction to a smaller sublevel. The descent and the uniform
localization of the curve shortening map hold with shortenings commuting with the half rotation:
the proofs for a given model do not depend on the number of vertices, which can be chosen
even. -/

@[expose] public section

namespace Finsler.ShorteningK

open Set
open Finsler.BorelLoop Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevCurveVariation Finsler.PolygonModel
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSampling Finsler.BorelK
open Finsler.BirkhoffDescent Finsler.BirkhoffLocalize Finsler.BirkhoffNear

noncomputable section

variable {n : ℕ}

local notation "Circ" => Finsler.SobolevCircleRepresentative.Circle

/-- A shortening commutes with the half rotation. -/
def HalfComm {F : ReversibleMetric n} {b : ℝ} (S : Shortening.Data F b) : Prop :=
  ∀ x : lev F b, (S.D ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ : Loops n) =
    half +ᵥ (S.D x : SphereLoop n)

section Model

variable {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N] (M : PolygonModelData F a N)

/-- Straightening on the staggered grid commutes with the rotation by k/N. -/
theorem stag_rotate_nat (k : ℕ) (τ : ℝ) (u : SphereLoop n) :
    Birkhoff.stag M τ (((((k : ℕ) : ℝ) / N : ℝ) : Circ) +ᵥ u) =
      ((((k : ℕ) : ℝ) / N : ℝ) : Circ) +ᵥ Birkhoff.stag M τ u := by
  have e1 : (((1 / (2 * N) : ℝ)) : Circ) +ᵥ (((((k : ℕ) : ℝ) / N : ℝ) : Circ) +ᵥ u) =
      ((((k : ℕ) : ℝ) / N : ℝ) : Circ) +ᵥ ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ u) := by
    rw [vadd_vadd, vadd_vadd, add_comm]
  have h := deform_rotate_nat M k (τ, (((1 / (2 * N) : ℝ)) : Circ) +ᵥ u)
  have e2 : deform M (τ, ((((k : ℕ) : ℝ) / N : ℝ) : Circ) +ᵥ ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ u)) =
      ((((k : ℕ) : ℝ) / N : ℝ) : Circ) +ᵥ deform M (τ, (((1 / (2 * N) : ℝ)) : Circ) +ᵥ u) := h
  unfold Birkhoff.stag
  rw [e1, e2, vadd_vadd, vadd_vadd, add_comm]

end Model

/-- The half rotation is the rotation by N₁/(2N₁). -/
theorem half_eq (N₁ : ℕ) [NeZero N₁] :
    half = ((((N₁ : ℕ) : ℝ) / ((2 * N₁ : ℕ) : ℝ) : ℝ) : Circ) := by
  have h : ((N₁ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N₁)
  have e : (1 / 2 : ℝ) = ((N₁ : ℕ) : ℝ) / ((2 * N₁ : ℕ) : ℝ) := by
    push_cast
    field_simp
  exact congrArg (fun x : ℝ => (x : Circ)) e

/-- The curve shortening map of a polygon model with an even number of vertices commutes with
the half rotation. -/
theorem halfComm_shortening {F : ReversibleMetric n} {a : ℝ} (N₁ : ℕ) [NeZero N₁]
    (M : PolygonModelData F a (2 * N₁)) (ha : 0 < a) : HalfComm (Birkhoff.shortening M ha) := by
  intro x
  have h := deform_rotate_nat M N₁ ((1 : ℝ), (x : SphereLoop n))
  have e : deform M (1, ((((N₁ : ℕ) : ℝ) / ((2 * N₁ : ℕ) : ℝ) : ℝ) : Circ) +ᵥ
      (x : SphereLoop n)) =
      ((((N₁ : ℕ) : ℝ) / ((2 * N₁ : ℕ) : ℝ) : ℝ) : Circ) +ᵥ deform M (1, (x : SphereLoop n)) := h
  change Birkhoff.stag M 1 (deform M (1, half +ᵥ (x : SphereLoop n))) =
    half +ᵥ Birkhoff.stag M 1 (deform M (1, (x : SphereLoop n)))
  rw [half_eq N₁, e, stag_rotate_nat]

/-- The restriction of a shortening commuting with the half rotation commutes with it. -/
theorem halfComm_restrict {F : ReversibleMetric n} {b b₁ : ℝ} (S : Shortening.Data F b₁)
    (hb : b ≤ b₁) (h : HalfComm S) : HalfComm (restrict S hb) := by
  intro x
  exact h (Set.inclusion (lev_mono F hb) x)

/-- Descent with a shortening commuting with the half rotation. -/
theorem exists_descent_half (F : ReversibleMetric n) (hn : 1 ≤ n) {a₀ a' b : ℝ} (ha₀ : 0 < a₀)
    (h1 : a₀ ≤ a') (h2 : a' ≤ b)
    (hreg : ∀ u : SphereLoop n, TangentCritical F u → a₀ ^ 2 ≤ energy F u →
      energy F u ≤ a' ^ 2 → False) :
    ∃ (S : Shortening.Data F b) (k : ℕ), HalfComm S ∧ ∀ x : lev F b,
      (x : Loops n) ∈ lev F a' → (Shortening.iter S k x : Loops n) ∈ lev F a₀ := by
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S₀.δ) (a := b + 1) S₀.pos
  obtain ⟨N₁, hN₁⟩ := exists_edge_bound F hn a' (S₀.δ / 2) (half_pos S₀.pos)
  have hb1 : 0 < b + 1 := by linarith
  have hN0 : N₀ ≤ 2 * (max N₀ N₁ + 1) := by
    have := le_max_left N₀ N₁
    omega
  have hN1 : N₁ ≤ 2 * (max N₀ N₁ + 1) := by
    have := le_max_right N₀ N₁
    omega
  let M : PolygonModelData F (b + 1) (2 * (max N₀ N₁ + 1)) :=
    PolygonModelData.mk S₀ fun u hu s t hs ht hst =>
      hN₀ (2 * (max N₀ N₁ + 1)) hN0 (by omega) u hu s t hs ht hst
  obtain ⟨k, hk⟩ := descent_of_model M hb1 hn ha₀ h1 (by linarith : a' < b + 1)
    (fun q hq i => hN₁ (2 * (max N₀ N₁ + 1)) hN1 q hq i) hreg
  refine ⟨restrict (Birkhoff.shortening M hb1) (by linarith : b ≤ b + 1), k,
    halfComm_restrict _ _ (halfComm_shortening (max N₀ N₁ + 1) M hb1), fun x hx => ?_⟩
  rw [iter_restrict]
  exact hk _ hx

/-- A polygon model of level c + 2 with an even number of vertices, enough for the edge bound at
level c + 1 and for the Hölder modulus ρ/3. -/
theorem exists_near_model_even (F : ReversibleMetric n) (hn : 1 ≤ n) {c ρ R : ℝ}
    (hρ0 : 0 < ρ) (hR : 0 < R) :
    ∃ (N' : ℕ) (M : PolygonModelData F (c + 2) (2 * (N' + 1))),
      (∀ q : ZMod (2 * (N' + 1)) → Sphere n,
        polyEnergy F (2 * (N' + 1)) (fun i => (q i : Ambient n)) ≤ (c + 1) ^ 2 →
        ∀ i : ZMod (2 * (N' + 1)), ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2) ∧
      ∀ d : ℝ, d ≤ 1 / ((2 * (N' + 1) : ℕ) : ℝ) → Real.sqrt d * R ≤ ρ / 3 := by
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S₀.δ) (a := c + 2) S₀.pos
  obtain ⟨N₁, hN₁⟩ := exists_edge_bound F hn (c + 1) (S₀.δ / 2) (half_pos S₀.pos)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt ((3 * R / ρ) ^ 2)
  have hN0 : N₀ ≤ 2 * (max (max N₀ N₁) N₂ + 1) := by
    have := (le_max_left N₀ N₁).trans (le_max_left _ N₂)
    omega
  have hN1 : N₁ ≤ 2 * (max (max N₀ N₁) N₂ + 1) := by
    have := (le_max_right N₀ N₁).trans (le_max_left _ N₂)
    omega
  have hN2 : (N₂ : ℝ) ≤ ((2 * (max (max N₀ N₁) N₂ + 1) : ℕ) : ℝ) := by
    have : N₂ ≤ 2 * (max (max N₀ N₁) N₂ + 1) := by
      have := le_max_right (max N₀ N₁) N₂
      omega
    exact_mod_cast this
  refine ⟨max (max N₀ N₁) N₂, PolygonModelData.mk S₀ fun u hu s t hs ht hst =>
      hN₀ (2 * (max (max N₀ N₁) N₂ + 1)) hN0 (by omega) u hu s t hs ht hst, ?_, ?_⟩
  · exact fun q hq i => hN₁ (2 * (max (max N₀ N₁) N₂ + 1)) hN1 q hq i
  · exact fun d hd => sqrt_mul_le hR hρ0 (hN₂.trans_le hN2) hd

/-- Uniform localization with a shortening commuting with the half rotation. -/
theorem exists_near_half (F : ReversibleMetric n) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) {ρ : ℝ}
    (hρ0 : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a' b : ℝ, c - ε < a' → a' < c → c < b → b < c + ε →
      ∃ S : Shortening.Data F b, HalfComm S ∧ ∀ x : lev F b,
        a' < Real.sqrt (energy F (S.D x : SphereLoop n)) →
        ∃ γ : SphereLoop n, TangentCritical F γ ∧ energy F γ = c ^ 2 ∧
          ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
            ‖continuousRepresentative ((x : SphereLoop n).data : Space n) t -
              continuousRepresentative (γ.data : Space n) t‖ ≤ ρ := by
  obtain ⟨R, hR, hhold⟩ := exists_holder F (A := c + 1) (by linarith)
  obtain ⟨N', M, hedge, hmod⟩ := exists_near_model_even F hn (c := c) hρ0 hR
  obtain ⟨ε, hε0, hε1, hε2, hnear⟩ := near_of_model M hn hc hρ0 hhold hmod hedge
  have hB : 0 < c + 2 := by linarith
  refine ⟨ε, hε0, ?_⟩
  intro a' b ha1 ha2 hb1 hb2
  have hbB : b ≤ c + 2 := by linarith
  have ha'0 : 0 < a' := by linarith
  refine ⟨restrict (Birkhoff.shortening M hB) hbB,
    halfComm_restrict _ _ (halfComm_shortening (N' + 1) M hB), fun x hx => ?_⟩
  have hb0 : 0 < b := hc.trans hb1
  have hxb : energy F (x : SphereLoop n) < b ^ 2 := (Birkhoff.mem_lev_iff hb0 _).mp x.2
  have hbε : b ^ 2 < (c + ε) ^ 2 := pow_lt_pow_left₀ hb2 hb0.le two_ne_zero
  rw [restrict_shortening_D M hB hbB x] at hx
  have h1 : a' ^ 2 < energy F (Birkhoff.stag M 1 (deform M (1, (x : SphereLoop n)))) :=
    (Real.lt_sqrt ha'0.le).mp hx
  have h2 : (c - ε) ^ 2 < a' ^ 2 := pow_lt_pow_left₀ ha1 (by linarith) two_ne_zero
  exact hnear (x : SphereLoop n) (hxb.trans hbε) (h2.trans h1)

end

end Finsler.ShorteningK
