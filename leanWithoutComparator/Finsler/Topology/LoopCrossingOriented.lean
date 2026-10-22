module

public import Finsler.Topology.PolygonOriented
public import Finsler.Topology.PolygonLoopPairs
public import Finsler.Geometry.EnergyDiagonal

/-! The loop-space crossing pair of a critical level as a product of two polygon lens pairs.
Segment data stay valid for a smaller radius. Let F have finitely many prime closed geodesic
images and let c be the only critical level in [a₀, b₀], 0 < a₀ ≤ b₀. Then for all large N there
are disjoint open sets W₊, W₋ of the space of polygons with N vertices, a descending semiflow of
the polygon energy and d > 0 such that for all cuts a₀ ≤ a' < a ≤ b ≤ b₀ with b² − a'² < d and
every time T ≥ 1 the ordinary cohomology of the loop pair (t_b, t_a) is the product of the
cohomologies of the lens pairs of the polygon energy in W₊ and in W₋ for the cuts a², b². The
sets W₊ and W₋ consist of the short polygons whose broken geodesics are near the positive and
near the negative critical loops of level c. This combines the comparison of loop pairs with
polygon pairs by sampling and the decomposition of the polygon crossing pairs. -/

@[expose] public section

namespace Finsler.LoopCrossingOriented

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonModel
open Finsler.PolygonDescent Finsler.PolygonOriented Finsler.PolygonLoopPairs
open Finsler.CriticalLevels Finsler.OrientedCritical Finsler.FlowLens Finsler.LensContinuation
open Finsler.BorelCochain Finsler.BorelLoop Finsler.PairTriple Finsler.EnergyDiagonal
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} {F : ReversibleMetric n}

/-- Segment data for a smaller radius. -/
def shrink (S : SegmentData F) {δ' : ℝ} (hδ' : 0 < δ') (hle : δ' ≤ S.δ) : SegmentData F where
  δ := δ'
  pos := hδ'
  sc := S.sc
  sv := S.sv
  seg P Q h := S.seg P Q (h.trans_le hle)
  unif P₀ Q₀ h := S.unif P₀ Q₀ (h.trans_le hle)
  rev P Q h := S.rev P Q (h.trans_le hle)
  pkg T P Q hP h hT := S.pkg T P Q hP (h.trans_le hle) hT
  smooth P Q hne h := S.smooth P Q hne (h.trans_le hle)

/-- Polygons of energy at most B are short when N is large. -/
theorem short_of_energy_le {c δ B : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hedge : ∀ (N : ℕ) [NeZero N] (q : ZMod N → Sphere n) (b : ℝ),
      polyEnergy F N (fun i => (q i : Ambient n)) ≤ b →
      ∀ j : ZMod N, N * (c * ‖(q (j + 1) : Ambient n) - q j‖ ^ 2) ≤ b)
    {N : ℕ} [NeZero N] (hN : B / (c * δ ^ 2) < N) (q : ZMod N → Sphere n)
    (hq : PolygonDescent.energy F N q ≤ B) : ShortPolygon δ q := by
  intro j
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have h1 := hedge N q B hq j
  have h3 : B < N * (c * δ ^ 2) := by
    rw [div_lt_iff₀ (by positivity)] at hN
    linarith
  have h4 : N * (c * ‖(q (j + 1) : Ambient n) - q j‖ ^ 2) < N * (c * δ ^ 2) := by linarith
  have h5 : ‖(q (j + 1) : Ambient n) - q j‖ ^ 2 < δ ^ 2 :=
    lt_of_mul_lt_mul_left (lt_of_mul_lt_mul_left h4 hN0.le) hc.le
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le h5

/-- With finitely many prime closed geodesic images, the ordinary cohomology of the loop pair
(t_b, t_a) for tight cuts around the only critical level of a band is the product of the
cohomologies of two polygon lens pairs, for all large numbers of vertices. -/
theorem exists_loop_crossing_oriented (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      ∃ Wp Wm : Set (Poly n N), IsOpen Wp ∧ IsOpen Wm ∧ Disjoint Wp Wm ∧
      ∃ D : Descent (Poly n N) (PolygonDescent.energy F N), ∃ d : ℝ, 0 < d ∧
        ∀ (a' a b T : ℝ) (hab : a ≤ b), a₀ ≤ a' → a' < a → b ≤ b₀ →
          b ^ 2 - a' ^ 2 < d → 1 ≤ T → ∀ k : ℕ,
          Nonempty (H (triv (pairOf (lev_mono F hab))) k ≃ₗ[ZMod 2]
            (H (triv (pairOf (partY_sub_partU (PolygonDescent.energy F N) D Wp
                (a ^ 2) (b ^ 2) T))) k ×
              H (triv (pairOf (partY_sub_partU (PolygonDescent.energy F N) D Wm
                (a ^ 2) (b ^ 2) T))) k)) := by
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨δ₁, hδ₁, hC1⟩ := exists_ambientMinEnergy_contDiffAt_one F
  set S := shrink S₀ (lt_min S₀.pos hδ₁) (min_le_left _ _) with hS
  have hSδ : S.δ ≤ δ₁ := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := S.δ) (a := b₀) S.pos
  obtain ⟨e, he, hedge⟩ := PolygonEnergyGlobal.exists_edge_bound F hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (b₀ ^ 2 / (e * S.δ ^ 2))
  refine ⟨max N₁ N₂, fun N hN _ => ?_⟩
  have hNpos : 0 < N := NeZero.pos N
  let M : PolygonModelData F b₀ N :=
    PolygonModelData.mk S fun u hu s t hs ht hst =>
      hN₁ N ((le_max_left _ _).trans hN) hNpos u hu s t hs ht hst
  have hNR : b₀ ^ 2 / (e * S.δ ^ 2) < N :=
    hN₂.trans_le (Nat.cast_le.mpr ((le_max_right _ _).trans hN))
  have hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q ≤ b₀ ^ 2 →
      ShortPolygon M.δ q := fun q hq => short_of_energy_le he S.pos hedge hNR q hq
  have hC : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < M.δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)) :=
    fun P Q h => hC1 P Q (h.trans_le hSδ)
  obtain ⟨Up, Um, hUp, hUm, hUU, -, -, D, d, hd, hdec⟩ :=
    exists_oriented_decomposition M hn hfin hC ha₀ hab₀ hone hshort
  refine ⟨near M Up, near M Um, near_isOpen M hUp, near_isOpen M hUm, near_disjoint M hUU,
    D, d, hd, ?_⟩
  intro a' a b T hab ha' haa hb hwidth hT k
  have ha'0 : 0 < a' := ha₀.trans_le ha'
  have ha : 0 < a := ha'0.trans haa
  have hb0 : 0 < b := ha.trans_le hab
  have hsq : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  obtain ⟨e₁⟩ := hdec (a' ^ 2) (a ^ 2) (b ^ 2) T hsq (zero_le_one.trans hT)
    (pow_le_pow_left₀ ha₀.le ha' 2) (pow_lt_pow_left₀ haa ha'0.le two_ne_zero)
    (pow_le_pow_left₀ hb0.le hb 2) hwidth hT k
  let e₂ := LinearEquiv.ofBijective _ (sample_bijective M
    (fun q hq => hshort q (hq.le.trans (pow_le_pow_left₀ hb0.le hb 2))) ha hab hb k)
  exact ⟨e₂.symm.trans e₁⟩

end

end Finsler.LoopCrossingOriented
