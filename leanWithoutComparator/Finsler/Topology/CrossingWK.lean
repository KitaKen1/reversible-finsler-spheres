module

public import Finsler.Topology.CrossingW
public import Finsler.Topology.BorelLocalK

/-! The vanishing of the reflection class on the K-Borel cohomology of single crossings.
Rotations do not increase the uniform distance of loops and preserve the positive critical
loops of a level; the half rotation preserves the negative ones. Hence the orientation of the
uniform neighbourhood of the critical set of a level is invariant under the half rotation. The
curve shortening maps of polygon models with an even number of vertices commute with the half
rotation, so tight cuts around a critical level carry oriented local lenses compatible with the
half rotation. With finitely many prime closed geodesic images, the reflection class therefore
acts as zero on the K-Borel cohomology of the crossing pair (t_b, t_a) for regular cuts
0 < a ≤ b with at most one critical level between them. -/

@[expose] public section

namespace Finsler.CrossingWK

open Set Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.SmoothSobolev
open Finsler.SobolevCurveVariation Finsler.SobolevCircleRepresentative Finsler.SobolevReverse
open Finsler.SobolevShift Finsler.SobolevCircleAction Finsler.SobolevShiftEnergy
open Finsler.CriticalLevels Finsler.BorelLoop Finsler.BorelLocal Finsler.BorelCochain
open Finsler.BorelCrossing Finsler.OrientedCritical Finsler.BorelK Finsler.BorelCrossingK
open Finsler.BorelIterate Finsler.BorelFreeK Finsler.BorelLocalK Finsler.ShorteningK

noncomputable section

variable {n : ℕ}

local notation "Circ" => Finsler.SobolevCircleRepresentative.Circle

/-- Rotation does not increase the uniform distance. -/
theorem dist_sphereCircleMap_vadd_le (θ : Circ) (x y : SphereLoop n) :
    dist (sphereCircleMap (θ +ᵥ x)) (sphereCircleMap (θ +ᵥ y)) ≤
      dist (sphereCircleMap x) (sphereCircleMap y) := by
  rw [ContinuousMap.dist_le dist_nonneg]
  intro φ
  rw [sphereCircleMap_vadd, sphereCircleMap_vadd]
  exact ContinuousMap.dist_apply_le_dist _

/-- Rotations of positive critical loops of a level are positive critical loops of the level. -/
theorem vadd_mem_posCrit (F : ReversibleMetric n) (c : ℝ) (φ : Circ) {γ : SphereLoop n}
    (hγ : γ ∈ posCrit F c) : φ +ᵥ γ ∈ posCrit F c := by
  obtain ⟨s, hs, k, θ, hk, hck, rfl⟩ := hγ
  exact ⟨s, hs, k, φ + θ, hk, hck, vadd_vadd φ θ _⟩

/-- The half rotation of a negative critical loop of a level is a negative critical loop of the
level. -/
theorem half_mem_negCrit (F : ReversibleMetric n) (c : ℝ) {γ : SphereLoop n}
    (hγ : γ ∈ negCrit F c) : half +ᵥ γ ∈ negCrit F c := by
  obtain ⟨γ', hγ', rfl⟩ := hγ
  exact ⟨half +ᵥ γ', vadd_mem_posCrit F c half hγ', reverse_half γ'⟩

/-- The orientation of the uniform neighbourhood of the critical set of a level is invariant
under the half rotation. -/
theorem halfInvariant_orientation (F : ReversibleMetric n) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hsep : ∀ γ₁ ∈ posCrit F c, ∀ γ₂ ∈ negCrit F c,
      δ ≤ dist (sphereCircleMap γ₁) (sphereCircleMap γ₂)) :
    HalfInvariant (orientation F hc hδ hsep) where
  pos_half := by
    rintro u ⟨γ, hγ, hd⟩
    exact ⟨half +ᵥ γ, vadd_mem_posCrit F c half hγ,
      lt_of_le_of_lt (dist_sphereCircleMap_vadd_le half u γ) hd⟩
  neg_half := by
    rintro u ⟨γ, hγ, hd⟩
    exact ⟨half +ᵥ γ, half_mem_negCrit F c hγ,
      lt_of_le_of_lt (dist_sphereCircleMap_vadd_le half u γ) hd⟩

/-- Local lenses compatible with the half rotation from shortenings commuting with it: if for
tight cuts a' < c < b around a positive level c some shortening D of t_b commuting with the half
rotation is such that the loops x of t_b with √E(D x) > a' lie in V, then tight cuts around c
carry local lenses for V compatible with the half rotation. -/
theorem halfLens_of_shortening (F : ReversibleMetric n) {c : ℝ} (hc0 : 0 < c)
    (V : Set (Loops n))
    (hloc : ∃ ε : ℝ, 0 < ε ∧ ∀ a' b : ℝ, c - ε < a' → a' < c → c < b → b < c + ε →
      ∃ S : Shortening.Data F b, HalfComm S ∧ ∀ x : lev F b,
        a' < Real.sqrt (energy F (S.D x : SphereLoop n)) → (x : Loops n) ∈ V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a b : ℝ, c - ε < a → a < c → c < b → b < c + ε →
      ∃ L : LocalLens F a b V, HalfLens F L := by
  obtain ⟨ε, hε, h⟩ := hloc
  refine ⟨min ε c, lt_min hε hc0, ?_⟩
  intro a b ha1 ha2 hb1 hb2
  have ha0 : 0 < a := by
    have : c - min ε c ≥ 0 := sub_nonneg.mpr (min_le_right _ _)
    linarith
  have haε : c - ε < a := by
    have := min_le_left ε c
    linarith
  obtain ⟨a', ha'1, ha'2⟩ := exists_between haε
  have hbε : b < c + ε := by
    have := min_le_left ε c
    linarith
  obtain ⟨S, hSh, hS⟩ := h a' b ha'1 (ha'2.trans ha2) hb1 hbε
  exact ⟨localLens S V ha0 ha'2 (ha2.trans hb1).le hS,
    halfLens_localLens S hSh V ha0 ha'2 (ha2.trans hb1).le hS⟩

/-- Oriented local lenses compatible with the half rotation at tight cuts around a critical
level, for finitely many prime closed geodesic images. -/
theorem exists_oriented_halfLens (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c) :
    ∃ (V : Set (Loops n)) (O : Orientation V) (_ : HalfInvariant O) (ε : ℝ), 0 < ε ∧
      ∀ a b : ℝ, c - ε < a → a < c → c < b → b < c + ε →
        ∃ L : LocalLens F a b V, HalfLens F L := by
  obtain ⟨δ, hδ, hsep⟩ := exists_separation F hfin c
  obtain ⟨ε, hε, hL⟩ := halfLens_of_shortening F hc (tube F c (δ / 4))
    (exists_near_half F hn hc (by positivity))
  exact ⟨tube F c (δ / 4), orientation F hc hδ hsep, halfInvariant_orientation F hc hδ hsep,
    ε, hε, hL⟩

/-- The two commuting involutions on the crossing cochains in the form used for pairs are those
of the K-Borel crossing cochains. -/
theorem crossCommuting_eq (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) :
    crossCommuting F hab = halfCommutingCross F hab := rfl

/-- K-W-ZERO. With finitely many prime closed geodesic images, for regular cuts 0 < a ≤ b with
at most one critical level between them, the reflection class acts as zero on the K-Borel
cohomology of the crossing pair (t_b, t_a). -/
theorem crossWK_zero_of_finite (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit F)
    (hbc : b ∉ crit F) (hsub : (crit F ∩ Icc a b).Subsingleton) (q : ℕ)
    (z : HKCross F hab q) :
    BorelGraded.onHR (innerW (halfCommutingCross F hab)) q z = 0 :=
  crossWK_zero_of_flow F (crit F) (CrossingW.levelDeformation_of_regular F hn)
    (fun _ hc => exists_oriented_halfLens F hn hfin (crit_pos F hc)) hab ha hac hbc hsub q z

end

end Finsler.CrossingWK
