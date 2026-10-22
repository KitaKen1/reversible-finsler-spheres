module

public import Finsler.Topology.OrientedCritical
public import Finsler.Topology.BirkhoffNear

/-! The vanishing of w on single crossings. With finitely many prime closed geodesic images,
the critical set of a positive level has an oriented uniform neighbourhood (the two orientations
of the closed geodesics are separated), the loops which are not pushed below a tight lower cut
by the curve shortening map lie in this neighbourhood, and on pairs of reversal-invariant sets
of loops inside an oriented set w acts as zero. Hence tight cuts around a critical level carry
oriented local lenses, intervals without critical levels carry level deformations, and w acts
as zero on the reflection Borel cohomology of the crossing pair (t_b, t_a) for regular cuts
0 < a ≤ b with at most one critical level between them. -/

@[expose] public section

namespace Finsler.CrossingW

open Set
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.BorelLoop
open Finsler.BorelCochain Finsler.BorelCrossing Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCurveVariation Finsler.CriticalLevels Finsler.BorelLocal
open Finsler.OrientedCritical

noncomputable section

variable {n : ℕ}

/-- Level deformations on intervals without critical levels. -/
theorem levelDeformation_of_regular (F : ReversibleMetric n) (hn : 1 ≤ n) (a a' b : ℝ)
    (ha : 0 < a) (haa : a ≤ a') (hab : a' ≤ b) (hreg : ∀ x ∈ Icc a a', x ∉ crit F) :
    Nonempty (RegularInterval.LevelDeformation F a a' b) := by
  obtain ⟨S, k, hk⟩ := BirkhoffDescent.exists_descent F hn ha haa hab fun u hu h1 h2 =>
    hreg (Real.sqrt (energy F u))
      ⟨(Real.le_sqrt' ha).mpr h1, Real.sqrt_le_iff.mpr ⟨(ha.trans_le haa).le, h2⟩⟩
      (crit_mem F u hu (lt_of_lt_of_le (pow_pos ha 2) h1))
  exact ⟨Shortening.levelDeformation S k hk⟩

/-- Oriented local lenses at tight cuts around a critical level, for finitely many prime closed
geodesic images. -/
theorem exists_oriented_localLens (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c) :
    ∃ (V : Set (Loops n)) (_ : Orientation V) (ε : ℝ), 0 < ε ∧
      ∀ a b : ℝ, c - ε < a → a < c → c < b → b < c + ε → Nonempty (LocalLens F a b V) := by
  obtain ⟨ρ, hρ, ⟨O⟩⟩ := exists_orientation F hfin hc
  obtain ⟨ε, hε, hL⟩ := localLens_of_shortening F hc (tube F c ρ)
    (BirkhoffNear.exists_near F hn hc hρ)
  exact ⟨tube F c ρ, O, ε, hε, hL⟩

/-- W-ZERO. With finitely many prime closed geodesic images, for regular cuts 0 < a ≤ b with at
most one critical level between them, w acts as zero on the reflection Borel cohomology of the
crossing pair (t_b, t_a). -/
theorem crossW_zero_of_finite (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit F)
    (hbc : b ∉ crit F) (hsub : (crit F ∩ Icc a b).Subsingleton) (q : ℕ)
    (z : HR (crossComplex F hab) q) : w (crossComplex F hab) q z = 0 :=
  crossW_zero_of_flow F (crit F) (levelDeformation_of_regular F hn)
    (fun _ hc => exists_oriented_localLens F hn hfin (crit_pos F hc)) hab ha hac hbc hsub q z

/-- With finitely many prime closed geodesic images, forgetting the action is injective in
positive degrees on the reflection Borel cohomology of a single crossing. -/
theorem cross_forget_injective (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit F)
    (hbc : b ∉ crit F) (hsub : (crit F ∩ Icc a b).Subsingleton) (q : ℕ) :
    Function.Injective (forget (crossComplex F hab) (q + 1)) :=
  forget_injective_of_w_zero _ q (crossW_zero_of_finite F hn hfin hab ha hac hbc hsub q)

/-- With finitely many prime closed geodesic images, the transfer from ordinary to reflection
Borel cohomology is surjective on a single crossing. -/
theorem cross_transfer_surjective (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit F)
    (hbc : b ∉ crit F) (hsub : (crit F ∩ Icc a b).Subsingleton) (q : ℕ) :
    Function.Surjective (transfer (crossComplex F hab) q) :=
  transfer_surjective_of_w_zero _ q (crossW_zero_of_finite F hn hfin hab ha hac hbc hsub q)

end

end Finsler.CrossingW
