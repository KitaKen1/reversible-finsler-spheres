module

public import Finsler.Topology.EndgameShortening
public import Finsler.Topology.BirkhoffLocalize
public import Finsler.Topology.GeodesicMargin

/-! The final section with the vanishing of e on single crossings replaced by elementary
statements about closed geodesics. `CriticalInputs` keeps the other lemma-level inputs of
`EndgameAssembly.Core` and asks for a point p of the sphere at distance at least ρ > 0 from
every tangent critical loop of positive energy, and that the set of critical levels is positive
and contains √E of every such loop. The descent and localization properties of the curve
shortening map then hold (`BirkhoffDescent.exists_descent`, `BirkhoffLocalize.exists_localize`),
so the shortening inputs, the flow inputs and the vanishing of e follow, and the critical inputs
are contradictory as well. With finitely many prime closed geodesic images such a point exists
(`GeodesicMargin.exists_margin`), so e vanishes on single crossings (`crossE_zero_of_finite`) and
the inputs of `Core` alone are contradictory, provided the critical levels are positive and
contain √E of every tangent critical loop of positive energy. The inputs of `Core` are not
proved here. -/

@[expose] public section

namespace Finsler.EndgameCritical

open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.BorelLoop
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.SobolevCurveVariation
open Finsler.EndgameAssembly Finsler.EndgameShortening
open Set

noncomputable section

variable {n : ℕ}

/-- The lemma-level inputs of the final section for one reversible metric, with the vanishing
of e on single crossings replaced by a point at positive distance from all closed geodesics and
by the statement that the critical levels are positive and contain √E of every tangent critical
loop of positive energy. -/
structure CriticalInputs (F : ReversibleMetric n) (hn : 1 ≤ n) extends Core F hn where
  /-- a point of the sphere away from the closed geodesics -/
  p : Sphere n
  ρ : ℝ
  ρ_pos : 0 < ρ
  margin : ∀ u : SphereLoop n, TangentCritical F u → 0 < energy F u → ∀ t : ClosedInterval,
    ρ ≤ ‖(sphereRepresentative u t : Ambient n) - (p : Ambient n)‖
  crit_pos : ∀ c ∈ crit, 0 < c
  crit_mem : ∀ u : SphereLoop n, TangentCritical F u → 0 < energy F u →
    Real.sqrt (energy F u) ∈ crit

variable {F : ReversibleMetric n} {hn : 1 ≤ n}

/-- The shortening inputs from the critical inputs. -/
def toShorteningInputs (I : CriticalInputs F hn) : ShorteningInputs F hn where
  toCore := I.toCore
  p := I.p
  crit_pos := I.crit_pos
  descent := fun _ _ _ ha haa hab hreg =>
    BirkhoffDescent.exists_descent F hn ha haa hab fun u hu h1 h2 =>
      hreg (Real.sqrt (energy F u))
        ⟨(Real.le_sqrt' ha).mpr h1, Real.sqrt_le_iff.mpr ⟨(ha.trans_le haa).le, h2⟩⟩
        (I.crit_mem u hu (lt_of_lt_of_le (pow_pos ha 2) h1))
  localize := fun c hc =>
    BirkhoffLocalize.exists_localize F hn I.p I.ρ_pos I.margin (I.crit_pos c hc)

/-- The critical inputs of the final section are contradictory. -/
theorem false_of_criticalInputs (h2 : 2 ≤ n) (I : CriticalInputs F hn) : False :=
  false_of_shorteningInputs h2 (toShorteningInputs I)

/-- E-ZERO. With finitely many prime closed geodesic images, let crit be a set of positive
levels containing √E of every tangent critical loop of positive energy. Then for regular cuts
0 < a ≤ b with at most one point of crit between them, e acts as zero on the reflection Borel
cohomology of the crossing pair (t_b, t_a). -/
theorem crossE_zero_of_finite (F : ReversibleMetric n) (h2 : 2 ≤ n)
    (hfin : (primeImages F).Finite) (crit : Set ℝ) (hpos : ∀ c ∈ crit, 0 < c)
    (hmem : ∀ u : SphereLoop n, TangentCritical F u → 0 < energy F u →
      Real.sqrt (energy F u) ∈ crit)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit) (hbc : b ∉ crit)
    (hsub : (crit ∩ Icc a b).Subsingleton) (q : ℕ)
    (z : Finsler.BorelCochain.HR (Finsler.BorelCrossing.crossComplex F hab) q) :
    Finsler.BorelCrossing.crossE F hab (le_trans (by norm_num) h2) q z = 0 := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) h2
  obtain ⟨p, ρ, hρ, hmargin⟩ := GeodesicMargin.exists_margin F h2 hfin
  have hflow := Shortening.flow_of_shortening F p crit hpos
    (fun _ _ _ ha' haa hab' hreg =>
      BirkhoffDescent.exists_descent F hn1 ha' haa hab' fun u hu h1 h3 =>
        hreg (Real.sqrt (energy F u))
          ⟨(Real.le_sqrt' ha').mpr h1, Real.sqrt_le_iff.mpr ⟨(ha'.trans_le haa).le, h3⟩⟩
          (hmem u hu (lt_of_lt_of_le (pow_pos ha' 2) h1)))
    (fun c hc => BirkhoffLocalize.exists_localize F hn1 p hρ hmargin (hpos c hc))
  exact RegularInterval.crossE_zero_of_flow F hn1 p crit hflow.1 hflow.2 hab ha hac hbc hsub q z

/-- With finitely many prime closed geodesic images, the inputs of `Core` are contradictory if
the critical levels are positive and contain √E of every tangent critical loop of positive
energy: the vanishing of e on single crossings needs no further input. -/
theorem false_of_core (h2 : 2 ≤ n) (hfin : (primeImages F).Finite) (I : Core F hn)
    (hpos : ∀ c ∈ I.crit, 0 < c)
    (hmem : ∀ u : SphereLoop n, TangentCritical F u → 0 < energy F u →
      Real.sqrt (energy F u) ∈ I.crit) : False := by
  obtain ⟨p, ρ, hρ, hmargin⟩ := GeodesicMargin.exists_margin F h2 hfin
  exact false_of_criticalInputs h2
    { toCore := I, p := p, ρ := ρ, ρ_pos := hρ, margin := hmargin, crit_pos := hpos,
      crit_mem := hmem }

/-- If finiteness of the prime closed geodesic images yields the inputs of `Core` with positive
critical levels containing √E of every tangent critical loop of positive energy, there are
infinitely many prime closed geodesic images. -/
theorem infinite_of_core (F : ReversibleMetric n) (h2 : 2 ≤ n)
    (h : (primeImages F).Finite → ∃ I : Core F (le_trans (by norm_num) h2),
      (∀ c ∈ I.crit, 0 < c) ∧ ∀ u : SphereLoop n, TangentCritical F u → 0 < energy F u →
        Real.sqrt (energy F u) ∈ I.crit) :
    (primeImages F).Infinite := by
  intro hfin
  obtain ⟨I, hpos, hmem⟩ := h hfin
  exact false_of_core h2 hfin I hpos hmem

/-- Reduction of the candidate main assertion to the inputs of `Core`. -/
theorem assertion_of_core
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      ∃ I : Core F (le_trans (by norm_num) h3),
        (∀ c ∈ I.crit, 0 < c) ∧ ∀ u : SphereLoop n, TangentCritical F u → 0 < energy F u →
          Real.sqrt (energy F u) ∈ I.crit) :
    ReversibleSphereAssertion :=
  fun n h3 F => infinite_of_core F (le_trans (by norm_num) h3) (h n h3 F)

/-- If finiteness of the prime closed geodesic images yields the critical inputs, there are
infinitely many prime closed geodesic images. -/
theorem infinite_of_criticalInputs (F : ReversibleMetric n) (h2 : 2 ≤ n)
    (h : (primeImages F).Finite → Nonempty (CriticalInputs F (le_trans (by norm_num) h2))) :
    (primeImages F).Infinite := by
  intro hfin
  obtain ⟨I⟩ := h hfin
  exact false_of_criticalInputs h2 I

/-- Reduction of the candidate main assertion to the critical inputs. -/
theorem assertion_of_criticalInputs
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      Nonempty (CriticalInputs F (le_trans (by norm_num) h3))) :
    ReversibleSphereAssertion :=
  fun n h3 F => infinite_of_criticalInputs F (le_trans (by norm_num) h3) (h n h3 F)

end

end Finsler.EndgameCritical
