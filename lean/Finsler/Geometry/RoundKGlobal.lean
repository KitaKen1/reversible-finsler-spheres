module

public import Finsler.Geometry.RoundRGlobal
public import Finsler.Topology.GlobalK
public import Finsler.Topology.BasisData
public import Finsler.Topology.BorelCrossingK
public import Finsler.Topology.BorelLocalK

/-! The K-filtration of the round sphere and the global basis (stage 13 assembly).

The half rotation commutes with the reversal on all pairs of the round filtration, and the
restrictions commute with it; v^{n+1} = v^{d+2} vanishes on the K-crossings of odd m = j + 1
(`RoundCrossW.crossV_pow_zero`). With the local K-lift of the e-multiple of the start class at
the odd stages j (G6b, the hypothesis `YTop`) this is a `GlobalK.KGlobal (n − 1)`, whose basis data,
recast from the degree n − 1 + 1 and the cast evaluation cup to n and `fullE`, is the
`BasisBudget.Data n` required by `CoreResidual.Inputs`, together with w^n = 0.

The remaining inputs are exactly: `ECompat` (e-compatibility of the round crossings), `Supports`
(compact supports of loop space homology along the cuts; Tau Ceti `DirectedUnion`), `YTop` (G6b). -/

@[expose] public section

namespace Finsler.RoundKGlobal

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundCrossPattern
open Finsler.RoundFiltration Finsler.RoundTails Finsler.RoundRGlobal Finsler.GlobalBasis
open Finsler.GlobalK Finsler.FiltrationCollapse Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.BorelCrossing Finsler.BorelGraded Finsler.BorelCanonicalEvaluation
open Finsler.GysinPattern Finsler.BorelK Finsler.BorelCrossingK Finsler.BorelIterate
open Finsler.BasisBudget Finsler.CriticalLevels Finsler.NilpotentW
open Set

noncomputable section

variable {n : ℕ}

/-- **G6b**: at the odd stages the e-multiple of the start class lifts to K-Borel cohomology. -/
def YTop (n : ℕ) (hn : 3 ≤ n) : Prop :=
  ∀ j, Odd j → ∃ y : HR (borelInv (halfCommutingCross (roundMetric n) (cut_mono j)))
      ((n - 1) + 1 + lc n (j + 1)),
    fgtR (halfCommutingCross (roundMetric n) (cut_mono j)) _ y =
      castHR (degE hn _) (crossE (roundMetric n) (cut_mono j) (by omega) (lc n (j + 1))
        (startClass hn j))

theorem crit_eq (j : ℕ) {c : ℝ} (hc : c ∈ crit (roundMetric n) ∩ Icc (cut j) (cut (j + 1))) :
    c = 2 * Real.pi * ((j + 1 : ℕ) : ℝ) := by
  obtain ⟨hc, hca, hcb'⟩ := hc
  obtain ⟨m', hm', rfl⟩ := Finsler.RoundCrossW.crit_round hc
  have hπ := Real.pi_pos
  have h1 : (((j + 1 : ℕ) : ℝ) - 1) < m' :=
    lt_of_mul_lt_mul_left ((cut_lo j).trans_le hca) (by positivity)
  have h2 : (m' : ℝ) < ((j + 1 : ℕ) : ℝ) + 1 :=
    lt_of_mul_lt_mul_left (hcb'.trans_lt (cut_hi j)) (by positivity)
  have e1 : j + 1 < m' + 1 := by exact_mod_cast (show ((j + 1 : ℕ) : ℝ) < m' + 1 by linarith)
  have e2 : m' < j + 1 + 1 := by exact_mod_cast h2
  have : m' = j + 1 := by omega
  rw [this]

theorem vnil_round (hn : 3 ≤ n) (j : ℕ) (hj : Even j) (lo : ℕ)
    (x : HR (borelInv (halfCommutingCross (roundMetric n) (cut_mono j))) lo) :
    wPow (borelInv (halfCommutingCross (roundMetric n) (cut_mono j))) lo ((n - 1) + 2) x = 0 := by
  have hπ := Real.pi_pos
  have h2 : (n - 1) + 2 = n + 1 := by omega
  rw [h2]
  have ha : 0 < cut j := by
    unfold cut
    positivity
  exact Finsler.RoundCrossW.crossV_pow_zero (by omega) (cut_mono j) ha
    (a_not_crit (Nat.succ_pos j) (cut_lo j) (cut_ac j)) (b_not_crit (cut_cb j) (cut_hi j))
    (crit_subsingleton (cut_lo j) (cut_hi j))
    (fun c hc => ⟨j + 1, hj.add_one, crit_eq j hc⟩) lo x

/-- **The K-filtration of the round sphere.** -/
def roundKGlobal (hn : 3 ≤ n) (he : ECompat n hn) (hS : Supports n) (hy : YTop n hn) :
    KGlobal (n - 1) where
  toRGlobal := roundRGlobal hn he hS
  l_zero := by
    change lc n (0 + 1) = n - 1
    unfold lc
    simp
  SG := halfCommutingFull n
  SZ m := halfCommuting (roundMetric n) (cut m)
  SP j := halfCommutingCross (roundMetric n) (cut_mono j)
  ST m := halfCommutingTail (roundMetric n) (cut m)
  ι_s j k x := (relComm (roundMetric n) (cut_mono j)).comm_s k x
  π_s j k x := (cutComm (roundMetric n) (cut_mono j)).comm_s k x
  ρ_s m k x := (resComm (roundMetric n) (cut m)).comm_s k x
  κ_s m k x := (tailComm (roundMetric n) (cut m)).comm_s k x
  vnil j hj lo x := vnil_round hn j hj lo x
  ytop j hj := hy j hj

/-! ### The global basis -/

/-- Basis data in a degree equal to n, with an evaluation cup that differs by a degree cast. -/
def recast {G : InvComplex} {SG : Commuting G} {n n' : ℕ} (h : n' = n)
    {E : ∀ q, HR G q →ₗ[ZMod 2] HR G (n + q)} {E' : ∀ q, HR G q →ₗ[ZMod 2] HR G (n' + q)}
    (hE : ∀ q x, castHR (congrArg (· + q) h) (E' q x) = E q x) (A : AbsData G SG n' E') :
    AbsData G SG n E := by
  subst h
  have hE' : E' = E := funext fun q => LinearMap.ext fun x => hE q x
  subst hE'
  exact A

theorem hE_round (hn : 3 ≤ n) (q : ℕ) (x : HR (fullComplex n) q) :
    castHR (congrArg (· + q) (show n - 1 + 1 = n by omega))
        (castHR (degE hn q) (fullE n (by omega) q x)) = fullE n (by omega) q x := by
  rw [castHR_castHR]
  rfl

/-- **The global basis of the round sphere** (stage 13), given the three remaining inputs. -/
def roundData (hn : 3 ≤ n) (he : ECompat n hn) (hS : Supports n) (hy : YTop n hn) :
    Data n (by omega) :=
  Finsler.BasisData.toData (recast (show n - 1 + 1 = n by omega) (hE_round hn)
    (KGlobal.absData (roundKGlobal hn he hS hy)))

/-- **w^n = 0** on the reflection Borel cohomology of the loop space pair. -/
theorem round_w_nil (hn : 3 ≤ n) (he : ECompat n hn) (hS : Supports n) (lo : ℕ)
    (x : HR (fullComplex n) lo) : wPow (fullComplex n) lo n x = 0 := by
  have h := (roundRGlobal hn he hS).w_nil lo x
  have e : n - 1 + 1 = n := by omega
  rw [e] at h
  exact h

end

end Finsler.RoundKGlobal
