module

public import Finsler.Geometry.RoundTails
public import Finsler.Topology.GlobalBasis
public import Finsler.Topology.BorelCanonicalEvaluation

/-! The global filtration of the round sphere (G4/G5 wiring of the reflection part).

The round filtration, the full complex (Λ, M), the tails (Λ, t_{c_m}) with the restrictions, and
the canonical e actions (cup with the evaluation pullback of the sphere top class, with the degree
cast n + q = d + 1 + q) form an `RGlobal (n − 1)`, given the e-compatibility of the round
crossings and compact supports of the homology of the loop space along the cuts. -/

@[expose] public section

namespace Finsler.RoundRGlobal

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundCrossPattern
open Finsler.RoundFiltration Finsler.RoundTails Finsler.GlobalBasis Finsler.FiltrationCollapse
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelGraded Finsler.BorelCanonicalEvaluation Finsler.GysinPattern

noncomputable section

variable {n : ℕ}

theorem degE (hn : 3 ≤ n) (q : ℕ) : n + q = (n - 1) + 1 + q := by omega

theorem E_rho_eq (hn : 3 ≤ n) (m q : ℕ) (x : HR (fullComplex n) q) :
    HRmap (resHom (roundMetric n) (cut m)) ((n - 1) + 1 + q)
        (castHR (degE hn q) (fullE n (by omega) q x)) =
      castHR (degE hn q) (levE (roundMetric n) (cut m) (by omega) q
        (HRmap (resHom (roundMetric n) (cut m)) q x)) := by
  rw [HRmap_castHR, fullE_res]

theorem E_iota_eq (hn : 3 ≤ n) (j q : ℕ)
    (x : HR (crossComplex (roundMetric n) (cut_mono j)) q) :
    HRmap (relHom (roundMetric n) (cut_mono j)) ((n - 1) + 1 + q)
        (castHR (degE hn q) (crossE (roundMetric n) (cut_mono j) (by omega) q x)) =
      castHR (degE hn q) (levE (roundMetric n) (cut (j + 1)) (by omega) q
        (HRmap (relHom (roundMetric n) (cut_mono j)) q x)) := by
  rw [HRmap_castHR, crossE_rel]

theorem E_w_eq (hn : 3 ≤ n) (q : ℕ) (x : HR (fullComplex n) q) :
    castHR (Nat.add_assoc ((n - 1) + 1) q 1).symm
        (castHR (degE hn (q + 1)) (fullE n (by omega) (q + 1) (w _ q x))) =
      w _ ((n - 1) + 1 + q) (castHR (degE hn q) (fullE n (by omega) q x)) := by
  rw [w_castHR, ← fullE_w, castHR_castHR, castHR_castHR]

/-- **The global filtration of the round sphere.** -/
def roundRGlobal (hn : 3 ≤ n) (he : ECompat n hn) (hS : Supports n) : RGlobal (n - 1) where
  toFiltration := roundFiltration hn he
  G := fullComplex n
  T m := tailComplex (roundMetric n) (cut m)
  κ m := tailHom (roundMetric n) (cut m)
  ρ m := resHom (roundMetric n) (cut m)
  exactT m := shortExactTail (roundMetric n) (cut m)
  tail m q hq z := tail_zero hn hS m q hq z
  ρ_π m q x := by
    change HRmap (cutHom (roundMetric n) (cut_mono m)) q
      (HRmap (resHom (roundMetric n) (cut (m + 1))) q x) =
        HRmap (resHom (roundMetric n) (cut m)) q x
    rw [← HRmap_comp]
    exact HRmap_congr (cut_res_f (roundMetric n) (cut_mono m)) q x
  E q := (castHR (degE hn q)).comp (fullE n (by omega) q)
  EZ m q := (castHR (degE hn q)).comp (levE (roundMetric n) (cut m) (by omega) q)
  EP j q := (castHR (degE hn q)).comp (crossE (roundMetric n) (cut_mono j) (by omega) q)
  E_ρ m q x := E_rho_eq hn m q x
  E_ι j q x := E_iota_eq hn j q x
  E_w q x := E_w_eq hn q x
  σ_eq j := castHR_castHR _ _ _

end

end Finsler.RoundRGlobal
