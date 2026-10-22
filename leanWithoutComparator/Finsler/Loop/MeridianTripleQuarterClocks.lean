module

public import Finsler.Loop.BasedMeridianProducts
public import Finsler.Loop.MeridianLoopQuarterPaths

/-! Twelve exact quarter charts of the ORIGINAL triple based path.
The first two loops have duration1/4 and the third duration1/2;
all quarter endpoints and seams are retained. -/
@[expose] public section
namespace Finsler.MeridianTripleQuarterClocks
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.RationalSphereArc
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def triple {n : ℕ} (P : Sphere n) (v₀ : equator P) (v : Fin 3 → equator P) : Path P P :=
  ((loop P v₀ (v 0)).trans (loop P v₀ (v 1))).trans (loop P v₀ (v 2))

theorem original_family {n : ℕ} (P : Sphere n) (v₀ : equator P) (v : Fin 3 → equator P) :
    BasedMeridianProducts.tripleFamily P v₀ ((v 0, v 1), v 2) = triple P v₀ v := rfl

def localTime (q : Fin 4) (t : _root_.unitInterval) : ℝ := ((q.val : ℝ) + (t : ℝ)) / 4

theorem localTime_mem (q : Fin 4) (t : _root_.unitInterval) : localTime q t ∈ Set.Icc (0 : ℝ) 1 := by
  have hq : (q.val : ℝ) ≤ 3 := by exact_mod_cast (show q.val ≤ 3 by omega)
  have hq₀ : (0 : ℝ) ≤ q.val := Nat.cast_nonneg _
  constructor <;> dsimp [localTime] <;> linarith [t.property.1, t.property.2]

def clock (k : Fin 3) (q : Fin 4) (t : _root_.unitInterval) : ℝ :=
  match k with
  | 0 => localTime q t / 4
  | 1 => (1 + localTime q t) / 4
  | 2 => (1 + localTime q t) / 2

theorem clock_mem (k : Fin 3) (q : Fin 4) (t : _root_.unitInterval) : clock k q t ∈ Set.Icc (0 : ℝ) 1 := by
  have ht := localTime_mem q t
  fin_cases k <;> constructor <;> dsimp [clock] <;> linarith [ht.1, ht.2]

def piece {n : ℕ} (P : Sphere n) (v₀ v : equator P) (q : Fin 4) (t : _root_.unitInterval) : Sphere n :=
  match q with
  | 0 => arc (outgoing P v) t
  | 1 => arc (incoming P v) t
  | 2 => (arc (incoming P v₀)).symm t
  | 3 => (arc (outgoing P v₀)).symm t

theorem loop_quarter {n : ℕ} (P : Sphere n) (v₀ v : equator P) (q : Fin 4) (t : _root_.unitInterval) :
    (loop P v₀ v).extend (localTime q t) = piece P v₀ v q t := by
  fin_cases q
  · simpa only [localTime, piece, Nat.cast_zero, zero_add] using MeridianLoopQuarterPaths.first P v₀ v t
  · simpa only [localTime, piece, Nat.cast_one] using MeridianLoopQuarterPaths.second P v₀ v t
  · simpa only [localTime, piece, Nat.cast_ofNat] using MeridianLoopQuarterPaths.third P v₀ v t
  · simpa only [localTime, piece, Nat.cast_ofNat] using MeridianLoopQuarterPaths.fourth P v₀ v t

theorem triple_first {n : ℕ} (P : Sphere n) (v₀ : equator P) (v : Fin 3 → equator P)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (triple P v₀ v).extend (s / 4) = (loop P v₀ (v 0)).extend s := by
  rw [triple, Path.extend_trans_of_le_half _ _ (by linarith [hs.2]),
    Path.extend_trans_of_le_half _ _ (by linarith [hs.2])]
  congr 1
  ring

theorem triple_second {n : ℕ} (P : Sphere n) (v₀ : equator P) (v : Fin 3 → equator P)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (triple P v₀ v).extend ((1 + s) / 4) = (loop P v₀ (v 1)).extend s := by
  rw [triple, Path.extend_trans_of_le_half _ _ (by linarith [hs.2]),
    Path.extend_trans_of_half_le _ _ (by linarith [hs.1])]
  congr 1
  ring

theorem triple_third {n : ℕ} (P : Sphere n) (v₀ : equator P) (v : Fin 3 → equator P)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (triple P v₀ v).extend ((1 + s) / 2) = (loop P v₀ (v 2)).extend s := by
  rw [triple, Path.extend_trans_of_half_le _ _ (by linarith [hs.1])]
  congr 1
  ring

theorem triple_quarter {n : ℕ} (P : Sphere n) (v₀ : equator P) (v : Fin 3 → equator P)
    (k : Fin 3) (q : Fin 4) (t : _root_.unitInterval) :
    (triple P v₀ v).extend (clock k q t) = piece P v₀ (v k) q t := by
  fin_cases k
  · exact (triple_first P v₀ v _ (localTime_mem q t)).trans (loop_quarter P v₀ (v 0) q t)
  · exact (triple_second P v₀ v _ (localTime_mem q t)).trans (loop_quarter P v₀ (v 1) q t)
  · exact (triple_third P v₀ v _ (localTime_mem q t)).trans (loop_quarter P v₀ (v 2) q t)

end
end Finsler.MeridianTripleQuarterClocks
