module

public import Finsler.Topology.RootCatalogue
public import Finsler.Topology.PacketSupport

/-! use one divisor-root bound for the
ordinary index windows of actual packet lenses. Fixed-label windows remain separate. -/

@[expose] public section

namespace Finsler.UniformPacketWindow

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.CriticalLevels
open Finsler.CriticalCircles Finsler.CircleLabel Finsler.CircleRoot Finsler.RootCatalogue
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.FlowLens
open Finsler.BorelComparison Finsler.PairTriple Finsler.AmbientPenalty Finsler.CirclePacketFamily
open Finsler.PacketDeformation Finsler.LocalLabelPacket Finsler.PacketFinite Finsler.PacketSupport
open Finsler.SampleK Finsler.GeodesicFrames
open Finsler.CrossingSlopes

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Finite-dimensional shifted groups vanish above a root support cutoff. -/
theorem shifted_vanishing {V W : ℕ → Type*}
    [∀ q, AddCommGroup (V q)] [∀ q, Module (ZMod 2) (V q)]
    [∀ q, AddCommGroup (W q)] [∀ q, Module (ZMod 2) (W q)]
    (b D : ℕ) (hfinite : ∀ q, Module.Finite (ZMod 2) (V q))
    (hrank : ∀ j, Module.finrank (ZMod 2) (V (j + b)) ≤ Module.finrank (ZMod 2) (W j))
    (hlow : ∀ q, q < b → ∀ z : V q, z = 0)
    (hroot : ∀ j, D ≤ j → ∀ z : W j, z = 0)
    {q : ℕ} (hq : q < b ∨ b + D ≤ q) (z : V q) : z = 0 := by
  rcases hq with hq | hq
  · exact hlow q hq z
  · let j := q - b
    have hj : D ≤ j := by dsimp [j]; omega
    have hjq : j + b = q := by dsimp [j]; omega
    haveI : Subsingleton (W j) := ⟨fun y y' => (hroot j hj y).trans (hroot j hj y').symm⟩
    have hzero : Module.finrank (ZMod 2) (W j) = 0 := Module.finrank_eq_zero_of_subsingleton _ _
    have hv := hrank j
    rw [hjq, hzero] at hv
    haveI := hfinite q
    haveI : Subsingleton (V q) :=
      (Module.finrank_zero_iff (R := ZMod 2) (M := V q)).mp (Nat.eq_zero_of_le_zero hv)
    exact Subsingleton.elim _ _

variable {n M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
variable {F : ReversibleMetric n} {c η a₀ b₀ : ℝ} {p : ι → Packet n (2 * M)}
variable {Γ : ι → Set (ZMod (2 * M) → Ambient n)}
variable (han : ∀ i, Analytic F c η (Γ i) (p i))
variable (hdis : ∀ i j, i ≠ j → Disjoint (p i).U (p j).U)
variable (G : CirclePacketFamily.Global M F p a₀ b₀) (hn : 1 ≤ n)
variable (hfin : (primeImages F).Finite) (hη : 0 ≤ η)
variable {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
variable (hlreg : l ∉ crit F) (hureg : u ∉ crit F)
variable (ha₀ : a₀ ≤ l ^ 2 - η) (hb₀ : u ^ 2 + η ≤ b₀)
variable (hTval : ∀ i y, y ∈ (p i).T →
  l ^ 2 + η < pen F (2 * M) 1 y ∧ pen F (2 * M) 1 y < u ^ 2 - η)
variable (hs : ∀ q, Function.Bijective (nativePull (samplePair (F := F) (M := M) hl hlu) q))
variable (hm : ∀ i, Model F c (p i))
variable (hlc : l ^ 2 < c ^ 2) (hcu : c ^ 2 < u ^ 2)

include han hdis hn hη hl hlu hlreg hureg ha₀ hb₀ hTval hs hm hlc hcu in
/-- A single bound of the finite root catalogue works for every actual packet carrying a
complete circle specification, independently of the iterate and critical level. -/
theorem circle_window {A : ℕ} (hA : Bounds F hfin A) (i : ι)
    (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) {k N : ℕ} (hk : 0 < k)
    (hd : CircleSpec F hfin ℓ hℓ k N c η (p i)) :
    ∃ e : ℝ, 0 < e ∧ ∀ a' a b T : ℝ,
      l ^ 2 ≤ a' → a' < a → a < c ^ 2 → c ^ 2 < b → b ≤ u ^ 2 → b - a' < e → 1 ≤ T →
      ∀ q : ℕ, (A : ℝ) < |(q : ℝ) -
        (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I k| →
        ∀ z : localH G i a b T q, z = 0 := by
  obtain ⟨hindex, hrootfinite, hrootzero⟩ := hA ℓ hℓ k hk
  obtain ⟨ef, hef, hfinite⟩ := exists_local_finite han hdis G hn hfin hη hl hlu hlreg hureg
    ha₀ hb₀ hTval hs
  obtain ⟨em, hem, hmodel⟩ := PacketDeformation.Global.lens_model han hdis G hn hη hm
    ha₀ hb₀ hlc hcu i
  obtain ⟨er, her, hroot⟩ := hd.2.2.2.1
  let e := min ef (min em er)
  refine ⟨e, lt_min hef (lt_min hem her),
    fun a' a b T hla' ha' hac hcb hbu hw hT q hq z => ?_⟩
  have hwf : b - a' < ef := hw.trans_le (min_le_left _ _)
  have hwm : b - a < em := by
    have h := hw.trans_le ((min_le_right ef (min em er)).trans (min_le_left em er))
    linarith
  have hwr : b - a < er := by
    have h := hw.trans_le ((min_le_right ef (min em er)).trans (min_le_right em er))
    linarith
  obtain ⟨hrank, hlow⟩ := hmodel a b T hT hac hcb hwm
  have hout : q < (p i).b ∨ (p i).b + A ≤ q :=
    outside_shifted_interval hd.2.2.1 hindex le_rfl hq
  apply shifted_vanishing (V := fun q => localH G i a b T q)
    (W := fun j => rootH F hfin ℓ hℓ k j) (p i).b A
    (hfinite a' a b T hla' ha' hac hcb hbu hwf hT i)
    (fun j => ?_) hlow hrootzero hout z
  change Module.finrank (ZMod 2) (localH G i a b T (j + (p i).b)) ≤ _
  rw [hrank j]
  exact hroot a b T hT hac hcb hwr j (hrootfinite j)

include han hdis hn hη hl hlu hlreg hureg ha₀ hb₀ hTval hs hm hlc hcu in
/-- The uniform packet index window is a window around its actual mean-index slope line. -/
theorem circle_slope_window {A : ℕ} (hA : Bounds F hfin A) (i : ι)
    (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) {k N : ℕ} (hk : 0 < k)
    (hd : CircleSpec F hfin ℓ hℓ k N c η (p i))
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
      (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop) = c) :
    ∃ e : ℝ, 0 < e ∧ ∀ a' a b T : ℝ,
      l ^ 2 ≤ a' → a' < a → a < c ^ 2 → c ^ 2 < b → b ≤ u ^ 2 → b - a' < e → 1 ≤ T →
      ∀ q : ℕ, ((A + n : ℕ) : ℝ) < |(q : ℝ) - slope F ℓ * c| →
        ∀ z : localH G i a b T q, z = 0 := by
  obtain ⟨e, he, hwindow⟩ := circle_window han hdis G hn hfin hη hl hlu hlreg hureg
    ha₀ hb₀ hTval hs hm hlc hcu hA i ℓ hℓ hk hd
  refine ⟨e, he, fun a' a b T hla' ha' hac hcb hbu hw hT q hq z => ?_⟩
  apply hwindow a' a b T hla' ha' hac hcb hbu hw hT q _ z
  have hp := (mem_labels F hfin ℓ).mp hℓ
  have hEpos := Finsler.OrientedCritical.chosen_energy_pos F ℓ.1 hp
  have hmean := (iterData (labelGeod F ℓ hp)).mean k hk
  have hslope : slope F ℓ * c = (k : ℝ) * (iterData (labelGeod F ℓ hp)).Δ := by
    unfold Finsler.CrossingSlopes.slope
    rw [dite_eq_left hp, ← hkc]
    field_simp
  by_contra hnot
  have hnear : |(q : ℝ) - (iterData (labelGeod F ℓ hp)).I k| ≤ A := not_lt.mp hnot
  have hmean' : |((iterData (labelGeod F ℓ hp)).I k : ℝ) - slope F ℓ * c| ≤ n := by
    rw [hslope]
    exact hmean
  have hbound : |(q : ℝ) - slope F ℓ * c| ≤ (A : ℝ) + n := calc
    _ = |((q : ℝ) - (iterData (labelGeod F ℓ hp)).I k) +
        (((iterData (labelGeod F ℓ hp)).I k : ℝ) - slope F ℓ * c)| := by congr 1; ring
    _ ≤ |(q : ℝ) - (iterData (labelGeod F ℓ hp)).I k| +
        |((iterData (labelGeod F ℓ hp)).I k : ℝ) - slope F ℓ * c| := abs_add_le _ _
    _ ≤ (A : ℝ) + n := add_le_add hnear hmean'
  exact (not_lt_of_ge hbound) (by simpa only [Nat.cast_add] using hq)

end

end Finsler.UniformPacketWindow
