module

public import Finsler.Topology.PacketFinite
public import Finsler.Topology.LevelUniform

/-! Ordinary support windows of each actual packet lens. Finite-dimensionality is obtained
from the actual loop comparison before the model's rank equality and root bound are used.
The window is first stated around the packet shift, then around any index with the stated
index-difference formula. Uniformity over all critical levels and fixed windows are separate. -/

@[expose] public section

namespace Finsler.PacketSupport

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.CriticalLevels
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.FlowLens
open Finsler.BorelComparison Finsler.PairTriple Finsler.LensFamily Finsler.LensContinuation
open Finsler.AmbientPenalty Finsler.CirclePacketFamily Finsler.PacketDeformation
open Finsler.LocalLabelPacket Finsler.PacketFinite Finsler.SampleK Finsler.CircleLabel
open Finsler.LevelBounds

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem outside_shifted_interval {b I R D A q : ℕ} (hb : b = I - R)
    (hR : R ≤ A) (hD : D ≤ A) (hq : (A : ℝ) < |(q : ℝ) - I|) :
    q < b ∨ b + D ≤ q := by
  by_cases hqb : q < b
  · exact Or.inl hqb
  by_cases hbq : b + D ≤ q
  · exact Or.inr hbq
  have hqi : q ≤ I + A := by omega
  have hiq : I ≤ q + A := by omega
  have hqi' : (q : ℝ) ≤ I + A := by exact_mod_cast hqi
  have hiq' : (I : ℝ) ≤ q + A := by exact_mod_cast hiq
  have hbound : |(q : ℝ) - I| ≤ A := abs_le.mpr ⟨by linarith, by linarith⟩
  exact False.elim ((not_lt_of_ge hbound) hq)

variable {n M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
variable {F : ReversibleMetric n} {c η a₀ b₀ : ℝ} {p : ι → Packet n (2 * M)}
variable {Γ : ι → Set (ZMod (2 * M) → Ambient n)}

abbrev localH (G : CirclePacketFamily.Global M F p a₀ b₀) (i : ι) (a b T : ℝ) (q : ℕ) :=
  H (triv (pairOf (partY_sub_partU (fun Q : Om n (2 * M) => deformed M F p Q.1)
    (PacketDeformation.Global.descent G) (p i).big a b T))) q

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

include han hdis hn hfin hη hl hlu hlreg hureg ha₀ hb₀ hTval hs hm hlc hcu in
/-- Each actual packet lens is supported in a finite interval starting at its shift. -/
theorem exists_support (i : ι) {x : ℝ} (hx : 0 < x) (hr : RootBound F hfin c x (p i)) :
    ∃ D : ℕ, ∃ e : ℝ, 0 < e ∧ ∀ a' a b T : ℝ,
      l ^ 2 ≤ a' → a' < a → a < c ^ 2 → c ^ 2 < b → b ≤ u ^ 2 → b - a' < e → 1 ≤ T →
      ∀ q, q < (p i).b ∨ (p i).b + D ≤ q → ∀ z : localH G i a b T q, z = 0 := by
  obtain ⟨ef, hef, hfinite⟩ := exists_local_finite han hdis G hn hfin hη hl hlu hlreg hureg
    ha₀ hb₀ hTval hs
  obtain ⟨em, hem, hmodel⟩ := PacketDeformation.Global.lens_model han hdis G hn hη hm
    ha₀ hb₀ hlc hcu i
  obtain ⟨er, her, hroot⟩ := hr
  obtain ⟨hroot0, _, _, _⟩ := isoBand_spec F hfin hx
  obtain ⟨hroota, hrootb⟩ := isoBand_regular F hfin hx
  obtain ⟨D, hrootfinite, hrootzero⟩ := cross_finite F hn hfin hroot0 (isoBand_le F hfin x)
    hroota hrootb
  let e := min ef (min em er)
  have he : 0 < e := lt_min hef (lt_min hem her)
  refine ⟨D, e, he, fun a' a b T hla' ha' hac hcb hbu hw hT q hq z => ?_⟩
  have hwf : b - a' < ef := hw.trans_le (min_le_left _ _)
  have hwm : b - a < em := by
    have h := hw.trans_le ((min_le_right ef (min em er)).trans (min_le_left em er))
    linarith
  have hwr : b - a < er := by
    have h := hw.trans_le ((min_le_right ef (min em er)).trans (min_le_right em er))
    linarith
  obtain ⟨hrank, hlow⟩ := hmodel a b T hT hac hcb hwm
  rcases hq with hq | hq
  · exact hlow q hq z
  · have hbq : (p i).b ≤ q := by omega
    let j := q - (p i).b
    have hj : D ≤ j := by dsimp [j]; omega
    have hjq : j + (p i).b = q := by dsimp [j]; omega
    haveI := hrootfinite j
    haveI : Subsingleton (H (triv (pairOf (lev_mono F (isoBand_le F hfin x)))) j) :=
      ⟨fun y y' => (hrootzero j hj y).trans (hrootzero j hj y').symm⟩
    have hrank0 : Module.finrank (ZMod 2)
        (H (triv (pairOf (lev_mono F (isoBand_le F hfin x)))) j) = 0 :=
      Module.finrank_eq_zero_of_subsingleton _ _
    have hr0 : (p i).r a b T j = 0 := by
      have h := hroot a b T hT hac hcb hwr j (hrootfinite j)
      rw [hrank0] at h
      omega
    have hz := hrank j
    rw [hjq, hr0] at hz
    haveI := hfinite a' a b T hla' ha' hac hcb hbu hwf hT i q
    haveI : Subsingleton (localH G i a b T q) :=
      (Module.finrank_zero_iff (R := ZMod 2) (M := localH G i a b T q)).mp hz
    exact Subsingleton.elim _ _

include han hdis hn hfin hη hl hlu hlreg hureg ha₀ hb₀ hTval hs hm hlc hcu in
/-- The index-difference formula converts support of the actual local group to an index window. -/
theorem exists_index_window (i : ι) {x : ℝ} (hx : 0 < x) (hr : RootBound F hfin c x (p i))
    {I R : ℕ} (hb : (p i).b = I - R) :
    ∃ A : ℕ, ∃ e : ℝ, 0 < e ∧ ∀ a' a b T : ℝ,
      l ^ 2 ≤ a' → a' < a → a < c ^ 2 → c ^ 2 < b → b ≤ u ^ 2 → b - a' < e → 1 ≤ T →
      ∀ q : ℕ, (A : ℝ) < |(q : ℝ) - I| → ∀ z : localH G i a b T q, z = 0 := by
  obtain ⟨D, e, he, hsupport⟩ := exists_support han hdis G hn hfin hη hl hlu hlreg hureg
    ha₀ hb₀ hTval hs hm hlc hcu i hx hr
  refine ⟨max R D, e, he, fun a' a b T hla' ha' hac hcb hbu hw hT q hq => ?_⟩
  exact hsupport a' a b T hla' ha' hac hcb hbu hw hT q
    (outside_shifted_interval hb (le_max_left _ _) (le_max_right _ _) hq)

end

end Finsler.PacketSupport
