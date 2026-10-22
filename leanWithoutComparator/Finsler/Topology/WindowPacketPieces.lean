module

public import Finsler.Topology.PacketSlopeWindows
public import Finsler.Topology.PacketPieces

/-! The actual coupled packets supply both orbit-part windows and trapping. The Pieces
construction below takes sampling and regular wide cuts, with no local-window hypotheses. -/

@[expose] public section

namespace Finsler.WindowPacketPieces

open CategoryTheory Set Module Finsler.Geometry Finsler.SphereGeometry Finsler.Geodesics
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.CrossingSlopes
open Finsler.LocalLabelPacket Finsler.CirclePacketFamily Finsler.ActualWindowCollar
open Finsler.PacketDeformation Finsler.PacketSymmetry Finsler.AmbientPenalty Finsler.AmbientK
open Finsler.FixedAmbientNormalize Finsler.InvPairs Finsler.PolySplit Finsler.FlowLens
open Finsler.LensContinuation Finsler.LensFamily Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.PairTriple Finsler.BorelComparison Finsler.BorelIterate
open Finsler.SampleK Finsler.FixedSampleK Finsler.OrbitAssembly

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem finite_width {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i, e ≤ f i := by
  classical
  have h : ∀ t : Finset ι, ∃ e : ℝ, 0 < e ∧ ∀ i ∈ t, e ≤ f i := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i t hi ih =>
      obtain ⟨e, he, ht⟩ := ih
      refine ⟨min e (f i), lt_min he (hf i), fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (ht j hj)
  obtain ⟨e, he, hall⟩ := h Finset.univ
  exact ⟨e, he, fun i => hall i (Finset.mem_univ i)⟩

variable {n M : ℕ} [NeZero M] {ι : Type} [Fintype ι]
variable {F : ReversibleMetric n} {hfin : (primeImages F).Finite}
variable {s : ι → Set (Sphere n)} {hs : ∀ i, s i ∈ primeImages F} {k : ι → ℕ}
variable {A : ℕ} {c η a₀ b₀ l u : ℝ}

theorem exists_pieces (B : Data F hfin s hs k A M c η a₀ b₀ (l ^ 2) (u ^ 2))
    (hn : 1 ≤ n) (hη : 0 ≤ η) (hA : Finsler.RootCatalogue.Bounds F hfin A)
    (hk : ∀ i, 0 < k i)
    (hkc : ∀ i, (k i : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
      (chosen F (s i) (hs i)).loop) = c)
    (hl : 0 < l) (hlu : l ≤ u) (hlreg : l ∉ crit F) (hureg : u ∉ crit F)
    (ha : a₀ ≤ l ^ 2 - η) (hb : u ^ 2 + η ≤ b₀)
    (hlc : l ^ 2 < c ^ 2) (hcu : c ^ 2 < u ^ 2)
    (hsO : ∀ q, Function.Bijective (nativePull (samplePair (F := F) (M := M) hl hlu) q))
    (hsK : ∀ q, Function.Bijective (HRmap (borelHom (sampleHom (F := F) (M := M) hl hlu)) q))
    (hsF : ∀ q, Function.Bijective (HRmap (borelHom (sampleFixHom (F := F) (M := M) hl hlu)) q))
    (hsR : ∀ q, Function.Bijective (HRmap (sampleFixHom (F := F) (M := M) hl hlu).φ q)) :
    ∃ e : ℝ, 0 < e ∧ ∀ a' a b T : ℝ,
      l ^ 2 ≤ a' → a' < a → a < c ^ 2 → c ^ 2 < b → b ≤ u ^ 2 → b - a' < e → 1 ≤ T →
      Nonempty (Pieces F hlu c ((A + n : ℕ) : ℝ)
        (insert (0 : ℝ) ((labels F hfin).image (slope F)))) := by
  classical
  let P := packetFamily M B.d
  let D := PacketDeformation.Global.descent B.global
  have han := family_analytic M F hfin s hs k (fun i => M / k i) B.spec
  have hm := family_model M F hfin s hs k (fun i => M / k i) B.spec
  have hgρ := deformed_rho B.spec B.kn
  have hgσ := deformed_sigma B.spec B.kn
  have hgc := deformed_continuous han hn
  have hO : ∀ i : ι, ∃ e : ℝ, 0 < e ∧ ∀ a' a b T : ℝ,
      l ^ 2 ≤ a' → a' < a → a < c ^ 2 → c ^ 2 < b → b ≤ u ^ 2 → b - a' < e → 1 ≤ T →
      ∀ q : ℕ, ((A + n : ℕ) : ℝ) < |(q : ℝ) - slope F (s i, true) * c| →
        ∀ z : lensH D (B.d i).big a b T q, z = 0 := by
    intro i
    exact Finsler.UniformPacketWindow.circle_slope_window han B.disjoint B.global hn hfin hη
      hl hlu hlreg hureg ha hb B.collar hsO hm hlc hcu hA (i, true) (s i, true)
      ((mem_labels F hfin (s i, true)).mpr (hs i)) (hk i) (B.spec i).1 (hkc i)
  have hF := fun i => Finsler.PacketSlopeWindows.fixed_slope_window B hn hη hk hkc ha hb hlc hcu i
  choose eO heO hOw using hO
  choose eF heF hFw using hF
  obtain ⟨ew, hew, hwe⟩ := finite_width (fun i => min (eO i) (eF i))
    (fun i => lt_min (heO i) (heF i))
  obtain ⟨et, het, htrap⟩ := PacketDeformation.Global.exists_trap han B.disjoint B.global hn hη ha hb
  have hbig := Finsler.PacketFinite.big_disjoint han B.disjoint
  have hhalf : ∀ i, Disjoint (B.d i).big ((ambK M).ρ ⁻¹' (B.d i).big) :=
    fun i => @hbig (i, true) (i, false) (by simp)
  have hInv := orbitBig_invariant B.spec B.kn
  have hopen := orbitBig_open B.spec
  have hdis : Pairwise fun i j => Disjoint (orbitBig B.d i) (orbitBig B.d j) := by
    intro i j hij
    have hd : ∀ o₁ o₂ : Bool, Disjoint (P (i, o₁)).big (P (j, o₂)).big := by
      intro o₁ o₂
      exact @hbig _ _ (fun he => hij (Prod.mk.inj he).1)
    exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hd true true, hd true false⟩,
      disjoint_union_right.mpr ⟨hd false true, hd false false⟩⟩
  let line : ι → ℝ := fun i => slope F (s i, true)
  have hline : ∀ i, line i ∈ insert (0 : ℝ) ((labels F hfin).image (slope F)) :=
    fun i => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      ((mem_labels F hfin (s i, true)).mpr (hs i)))
  refine ⟨min et ew, lt_min het hew, fun a' a b T hla' ha' hac hcb hbu hw hT => ?_⟩
  have hwT : b - a' < et := hw.trans_le (min_le_left _ _)
  have hwW : b - a' < ew := hw.trans_le (min_le_right _ _)
  have hcover : ∀ Q : Om n (2 * M), deformed M F P Q.1 < b →
      a' < deformed M F P (D.flow T Q).1 → ∃ i, Q ∈ orbitBig B.d i := by
    intro Q hQ hflow
    obtain ⟨⟨i, o⟩, hi⟩ := htrap a' b T hla' hbu hwT hT Q hQ hflow.le
    refine ⟨i, ?_⟩
    cases o
    · exact Or.inr hi
    · exact Or.inl hi
  apply Finsler.PacketPieces.nonempty_pieces han B.disjoint B.global hn hη hgρ hgσ
    hl hlu (hla'.trans ha'.le) hac hcb hbu ha hb B.collar ha'
    (zero_le_one.trans hT) (orbitBig B.d) hInv hopen hdis hcover hsK hsF hsR line hline
  · intro i q hq x
    have hwo : b - a' < eO i := hwW.trans_le ((hwe i).trans (min_le_left _ _))
    exact Finsler.HalfPartWindows.part_eq_zero (ambK M) hgρ hgσ D B.global.rho B.global.sigma
      ha' (orbitBig B.d) hInv i ((B.spec i).1.1.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (hhalf i) rfl hgc (hOw i a' a b T hla' ha' hac hcb hbu hwo hT q hq) x
  · intro i q hq x
    have hwf : b - a < eF i := by
      have h := hwW.trans_le ((hwe i).trans (min_le_right _ _))
      linarith
    exact Finsler.HalfPartWindows.fixed_part_eq_zero (ambK M) hgρ hgσ D B.global.rho B.global.sigma
      ha' (orbitBig B.d) hInv i ((B.spec i).1.1.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (hhalf i) rfl (fixOm_invariant M) hgc (hFw i a b T hT hac hcb hwf q hq) x

end

end Finsler.WindowPacketPieces
