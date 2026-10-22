module

public import Finsler.Topology.WindowPacketPieces
public import Finsler.Topology.TightLoc

/-! Actual isolated crossings admit pieces with uniform slope windows. All sampling,
collar, trapping and local-window inputs are constructed. This supplies EventBounds. -/

@[expose] public section

namespace Finsler.ActualWindowPieces

open Set Module Finsler.Geometry Finsler.SphereGeometry Finsler.Geodesics
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.CrossingSlopes
open Finsler.LocalLabelPacket Finsler.CirclePacketFamily Finsler.ActualWindowCollar
open Finsler.PolygonLoopPairs Finsler.SampleK Finsler.FixedSampleK
open Finsler.BorelCochain Finsler.BorelComparison Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.OrbitAssembly Finsler.TightLoc

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

theorem exists_pieces (F : ReversibleMetric n) (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    {A : ℕ} (hA : Finsler.RootCatalogue.Bounds F hfin A) (hAv : Available F hfin A)
    {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hac : a₀ < c) (hcb : c < b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c) :
    ∃ (l u : ℝ) (hlu : l ≤ u), a₀ < l ∧ l < c ∧ c < u ∧ u < b₀ ∧
      Nonempty (Pieces F hlu c ((A + n : ℕ) : ℝ)
        (insert (0 : ℝ) ((labels F hfin).image (slope F)))) := by
  classical
  have hc : 0 < c := ha₀.trans hac
  let l := (a₀ + c) / 2
  let u := (c + b₀) / 2
  have hl₀ : 0 < l := by dsimp [l]; linarith
  have ha₀l : a₀ < l := by dsimp [l]; linarith
  have hlc : l < c := by dsimp [l]; linarith
  have hcu : c < u := by dsimp [u]; linarith
  have hub₀ : u < b₀ := by dsimp [u]; linarith
  have hu₀ : 0 < u := hc.trans hcu
  have hlu : l ≤ u := (hlc.trans hcu).le
  have h₁ : a₀ ^ 2 < l ^ 2 := pow_lt_pow_left₀ ha₀l ha₀.le two_ne_zero
  have h₂ : l ^ 2 < c ^ 2 := pow_lt_pow_left₀ hlc hl₀.le two_ne_zero
  have h₃ : c ^ 2 < u ^ 2 := pow_lt_pow_left₀ hcu hc.le two_ne_zero
  have h₄ : u ^ 2 < b₀ ^ 2 := pow_lt_pow_left₀ hub₀ hu₀.le two_ne_zero
  let η := min ((l ^ 2 - a₀ ^ 2) / 2) (min ((b₀ ^ 2 - u ^ 2) / 2)
    (min ((c ^ 2 - l ^ 2) / 2) ((u ^ 2 - c ^ 2) / 2)))
  have hη : 0 < η := lt_min (by linarith) (lt_min (by linarith)
    (lt_min (by linarith) (by linarith)))
  have hη₁ : η ≤ (l ^ 2 - a₀ ^ 2) / 2 := min_le_left _ _
  have hη₂ : η ≤ (b₀ ^ 2 - u ^ 2) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hη₃ : η ≤ (c ^ 2 - l ^ 2) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη₄ : η ≤ (u ^ 2 - c ^ 2) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨k, hk, L, M₀, hL, _, hdata⟩ := hAv ha₀ hac hcb hone
  obtain ⟨NO, hNO⟩ := exists_sample_bijective F hn b₀
  obtain ⟨NK, hNK⟩ := exists_HK_sample_bijective F hn b₀
  obtain ⟨NF, hNF⟩ := exists_fixed_sample_bijective F hn b₀
  let Q := M₀ + NO + NK + NF + 1
  let M := L * Q
  have hQ : 0 < Q := by dsimp [Q]; omega
  have hQM : Q ≤ M := by dsimp [M]; nlinarith
  have hM : 0 < M := hQ.trans_le hQM
  have : NeZero M := ⟨hM.ne'⟩
  have hM₀ : M₀ ≤ M := by dsimp [Q] at hQM; omega
  have hNO' : NO ≤ 2 * M := by dsimp [Q] at hQM; omega
  have hNK' : NK ≤ M := by dsimp [Q] at hQM; omega
  have hNF' : NF ≤ M := by dsimp [Q] at hQM; omega
  obtain ⟨B⟩ := hdata M hM₀ (dvd_mul_right L Q) hη
    (by linarith : l ^ 2 + η < c ^ 2) (by linarith : c ^ 2 < u ^ 2 - η)
  have hsO : ∀ q, Function.Bijective (nativePull (samplePair (F := F) (M := M) hl₀ hlu) q) :=
    fun q => Finsler.LensK.nativePull_bijective_of_Hmap _ q (hNO (2 * M) hNO' hl₀ hlu hub₀.le q)
  obtain ⟨hsF, hsR⟩ := hNF M hNF' hl₀ hlu hub₀.le
  obtain ⟨e, he, hp⟩ := Finsler.WindowPacketPieces.exists_pieces B hn hη.le hA
    (fun i => (hk i).1) (fun i => (hk i).2) hl₀ hlu
    (fun h => hlc.ne (hone l h ha₀l.le (hlc.le.trans hcb.le)))
    (fun h => hcu.ne' (hone u h (hac.le.trans hcu.le) hub₀.le))
    (by linarith : a₀ ^ 2 ≤ l ^ 2 - η) (by linarith : u ^ 2 + η ≤ b₀ ^ 2)
    h₂ h₃ hsO (hNK M hNK' hl₀ hlu hub₀.le) hsF hsR
  let δ := min (e / 4) (min ((c ^ 2 - l ^ 2) / 4) ((u ^ 2 - c ^ 2) / 4))
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδ₁ : δ ≤ e / 4 := min_le_left _ _
  have hδ₂ : δ ≤ (c ^ 2 - l ^ 2) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₃ : δ ≤ (u ^ 2 - c ^ 2) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨l, u, hlu, ha₀l, hlc, hcu, hub₀, ?_⟩
  exact hp (c ^ 2 - 2 * δ) (c ^ 2 - δ) (c ^ 2 + δ) 1
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) le_rfl

theorem exists_tight_split (F : ReversibleMetric n) (hn : 1 ≤ n) (hfin : (primeImages F).Finite) :
    ∃ O : TightSplit F, O.S = insert (0 : ℝ) ((labels F hfin).image (slope F)) := by
  obtain ⟨A, hA, hAv⟩ := exists_uniform_collar F hn hfin
  refine ⟨{
    S := insert (0 : ℝ) ((labels F hfin).image (slope F))
    A := ((A + n : ℕ) : ℝ)
    A_nonneg := by positivity
    split := ?_ }, rfl⟩
  intro a b hab ha hareg hbreg hsub c hc
  have hac : 2 * a < c := lt_of_le_of_ne hc.2.1 (fun h => hareg (h ▸ hc.1))
  have hcb : c < 2 * b := lt_of_le_of_ne hc.2.2 (fun h => hbreg (h.symm ▸ hc.1))
  have hone : ∀ x ∈ crit F, 2 * a ≤ x → x ≤ 2 * b → x = c :=
    fun x hx h1 h2 => hsub ⟨hx, h1, h2⟩ hc
  obtain ⟨l, u, hlu, hal, hlc, hcu, hub, hp⟩ := exists_pieces F hn hfin hA hAv
    (by linarith : 0 < 2 * a) hac hcb hone
  refine ⟨l / 2, u / 2, by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
  · intro x hx hcrit
    have he := hone x hcrit hx.1 (by linarith [hx.2])
    linarith [hx.2]
  · intro x hx hcrit
    have he := hone x hcrit (by linarith [hx.1]) hx.2
    linarith [hx.1]
  · have hl : 2 * (l / 2) = l := by ring
    have hu : 2 * (u / 2) = u := by ring
    simpa only [hl, hu] using hp

theorem nonempty_eventBounds (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) : Nonempty (Finsler.EventSum.EventBounds F) := by
  obtain ⟨O, _⟩ := exists_tight_split F hn hfin
  exact Finsler.TightLoc.nonempty_eventBounds_of_tightSplit F hn hfin O

theorem nonempty_gapLoc (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) : Nonempty (Finsler.EventFar.GapLoc F hfin) := by
  obtain ⟨O, hS⟩ := exists_tight_split F hn hfin
  exact Finsler.TightLoc.gapLoc_of_tightSplit F hn hfin O (by rw [hS])

end

end Finsler.ActualWindowPieces
