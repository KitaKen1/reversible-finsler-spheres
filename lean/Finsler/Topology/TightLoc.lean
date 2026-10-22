module

public import Finsler.Topology.StripK

/-! Splittings at tight cuts suffice. The lens decompositions of crossings live at tight cuts around
a critical level. If for every single crossing of regular cuts 2a ≤ 2b with critical level c₀
there are tight cuts 2a ≤ 2a' < c₀ < 2b' ≤ 2b without critical levels in [2a, 2a'] and
[2b', 2b] and a splitting of the tight crossing pair into pieces (`OrbitAssembly.Pieces`), then
the tight crossing satisfies the windowed localization (`OrbitAssembly.loc_of_pieces`, with the
localization of crossings as anchor), and so does the wide crossing (`StripK`). Hence such tight
splittings give the windowed localization of single crossings, and the local bounds of the
events. -/

@[expose] public section

namespace Finsler.TightLoc

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.CriticalLevels Finsler.CutPotential
open Finsler.TotalExact Finsler.OrbitAssembly Finsler.CrossLocalize Finsler.EventFar
open Finsler.EventSum Finsler.StripK Finsler.CriticalCircles Finsler.CrossingSlopes

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- Splittings of the single crossings at tight cuts, with slopes in S and windows of width A. -/
structure TightSplit where
  S : Finset ℝ
  A : ℝ
  A_nonneg : 0 ≤ A
  split : ∀ (a b : ℝ), 2 * a ≤ 2 * b → 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
    (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ c₀ ∈ crit F ∩ Icc (2 * a) (2 * b),
    ∃ (a' b' : ℝ) (haa : a ≤ a') (hab' : a' ≤ b') (hbb : b' ≤ b),
      (∀ x ∈ Icc (2 * a) (2 * a'), x ∉ crit F) ∧ (∀ x ∈ Icc (2 * b') (2 * b), x ∉ crit F) ∧
      Nonempty (Pieces F (by linarith : 2 * a' ≤ 2 * b') c₀ A S)

/-- **Localization from tight splittings.** -/
theorem loc_of_tightSplit (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (O : TightSplit F) :
    ∀ (a b : ℝ) (hab : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
      (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ c₀ ∈ crit F ∩ Icc (2 * a) (2 * b),
      ∀ q : ℕ, (∀ s ∈ O.S, 2 * O.A + 1 < |(q : ℝ) - s * c₀|) →
        Function.Injective (crossEps F hab q) ∧
          LinearMap.range (crossEps F hab q) = LinearMap.range (cut (crossR F hab) (q / 2)) := by
  intro a b hab ha h2a h2b hsub c₀ hc₀ q hq
  obtain ⟨a', b', haa, hab', hbb, hreg1, hreg2, ⟨P⟩⟩ := O.split a b hab ha h2a h2b hsub c₀ hc₀
  have ha' : 0 < a' := lt_of_lt_of_le ha haa
  have h2a' : 2 * a' ∉ crit F := hreg1 (2 * a') ⟨by linarith, le_rfl⟩
  have h2b' : 2 * b' ∉ crit F := hreg2 (2 * b') ⟨le_rfl, by linarith⟩
  have htight := loc_of_pieces P O.A_nonneg
    (exists_crossRes_bijective F hn hfin ha' (by linarith) h2a' h2b') q hq
  exact (loc_tight_iff_wide F hn ha haa hab' hbb hreg1 hreg2 q (q / 2)).mpr htight

/-- Tight splittings give the windowed localization. -/
theorem windowLoc_of_tightSplit (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (O : TightSplit F) :
    Nonempty (WindowLoc F) :=
  ⟨⟨O.S, 2 * O.A + 1, loc_of_tightSplit F hn hfin O⟩⟩

/-- With the slopes of the pieces among the slopes of the labels and zero, tight splittings give
the windowed localization below the lines. -/
theorem gapLoc_of_tightSplit (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (O : TightSplit F)
    (hS : O.S ⊆ insert (0 : ℝ) ((labels F hfin).image (slope F))) :
    Nonempty (GapLoc F hfin) :=
  ⟨⟨2 * O.A + 1, fun a b hab ha h2a h2b hsub c₀ hc₀ q hq _ =>
    loc_of_tightSplit F hn hfin O a b hab ha h2a h2b hsub c₀ hc₀ q fun s hs => hq s (hS hs)⟩⟩

/-- **The local bounds of the events from tight splittings.** -/
theorem nonempty_eventBounds_of_tightSplit (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    (O : TightSplit F) : Nonempty (EventBounds F) := by
  obtain ⟨L⟩ := windowLoc_of_tightSplit F hn hfin O
  exact nonempty_eventBounds_of_loc F hn hfin L

end

end Finsler.TightLoc
