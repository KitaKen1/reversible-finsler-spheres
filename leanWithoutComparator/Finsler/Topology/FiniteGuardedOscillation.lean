module

public import Finsler.Topology.CompactRectangleOscillation

/-! One factorwise rectangle scale for finitely many guarded partial tests.
Each distance test is continuous on the compact outer parameter tube. Its
tested length need only be continuous on its own closed intermediate tube.
A near witness first puts the whole parent in that tube; a high tested
length witness then controls the entire parent, simultaneously for every
selected test and below any previously fixed positive cover scale. -/

@[expose] public section
namespace Finsler.FiniteGuardedOscillation

open Set Finsler.PairDistanceCover

noncomputable section
set_option maxHeartbeats 600000

variable {Z ι : Type*} [PseudoMetricSpace Z]

def guarded (K : Set Z) (d : Z → ℝ) (ρ : ℝ) : Set Z := K ∩ {z | d z ≤ 2 * ρ}

theorem compact_guarded {K : Set Z} (hK : IsCompact K) (d : Z → ℝ)
    (hd : ContinuousOn d K) (ρ : ℝ) : IsCompact (guarded K d ρ) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun z : K => d z.val) := hd.domRestrict
  have hs : IsCompact {z : K | d z.val ≤ 2 * ρ} :=
    (isClosed_le hc continuous_const).isCompact
  have hi := hs.image (continuous_subtype_val : Continuous (Subtype.val : K → Z))
  have he : Subtype.val '' {z : K | d z.val ≤ 2 * ρ} = guarded K d ρ := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property, hw⟩
    · intro hz
      exact ⟨⟨z, hz.1⟩, hz.2, rfl⟩
  rwa [he] at hi

theorem exists_simultaneous_radius (s : Finset ι) (K : ι → Set Z)
    (hK : ∀ i ∈ s, IsCompact (K i)) (f : ι → Z → ℝ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (K i)) (ε : ι → ℝ)
    (hε : ∀ i ∈ s, 0 < ε i) :
    ∃ δ > 0, ∀ i ∈ s, ∀ z ∈ K i, ∀ w ∈ K i,
      dist z w < δ → |f i z - f i w| < ε i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδ, hb⟩ := ih
      (fun i hi => hK i (Finset.mem_insert_of_mem hi))
      (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hε i (Finset.mem_insert_of_mem hi))
    obtain ⟨δa, hδa, hba⟩ := (Metric.uniformContinuousOn_iff.mp
      ((hK a (Finset.mem_insert_self a s)).uniformContinuousOn_of_continuous
        (hf a (Finset.mem_insert_self a s)))) (ε a) (hε a (Finset.mem_insert_self a s))
    refine ⟨min δa δ, lt_min hδa hδ, ?_⟩
    intro i hi z hz w hw hzw
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simpa only [Real.dist_eq] using hba z hz w hw (hzw.trans_le (min_le_left _ _))
    · exact hb i hi z hz w hw (hzw.trans_le (min_le_right _ _))

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem exists_rectangle_adequacy (s : Finset ι) {K : Set (X × Y)} (hK : IsCompact K)
    (d f : ι → X × Y → ℝ) (ρ : ι → ℝ)
    (hρ : ∀ i ∈ s, 0 < ρ i) (hd : ∀ i ∈ s, ContinuousOn (d i) K)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (guarded K (d i) (ρ i)))
    {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∃ η > 0, η ≤ a ∧ ∀ (cx : X) (cy : Y) (P : Set (X × Y)),
      P ⊆ cover id η cx ×ˢ cover id η cy → P ⊆ K →
      ∀ i ∈ s, (∃ w ∈ P, d i w < ρ i) →
        (∀ z ∈ P, d i z < 2 * ρ i) ∧
        (∀ L : ℝ, (∃ w ∈ P, L ≤ f i w) → ∀ z ∈ P, L - ε ≤ f i z) := by
  obtain ⟨δd, hδd, hdb⟩ := exists_simultaneous_radius s (fun _ => K)
    (fun _ _ => hK) d hd ρ hρ
  obtain ⟨δf, hδf, hfb⟩ := exists_simultaneous_radius s
    (fun i => guarded K (d i) (ρ i))
    (fun i hi => compact_guarded hK (d i) (hd i hi) (ρ i)) f hf (fun _ => ε) (fun _ _ => hε)
  let η := min (min δd δf / 4) a
  have hη : 0 < η := lt_min (div_pos (lt_min hδd hδf) (by norm_num)) ha
  have hdist {cx : X} {cy : Y} {z w : X × Y}
      (hz : z ∈ cover id η cx ×ˢ cover id η cy)
      (hw : w ∈ cover id η cx ×ˢ cover id η cy) : dist z w < min δd δf := by
    have hx := same_member id hz.1 hw.1
    have hy := same_member id hz.2 hw.2
    have hηle : η ≤ min δd δf / 4 := min_le_left _ _
    change dist z.1 w.1 < 2 * η at hx
    change dist z.2 w.2 < 2 * η at hy
    rw [Prod.dist_eq]
    apply max_lt <;> linarith [lt_min hδd hδf]
  refine ⟨η, hη, min_le_right _ _, ?_⟩
  intro cx cy P hrect hPK i hi hw
  obtain ⟨w, hwP, hdw⟩ := hw
  have hnear : ∀ z ∈ P, d i z < 2 * ρ i := by
    intro z hz
    have h := (abs_lt.mp (hdb i hi z (hPK hz) w (hPK hwP)
      ((hdist (hrect hz) (hrect hwP)).trans_le (min_le_left _ _)))).2
    linarith
  refine ⟨hnear, ?_⟩
  intro L hL z hz
  obtain ⟨v, hv, hLv⟩ := hL
  have hzg : z ∈ guarded K (d i) (ρ i) := ⟨hPK hz, (hnear z hz).le⟩
  have hvg : v ∈ guarded K (d i) (ρ i) := ⟨hPK hv, (hnear v hv).le⟩
  have h := (abs_lt.mp (hfb i hi z hzg v hvg
    ((hdist (hrect hz) (hrect hv)).trans_le (min_le_right _ _)))).1
  linarith

end
end Finsler.FiniteGuardedOscillation
