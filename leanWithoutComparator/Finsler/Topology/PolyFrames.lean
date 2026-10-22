module

public import Finsler.Topology.PolyModels
public import Finsler.Topology.PolyOrbits

/-! Orbit frames of the single crossings. An orbit frame of a crossing at cuts 0 < a ≤ b around a
level c₀ consists of polygons with 2M vertices on which sampling is bijective (on the K-Borel
cohomology of the crossing pair and on the K-Borel and reflection Borel cohomology of the fixed
crossing pair), a polygon model, the orbit neighbourhoods of the critical circles of c₀ cut down
to two halves exchanged by the reversal (`PolyOrbits`), an equivariant descent, a time T ≥ 0 and
a level a'' < a² such that the polygons below b² not taken below a'' in time T lie near the orbit
sets. With slopes and windows of the parts, an orbit frame is a polygon model of the crossing
(`PolyModels`). For every single crossing of regular cuts around a critical level c₀ there are
tight cuts around c₀ with orbit frames: sampling is bijective for all large M, the equivariant
descent traps the band into the polygons near the orbit sets (`PolygonLensK`), and the cuts are
chosen within the trapping width. Hence windows of the parts of all orbit frames at tight cuts
around critical levels, the local critical groups of the orbits of critical circles, give polygon
models of the single crossings, hence the windowed localization, GapLoc and the local bounds of
the events. -/

@[expose] public section

namespace Finsler.PolyFrames

open Set Topology
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.SobolevReverse
open Finsler.IntervalSobolev Finsler.BorelLoop Finsler.BorelK Finsler.BorelCoverK
open Finsler.BorelIterate Finsler.BorelCochain Finsler.BorelComparison Finsler.PolygonLoop
open Finsler.PolygonModel Finsler.PolygonDescent Finsler.PolygonDescentK Finsler.PolygonLensK
open Finsler.PolygonOriented Finsler.PolygonLoopPairs Finsler.PolygonSampling Finsler.SampleK
open Finsler.FixedSampleK Finsler.InvPairs Finsler.OrbitNbhd Finsler.OrientedCritical
open Finsler.CriticalCircles Finsler.CriticalLevels Finsler.FlowLens Finsler.PairAdditive
open Finsler.PolyOrbits Finsler.PolyModels Finsler.OrbitAssembly Finsler.LensFixed
open Finsler.PolySplit Finsler.PolyPieces Finsler.TightLoc Finsler.EventSum Finsler.EventFar
open Finsler.CrossingSlopes Finsler.PolygonCritical

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (F : ReversibleMetric n)

/-- An orbit frame of the crossing at cuts 0 < a ≤ b around the level c₀: all data of a polygon
model except slopes and windows, with the polygons near the orbit sets of the critical circles of
c₀ as open sets. -/
structure OrbitFrame {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (c₀ : ℝ) where
  M : ℕ
  [neZero : NeZero M]
  L : ℝ
  P : PolygonModelData F L (2 * M)
  r : ℝ
  Up : Set (Loops n)
  hUp : IsOpen Up
  hhalf : ∀ u, half +ᵥ u ∈ Up ↔ u ∈ Up
  hUU : Disjoint Up (reverseSphere ⁻¹' Up)
  hdis : Pairwise fun s s' : Set (Sphere n) => Disjoint (nbhd F c₀ r s) (nbhd F c₀ r s')
  D : Descent (Poly n (2 * M)) (energy F (2 * M))
  hDρ : ∀ t w, D.flow t ((kPoly n M).ρ w) = (kPoly n M).ρ (D.flow t w)
  hDσ : ∀ t w, D.flow t ((kPoly n M).σ w) = (kPoly n M).σ (D.flow t w)
  T : ℝ
  hT : 0 ≤ T
  a'' : ℝ
  ha'' : a'' < a ^ 2
  htrap : ∀ w, energy F (2 * M) w < b ^ 2 → a'' < energy F (2 * M) (D.flow T w) →
    ∃ s, w ∈ near P (orbitSet (F := F) (c := c₀) r Up s)
  hsK : ∀ q, Function.Bijective (HRmap (borelHom (sampleHom (F := F) (M := M) ha hab)) q)
  hsF : ∀ q, Function.Bijective (HRmap (borelHom (sampleFixHom (F := F) (M := M) ha hab)) q)
  hsR : ∀ q, Function.Bijective (HRmap (sampleFixHom (F := F) (M := M) ha hab).φ q)

attribute [instance] OrbitFrame.neZero

namespace OrbitFrame

variable {F} {a b : ℝ} {hab : a ≤ b} {ha : 0 < a} {c₀ : ℝ} (Fr : OrbitFrame F hab ha c₀)

/-- **Orbit frames with windows are polygon models.** -/
def model {A : ℝ} {S : Finset ℝ} (slope : Set (Sphere n) → ℝ) (hslope : ∀ s, slope s ∈ S)
    (hwin : ∀ s (i : ℕ), A < |(i : ℝ) - slope s * c₀| →
      ∀ z : native (pairOf (part_sub (inter_subset_inter_right (lensN Fr.D Fr.a'' Fr.T)
        (lensY_subset Fr.D (a ^ 2) (b ^ 2) Fr.T))
          (near Fr.P (orbitSet (F := F) (c := c₀) Fr.r Fr.Up s)))) i, z = 0)
    (hwinh : ∀ s (l : ℕ), 2 * A < |2 * (l : ℝ) - slope s * c₀| →
      ∀ z : native (pairOf (part_sub (inter_subset_inter_right (lensN Fr.D Fr.a'' Fr.T)
        (lensY_inter_subset (Z := fixP n Fr.M) Fr.D (a := a ^ 2) (b := b ^ 2) (T := Fr.T)))
          (near Fr.P (orbitSet (F := F) (c := c₀) Fr.r Fr.Up s)))) l, z = 0) :
    PolyModel F hab ha c₀ A S where
  M := Fr.M
  neZero := Fr.neZero
  D := Fr.D
  hDρ := Fr.hDρ
  hDσ := Fr.hDσ
  T := Fr.T
  hT := Fr.hT
  a'' := Fr.a''
  ha'' := Fr.ha''
  J := Set (Sphere n)
  𝒲 s := near Fr.P (orbitSet (F := F) (c := c₀) Fr.r Fr.Up s)
  h𝒲K s := near_inv Fr.P (kInv_orbitSet Fr.hhalf s)
  h𝒲 s := near_isOpen Fr.P (orbitSet_isOpen Fr.hUp s)
  hdis _ _ h := near_disjoint Fr.P (orbitSet_disjoint (Fr.hdis h))
  htrap := Fr.htrap
  hsK := Fr.hsK
  hsF := Fr.hsF
  hsR := Fr.hsR
  U s := near Fr.P (orbitHalf (F := F) (c := c₀) Fr.r Fr.Up s)
  hU s := near_isOpen Fr.P (orbitHalf_isOpen Fr.hUp s)
  hswap s := near_swap Fr.P (orbitHalf_swap Fr.hUU s)
  slope := slope
  hslope := hslope
  hwin := hwin
  hwinh := hwinh

end OrbitFrame

/-- **Orbit frames at tight cuts.** For a crossing of cuts 2a < c₀ < 2b in which c₀ is the only
critical level, there are tight cuts 2a ≤ 2a' < c₀ < 2b' ≤ 2b with an orbit frame. -/
theorem exists_orbitFrame (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b c₀ : ℝ}
    (ha : 0 < a) (h2a : 2 * a < c₀) (h2b : c₀ < 2 * b)
    (hone : ∀ c' ∈ crit F, 2 * a ≤ c' → c' ≤ 2 * b → c' = c₀) :
    ∃ (a' b' : ℝ) (haa : a ≤ a') (hab' : a' ≤ b') (_ : b' ≤ b), 2 * a' < c₀ ∧ c₀ < 2 * b' ∧
      Nonempty (OrbitFrame F (by linarith : 2 * a' ≤ 2 * b') (by linarith : 0 < 2 * a') c₀) := by
  have hc₀ : 0 < c₀ := by linarith
  obtain ⟨M₀, hM₀⟩ := exists_HK_sample_bijective F hn (2 * b)
  obtain ⟨M₁, hM₁⟩ := exists_fixed_sample_bijective F hn (2 * b)
  obtain ⟨Sg⟩ := exists_segmentData F
  obtain ⟨δC, hδC, hC⟩ := Finsler.EnergyDiagonal.exists_ambientMinEnergy_contDiffAt_one F
  have hδ : 0 < min Sg.δ δC := lt_min Sg.pos hδC
  obtain ⟨N₂, hN₂⟩ := exists_sample_spacing F (δ := Sg.δ) (a := 2 * b) Sg.pos
  obtain ⟨c, hc, hedge⟩ := Finsler.PolygonEnergyGlobal.exists_edge_bound F hn
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt ((2 * b + 1) ^ 2 / (c * (min Sg.δ δC) ^ 2))
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = max (max M₀ M₁) (max N₂ N₃) + 1 := ⟨_, rfl⟩
  have : NeZero M := ⟨by omega⟩
  have hNpos : 0 < 2 * M := by omega
  let P : PolygonModelData F (2 * b) (2 * M) :=
    PolygonModelData.mk Sg fun u hu s t hs ht hst =>
      hN₂ (2 * M) (by omega) hNpos u hu s t hs ht hst
  have hshort : ∀ q : ZMod (2 * M) → Sphere n, energy F (2 * M) q ≤ (2 * b) ^ 2 →
      ShortPolygon (min Sg.δ δC) q := by
    intro q hq
    have hlt : energy F (2 * M) q < (2 * b + 1) ^ 2 := lt_of_le_of_lt hq (by nlinarith)
    have hN : (2 * b + 1) ^ 2 / (c * (min Sg.δ δC) ^ 2) < ((2 * M : ℕ) : ℝ) :=
      hN₃.trans_le (Nat.cast_le.mpr (by omega))
    exact short_of_energy_lt hc hδ hedge (le_refl (2 * b + 1)) (by linarith) hN q hlt
  obtain ⟨r, -, -, -, hdisN, hmem, -⟩ := exists_orbit_nhds F hfin hc₀
  obtain ⟨Up, hUp, hpU, hhalf, hUU⟩ := exists_half (F := F) hfin c₀
  have hcrit : ∀ q : ZMod (2 * M) → Sphere n, (2 * a) ^ 2 ≤ energy F (2 * M) q →
      energy F (2 * M) q ≤ (2 * b) ^ 2 → PolyCritical F (2 * M) q →
      ∃ s, q ∈ near P (orbitSet (F := F) (c := c₀) r Up s) := by
    intro q h1 h2 hq
    have hs : ShortPolygon P.δ q := fun i => lt_of_lt_of_le (hshort q h2 i) (min_le_left _ _)
    obtain ⟨s, hs'⟩ := mem_iUnion.mp (crit_subset_orbitSet (F := F) (c := c₀) hpU hmem
      (broken_mem_crit P (by linarith : 0 < 2 * a) (by linarith) hone hs hq h1 h2))
    exact ⟨s, hs, hs'⟩
  obtain ⟨D, hDρ, hDσ, d, hd, htr⟩ := exists_descent_trap F hn (half_shift M)
    (fun P' Q' h => hC P' Q' (lt_of_lt_of_le h (min_le_right _ _))) hshort
    (fun s => near P (orbitSet (F := F) (c := c₀) r Up s))
    (fun s => near_isOpen P (orbitSet_isOpen hUp s))
    (fun s => near_inv P (kInv_orbitSet hhalf s)) hcrit
  -- the tight cuts
  obtain ⟨δ₁, hδ₁def⟩ : ∃ δ₁ : ℝ, δ₁ = min (c₀ - 2 * a) (2 * b - c₀) := ⟨_, rfl⟩
  have hm1 : δ₁ ≤ c₀ - 2 * a := hδ₁def ▸ min_le_left _ _
  have hm2 : δ₁ ≤ 2 * b - c₀ := hδ₁def ▸ min_le_right _ _
  have hδ₁ : 0 < δ₁ := hδ₁def ▸ lt_min (by linarith) (by linarith)
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (δ₁ / 4) (d / (32 * c₀)) := ⟨_, rfl⟩
  have hε : 0 < ε := hεdef ▸ lt_min (by linarith) (div_pos hd (by linarith))
  have hε1 : ε ≤ δ₁ / 4 := hεdef ▸ min_le_left _ _
  have hε2 : ε ≤ d / (32 * c₀) := hεdef ▸ min_le_right _ _
  have hε3 : 32 * c₀ * ε ≤ d := by
    have := mul_le_mul_of_nonneg_left hε2 (by linarith : (0 : ℝ) ≤ 32 * c₀)
    rwa [mul_div_cancel₀ _ (by linarith : (32 * c₀ : ℝ) ≠ 0)] at this
  obtain ⟨a', ha'def⟩ : ∃ a' : ℝ, a' = (c₀ - 2 * ε) / 2 := ⟨_, rfl⟩
  obtain ⟨b', hb'def⟩ : ∃ b' : ℝ, b' = (c₀ + 2 * ε) / 2 := ⟨_, rfl⟩
  have haa : a ≤ a' := by rw [ha'def]; linarith
  have hab' : a' ≤ b' := by rw [ha'def, hb'def]; linarith
  have hbb : b' ≤ b := by rw [hb'def]; linarith
  have h2a' : 2 * a < 2 * a' := by rw [ha'def]; linarith
  have h2a'c : 2 * a' < c₀ := by rw [ha'def]; linarith
  have h2b'c : c₀ < 2 * b' := by rw [hb'def]; linarith
  have hgap : 0 < (2 * a') ^ 2 - (2 * a) ^ 2 := by nlinarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (d / 4) (((2 * a') ^ 2 - (2 * a) ^ 2) / 2) := ⟨_, rfl⟩
  have hη : 0 < η := hηdef ▸ lt_min (by linarith) (by linarith)
  have hη1 : η ≤ d / 4 := hηdef ▸ min_le_left _ _
  have hη2 : η ≤ ((2 * a') ^ 2 - (2 * a) ^ 2) / 2 := hηdef ▸ min_le_right _ _
  have e : (2 * b') ^ 2 - (2 * a') ^ 2 = 8 * c₀ * ε := by rw [ha'def, hb'def]; ring
  have hwidth : (2 * b') ^ 2 - ((2 * a') ^ 2 - η) < d := by linarith
  have hbb2 : (2 * b') ^ 2 ≤ (2 * b) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hpos : (0 : ℝ) < 2 * a' := by linarith
  have hle : 2 * a' ≤ 2 * b' := by linarith
  have hleb : 2 * b' ≤ 2 * b := by linarith
  refine ⟨a', b', haa, hab', hbb, h2a'c, h2b'c, ⟨?_⟩⟩
  exact
    { M := M
      L := 2 * b
      P := P
      r := r
      Up := Up
      hUp := hUp
      hhalf := hhalf
      hUU := hUU
      hdis := hdisN
      D := D
      hDρ := hDρ
      hDσ := hDσ
      T := 1
      hT := zero_le_one
      a'' := (2 * a') ^ 2 - η
      ha'' := by linarith
      htrap := fun w hw hw' => htr ((2 * a') ^ 2 - η) ((2 * b') ^ 2) 1 (by linarith) hbb2 hwidth
        le_rfl w hw hw'.le
      hsK := hM₀ M (by omega) hpos hle hleb
      hsF := (hM₁ M (by omega) hpos hle hleb).1
      hsR := (hM₁ M (by omega) hpos hle hleb).2 }

/-- Windows of the parts of all orbit frames at tight cuts around critical levels, with slopes in
S and width A: the local critical groups of the orbits of critical circles. -/
def FrameWindows (S : Finset ℝ) (A : ℝ) : Prop :=
  ∀ {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (c₀ : ℝ), c₀ ∈ crit F → a < c₀ → c₀ < b →
    ∀ Fr : OrbitFrame F hab ha c₀, ∃ slope : Set (Sphere n) → ℝ, (∀ s, slope s ∈ S) ∧
      (∀ s (i : ℕ), A < |(i : ℝ) - slope s * c₀| →
        ∀ z : native (pairOf (part_sub (inter_subset_inter_right (lensN Fr.D Fr.a'' Fr.T)
          (lensY_subset Fr.D (a ^ 2) (b ^ 2) Fr.T))
            (near Fr.P (orbitSet (F := F) (c := c₀) Fr.r Fr.Up s)))) i, z = 0) ∧
      (∀ s (l : ℕ), 2 * A < |2 * (l : ℝ) - slope s * c₀| →
        ∀ z : native (pairOf (part_sub (inter_subset_inter_right (lensN Fr.D Fr.a'' Fr.T)
          (lensY_inter_subset (Z := fixP n Fr.M) Fr.D (a := a ^ 2) (b := b ^ 2) (T := Fr.T)))
            (near Fr.P (orbitSet (F := F) (c := c₀) Fr.r Fr.Up s)))) l, z = 0)

/-- Windows of the orbit frames give polygon models of the single crossings. -/
def polyTight (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {S : Finset ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hW : FrameWindows F S A) : PolyTight F where
  S := S
  A := A
  A_nonneg := hA
  model a b _ ha h2a h2b hsub c₀ hc₀ := by
    obtain ⟨hc, hc1, hc2⟩ := hc₀
    have hlt1 : 2 * a < c₀ := lt_of_le_of_ne hc1 fun h => h2a (h ▸ hc)
    have hlt2 : c₀ < 2 * b := lt_of_le_of_ne hc2 fun h => h2b (h.symm ▸ hc)
    have hone : ∀ c' ∈ crit F, 2 * a ≤ c' → c' ≤ 2 * b → c' = c₀ :=
      fun c' hc' h1 h2 => hsub ⟨hc', h1, h2⟩ ⟨hc, hc1, hc2⟩
    obtain ⟨a', b', haa, hab', hbb, h1, h2, ⟨Fr⟩⟩ := exists_orbitFrame F hn hfin ha hlt1 hlt2 hone
    obtain ⟨slope, hslope, hwin, hwinh⟩ := hW _ _ c₀ hc h1 h2 Fr
    refine ⟨a', b', haa, hab', hbb, fun x hx hxc => ?_, fun x hx hxc => ?_,
      ⟨Fr.model slope hslope hwin hwinh⟩⟩
    · have := hone x hxc hx.1 (by linarith [hx.2])
      linarith [hx.2]
    · have := hone x hxc (by linarith [hx.1]) hx.2
      linarith [hx.1]

/-- **The local bounds of the events from windows of the orbit frames.** -/
theorem nonempty_eventBounds_of_frameWindows (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    {S : Finset ℝ} {A : ℝ} (hA : 0 ≤ A) (hW : FrameWindows F S A) :
    Nonempty (EventBounds F) :=
  nonempty_eventBounds_of_polyTight F hn hfin (polyTight F hn hfin hA hW)

/-- With the slopes among the slopes of the labels and zero, windows of the orbit frames give the
windowed localization below the lines. -/
theorem gapLoc_of_frameWindows (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {S : Finset ℝ}
    {A : ℝ} (hA : 0 ≤ A) (hW : FrameWindows F S A)
    (hS : S ⊆ insert (0 : ℝ) ((labels F hfin).image (slope F))) :
    Nonempty (GapLoc F hfin) :=
  gapLoc_of_polyTight F hn hfin (polyTight F hn hfin hA hW) hS

end

end Finsler.PolyFrames
