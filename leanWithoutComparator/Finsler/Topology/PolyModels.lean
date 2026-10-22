module

public import Finsler.Topology.PolyPieces
public import Finsler.Topology.TightLoc

/-! Polygon models of the single crossings. A polygon model of a crossing of the loop space at
cuts 0 < a ≤ b consists of polygons with 2M vertices on which sampling is bijective on the K-Borel
cohomology of the crossing pair and on the K-Borel and reflection Borel cohomology of the fixed
crossing pair, an equivariant descent of the polygon energy, a time T ≥ 0, a level a'' < a²,
pairwise disjoint invariant open sets 𝒲 j of polygons containing every polygon below b² not taken
below a'' in time T, open halves U j exchanged by the reversal, slopes in S, and windows of width
A around the lines through c₀ of the actual relative cohomology of the parts of the lens pair and
of their fixed parts. Such models give pieces of the crossing (`PolyPieces`); models of the single
crossings at tight cuts give tight splittings, hence the windowed localization of the crossings
(`TightLoc`) and the local bounds of the events. What remains for these bounds is the
computation of the windows of the parts, the local critical groups of the orbits of critical
circles. -/

@[expose] public section

namespace Finsler.PolyModels

open Set
open Finsler.Geometry Finsler.Geodesics Finsler.CriticalLevels Finsler.CutPotential
open Finsler.TotalExact Finsler.OrbitAssembly Finsler.CrossLocalize Finsler.EventFar
open Finsler.EventSum Finsler.StripK Finsler.CriticalCircles Finsler.CrossingSlopes
open Finsler.TightLoc Finsler.PolyPieces Finsler.PolySplit Finsler.LensK Finsler.LensFixed
open Finsler.PolygonDescent Finsler.PolygonDescentK Finsler.SampleK Finsler.FixedSampleK
open Finsler.InvPairs Finsler.FlowLens Finsler.BorelLoop Finsler.BorelIterate Finsler.BorelK
open Finsler.BorelComparison Finsler.PairAdditive Finsler.BorelCochain

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- A polygon model of the crossing at cuts 0 < a ≤ b, with windows of width A around the lines
through c₀ with slopes in S. -/
structure PolyModel {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (c₀ A : ℝ) (S : Finset ℝ) where
  M : ℕ
  [neZero : NeZero M]
  D : Descent (Poly n (2 * M)) (energy F (2 * M))
  hDρ : ∀ t w, D.flow t ((kPoly n M).ρ w) = (kPoly n M).ρ (D.flow t w)
  hDσ : ∀ t w, D.flow t ((kPoly n M).σ w) = (kPoly n M).σ (D.flow t w)
  T : ℝ
  hT : 0 ≤ T
  a'' : ℝ
  ha'' : a'' < a ^ 2
  J : Type
  𝒲 : J → Set (Poly n (2 * M))
  h𝒲K : ∀ j, Inv (kPoly n M) (𝒲 j)
  h𝒲 : ∀ j, IsOpen (𝒲 j)
  hdis : Pairwise fun i j => Disjoint (𝒲 i) (𝒲 j)
  htrap : ∀ w, energy F (2 * M) w < b ^ 2 → a'' < energy F (2 * M) (D.flow T w) →
    ∃ j, w ∈ 𝒲 j
  hsK : ∀ q, Function.Bijective (HRmap (borelHom (sampleHom (F := F) (M := M) ha hab)) q)
  hsF : ∀ q, Function.Bijective (HRmap (borelHom (sampleFixHom (F := F) (M := M) ha hab)) q)
  hsR : ∀ q, Function.Bijective (HRmap (sampleFixHom (F := F) (M := M) ha hab).φ q)
  U : J → Set (Poly n (2 * M))
  hU : ∀ j, IsOpen (U j)
  hswap : ∀ j, ∀ x ∈ 𝒲 j, (kPoly n M).ρ x ∈ U j ↔ x ∉ U j
  slope : J → ℝ
  hslope : ∀ j, slope j ∈ S
  hwin : ∀ j (i : ℕ), A < |(i : ℝ) - slope j * c₀| →
    ∀ z : native (pairOf (part_sub (inter_subset_inter_right (lensN D a'' T)
      (lensY_subset D (a ^ 2) (b ^ 2) T)) (𝒲 j))) i, z = 0
  hwinh : ∀ j (l : ℕ), 2 * A < |2 * (l : ℝ) - slope j * c₀| →
    ∀ z : native (pairOf (part_sub (inter_subset_inter_right (lensN D a'' T)
      (lensY_inter_subset (Z := fixP n M) D (a := a ^ 2) (b := b ^ 2) (T := T))) (𝒲 j))) l,
      z = 0

/-- The pieces of a crossing given by a polygon model. -/
def PolyModel.pieces (hn : 1 ≤ n) {a b : ℝ} {hab : a ≤ b} {ha : 0 < a} {c₀ A : ℝ}
    {S : Finset ℝ} (P : PolyModel F hab ha c₀ A S) : Pieces F hab c₀ A S :=
  haveI := P.neZero
  polyPiecesNative F P.D P.hDρ P.hDσ ha hab P.hT (energy_continuous F hn (2 * P.M)) P.ha''
    P.𝒲 P.h𝒲K P.h𝒲 P.hdis P.htrap P.hsK P.hsF P.hsR P.U P.hU P.hswap P.slope P.hslope
    P.hwin P.hwinh

/-- Polygon models of the single crossings at tight cuts. -/
structure PolyTight where
  S : Finset ℝ
  A : ℝ
  A_nonneg : 0 ≤ A
  model : ∀ (a b : ℝ), 2 * a ≤ 2 * b → ∀ ha : 0 < a, 2 * a ∉ crit F → 2 * b ∉ crit F →
    (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ c₀ ∈ crit F ∩ Icc (2 * a) (2 * b),
    ∃ (a' b' : ℝ) (haa : a ≤ a') (hab' : a' ≤ b') (hbb : b' ≤ b),
      (∀ x ∈ Icc (2 * a) (2 * a'), x ∉ crit F) ∧ (∀ x ∈ Icc (2 * b') (2 * b), x ∉ crit F) ∧
      Nonempty (PolyModel F (by linarith : 2 * a' ≤ 2 * b') (by linarith : 0 < 2 * a') c₀ A S)

/-- Polygon models of the single crossings at tight cuts give tight splittings. -/
def tightSplit (hn : 1 ≤ n) (P : PolyTight F) : TightSplit F where
  S := P.S
  A := P.A
  A_nonneg := P.A_nonneg
  split a b hab ha h2a h2b hsub c₀ hc₀ := by
    obtain ⟨a', b', haa, hab', hbb, h1, h2, ⟨Q⟩⟩ := P.model a b hab ha h2a h2b hsub c₀ hc₀
    exact ⟨a', b', haa, hab', hbb, h1, h2, ⟨Q.pieces F hn⟩⟩

/-- **Localization from polygon models.** -/
theorem windowLoc_of_polyTight (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (P : PolyTight F) :
    Nonempty (WindowLoc F) :=
  windowLoc_of_tightSplit F hn hfin (tightSplit F hn P)

/-- With the slopes among the slopes of the labels and zero, polygon models give the windowed
localization below the lines. -/
theorem gapLoc_of_polyTight (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (P : PolyTight F)
    (hS : P.S ⊆ insert (0 : ℝ) ((labels F hfin).image (slope F))) :
    Nonempty (GapLoc F hfin) :=
  gapLoc_of_tightSplit F hn hfin (tightSplit F hn P) hS

/-- **The local bounds of the events from polygon models of the single crossings.** -/
theorem nonempty_eventBounds_of_polyTight (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    (P : PolyTight F) : Nonempty (EventBounds F) :=
  nonempty_eventBounds_of_tightSplit F hn hfin (tightSplit F hn P)

end

end Finsler.PolyModels
