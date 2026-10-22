module

public import Finsler.Topology.PolySplit
public import Finsler.Topology.FixedSampleK
public import Finsler.Topology.SwapWindows

/-! Pieces of crossings from polygon models. For a crossing of the loop space at cuts 0 < a ≤ b,
take polygons with 2M vertices, a descent of their energy commuting with the reversal and the
rotation by M (hence keeping the polygons fixed by the rotation), a time T ≥ 0 and a level
a'' < a². The pair of the polygons below b² relative to the lens set maps to the loop crossing pair
by restriction to the polygon crossing pair followed by sampling, and its part in the fixed
polygons maps to the fixed loop crossing pair in the same way; both maps commute with the
restrictions to the fixed parts. Restriction to the polygon crossing pairs is bijective on K-Borel
cohomology (lens deformation, also inside the fixed polygons) and on reflection Borel cohomology
of the fixed parts; so if sampling is bijective (true for all large M), these maps are too. With
pairwise disjoint invariant open sets of polygons trapping the points not taken below a'' and
windows of their parts, the splitting of the lens pair (`PolySplit`) completes the data of
`OrbitAssembly.Pieces` of the crossing. If the reversal exchanges two halves of each open set,
windows of the actual relative cohomology of the parts suffice (`SwapWindows`). -/

@[expose] public section

namespace Finsler.PolyPieces

open CategoryTheory Set
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.BorelIterate Finsler.BorelK Finsler.BorelCoverK Finsler.BorelLocalK
open Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonModel Finsler.PolygonLoopPairs
open Finsler.PolygonDescent Finsler.PolygonDescentK Finsler.PolygonLensK Finsler.InvPairs
open Finsler.FlowLens Finsler.PairTriple Finsler.LocalCoverK Finsler.SampleK Finsler.FixedSampleK
open Finsler.BorelFixed Finsler.CutPotential Finsler.BorelComparison Finsler.AvoidPoint
open Finsler.LensK Finsler.LensFixed Finsler.PolySplit Finsler.OrbitAssembly Finsler.BorelDeformation
open Finsler.BorelLoop Finsler.PairAdditive Finsler.SwapWindows

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Comp

variable {K L N : InvComplex} {SK : Commuting K} {SL : Commuting L} {SN : Commuting N}

/-- Composition of maps commuting with the second involutions. -/
def commComp (Φ : CommHom SK SL) (Ψ : CommHom SL SN) : CommHom SK SN where
  φ := invHomComp Φ.φ Ψ.φ
  comm_s j x := by
    change Ψ.φ.f j (Φ.φ.f j (SK.s j x)) = SN.s j (Ψ.φ.f j (Φ.φ.f j x))
    rw [Φ.comm_s, Ψ.comm_s]

theorem HK_commComp (Φ : CommHom SK SL) (Ψ : CommHom SL SN) (q : ℕ) (x : HR (borelInv SK) q) :
    HRmap (borelHom (commComp Φ Ψ)) q x = HRmap (borelHom Ψ) q (HRmap (borelHom Φ) q x) := by
  rw [← HRmap_comp]
  exact HRmap_congr (fun _ _ => rfl) q x

/-- A composite of maps bijective on iterated Borel cohomology is bijective. -/
theorem HK_commComp_bijective (Φ : CommHom SK SL) (Ψ : CommHom SL SN) (q : ℕ)
    (hΦ : Function.Bijective (HRmap (borelHom Φ) q))
    (hΨ : Function.Bijective (HRmap (borelHom Ψ) q)) :
    Function.Bijective (HRmap (borelHom (commComp Φ Ψ)) q) := by
  have e : ⇑(HRmap (borelHom (commComp Φ Ψ)) q) =
      ⇑(HRmap (borelHom Ψ) q) ∘ ⇑(HRmap (borelHom Φ) q) :=
    funext (HK_commComp Φ Ψ q)
  rw [e]
  exact hΨ.comp hΦ

/-- A composite of maps bijective on reflection Borel cohomology is bijective. -/
theorem HR_commComp_bijective (Φ : CommHom SK SL) (Ψ : CommHom SL SN) (q : ℕ)
    (hΦ : Function.Bijective (HRmap Φ.φ q)) (hΨ : Function.Bijective (HRmap Ψ.φ q)) :
    Function.Bijective (HRmap (commComp Φ Ψ).φ q) := by
  have e : ⇑(HRmap (commComp Φ Ψ).φ q) = ⇑(HRmap Ψ.φ q) ∘ ⇑(HRmap Φ.φ q) :=
    funext (HRmap_comp Φ.φ Ψ.φ q)
  rw [e]
  exact hΨ.comp hΦ

end Comp

/-- Two composites of three pair maps which agree pull cochains back in the same way. -/
theorem pull_comp3 {P Q₁ Q₂ R₁ R₂ S : TopPair.{0}} (f₁ : P ⟶ Q₁) (f₂ : Q₁ ⟶ Q₂) (f₃ : Q₂ ⟶ S)
    (g₁ : P ⟶ R₁) (g₂ : R₁ ⟶ R₂) (g₃ : R₂ ⟶ S) (h : f₁ ≫ f₂ ≫ f₃ = g₁ ≫ g₂ ≫ g₃) (j : ℕ)
    (x : (cochains S).X j) :
    ((pull f₁).f j).hom (((pull f₂).f j).hom (((pull f₃).f j).hom x)) =
      ((pull g₁).f j).hom (((pull g₂).f j).hom (((pull g₃).f j).hom x)) := by
  rw [← pull_comp_apply f₂ f₃, ← pull_comp_apply f₁, ← pull_comp_apply g₂ g₃,
    ← pull_comp_apply g₁, h]

section Pieces

variable {n : ℕ} (F : ReversibleMetric n) {M : ℕ} [NeZero M]
  (D : Descent (Poly n (2 * M)) (energy F (2 * M)))
  (hDρ : ∀ t w, D.flow t ((kPoly n M).ρ w) = (kPoly n M).ρ (D.flow t w))
  (hDσ : ∀ t w, D.flow t ((kPoly n M).σ w) = (kPoly n M).σ (D.flow t w))
  {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {T : ℝ} (hT : 0 ≤ T)

omit [NeZero M] in
include hDσ in
/-- An equivariant descent keeps the polygons fixed by the rotation by M. -/
theorem flow_fixP (s : ℝ) (w : Poly n (2 * M)) (_ : 0 ≤ s) (hw : w ∈ fixP n M) :
    D.flow s w ∈ fixP n M := by
  change (kPoly n M).σ (D.flow s w) = D.flow s w
  rw [← hDσ]
  exact congrArg (D.flow s) hw

/-- Restriction from the polygons below b² relative to the lens set to the polygon crossing
pair. -/
abbrev lensRes :
    CommHom (mainS (kPoly n M) (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ (a ^ 2)
      (b ^ 2) T)
      (gCommuting (kPoly n M) (sub_sq_mono (F := F) (N := 2 * M) hab ha) (inv_subPoly (a ^ 2))
        (inv_subPoly (b ^ 2))) :=
  gHom (kPoly n M) (sub_sq_mono hab ha) (inv_subPoly (a ^ 2)) (inv_subPoly (b ^ 2))
    (lensY_subset D (a ^ 2) (b ^ 2) T)
    (inv_lensY (kPoly n M) (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ (a ^ 2)
      (b ^ 2) T)
    (inv_subPoly (b ^ 2)) (sub_subset_lensY D (pow_le_pow_left₀ ha.le hab 2) hT) subset_rfl

/-- Restriction from the fixed polygons below b² relative to the lens set to the fixed polygon
crossing pair. -/
abbrev fixLensRes :
    CommHom (fixMainS (kPoly n M) inv_fixP (energy_reversePolygon F) (energy_rotPoly F _) D hDρ
      hDσ (a ^ 2) (b ^ 2) T)
      (gCommuting (kPoly n M) (fixSub_mono (F := F) (M := M) hab ha) (inv_fixSub (a ^ 2))
        (inv_fixSub (b ^ 2))) :=
  gHom (kPoly n M) (fixSub_mono hab ha) (inv_fixSub (a ^ 2)) (inv_fixSub (b ^ 2))
    (lensY_inter_subset (Z := fixP n M) D (a := a ^ 2) (b := b ^ 2) (T := T))
    (inv_inter (inv_lensY (kPoly n M) (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ
      (a ^ 2) (b ^ 2) T) inv_fixP)
    (inv_fixSub (b ^ 2)) (sub_inter_subset_lensY D (pow_le_pow_left₀ ha.le hab 2) hT) subset_rfl

/-- The map from the lens pair of polygons to the loop crossing pair. -/
abbrev toCross := commComp (lensRes F D hDρ hDσ ha hab hT) (sampleHom (F := F) (M := M) ha hab)

/-- The map from the fixed lens pair of polygons to the fixed loop crossing pair. -/
abbrev toFixCross :=
  commComp (fixLensRes F D hDρ hDσ ha hab hT) (sampleFixHom (F := F) (M := M) ha hab)

/-- Sampling fixed loops into the lens pair in two ways. -/
theorem sample_square :
    inclPair (fixLev_mono F hab) (lev_mono F hab) (fixLev_subset_lev F a) (fixLev_subset_lev F b) ≫
      samplePair (M := M) ha hab ≫ inclPair (sub_sq_mono hab ha) (lensY_subset D (a ^ 2) (b ^ 2) T)
        (sub_subset_lensY D (pow_le_pow_left₀ ha.le hab 2) hT) subset_rfl =
    samplePairFix (M := M) ha hab ≫ inclPair (fixSub_mono hab ha)
        (lensY_inter_subset (Z := fixP n M) D)
        (sub_inter_subset_lensY D (pow_le_pow_left₀ ha.le hab 2) hT) subset_rfl ≫
      inclPair (lensY_inter_subset (Z := fixP n M) D) (lensY_subset D (a ^ 2) (b ^ 2) T)
        inter_subset_left inter_subset_left := by
  ext x <;> rfl

/-- The maps to the crossing commute with the restrictions to the fixed parts. -/
theorem toCross_comm (i : ℕ) (x : (gComplex (kPoly n M) (lensY_subset D (a ^ 2) (b ^ 2) T)
      (inv_lensY (kPoly n M) (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ (a ^ 2)
        (b ^ 2) T) (inv_subPoly (b ^ 2))).C i) :
    (crossHom F hab).φ.f i ((toCross F D hDρ hDσ ha hab hT).φ.f i x) =
      (toFixCross F D hDρ hDσ ha hab hT).φ.f i
        ((mainHom (kPoly n M) inv_fixP (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ
          (a ^ 2) (b ^ 2) T).φ.f i x) := by
  show ((pull (inclPair (fixLev_mono F hab) (lev_mono F hab) (fixLev_subset_lev F a)
      (fixLev_subset_lev F b))).f i).hom (((pull (samplePair (M := M) ha hab)).f i).hom
        (((pull (inclPair (sub_sq_mono hab ha) (lensY_subset D (a ^ 2) (b ^ 2) T)
          (sub_subset_lensY D (pow_le_pow_left₀ ha.le hab 2) hT) subset_rfl)).f i).hom x)) =
    ((pull (samplePairFix (M := M) ha hab)).f i).hom
      (((pull (inclPair (fixSub_mono hab ha) (lensY_inter_subset (Z := fixP n M) D)
        (sub_inter_subset_lensY D (pow_le_pow_left₀ ha.le hab 2) hT) subset_rfl)).f i).hom
        (((pull (inclPair (lensY_inter_subset (Z := fixP n M) D)
          (lensY_subset D (a ^ 2) (b ^ 2) T) inter_subset_left inter_subset_left)).f i).hom x))
  exact pull_comp3 _ _ _ _ _ _ (sample_square F D ha hab hT) i x

/-- The map from the lens pair is bijective on K-Borel cohomology if sampling is. -/
theorem toCross_bijective (q : ℕ)
    (hs : Function.Bijective (HRmap (borelHom (sampleHom (F := F) (M := M) ha hab)) q)) :
    Function.Bijective (HRmap (borelHom (toCross F D hDρ hDσ ha hab hT)) q) :=
  HK_commComp_bijective _ _ q
    (HK_lens_bijective (kPoly n M) (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ
      (pow_le_pow_left₀ ha.le hab 2) hT q) hs

/-- The map from the fixed lens pair is bijective on K-Borel cohomology if sampling is. -/
theorem toFixCross_bijective (q : ℕ)
    (hs : Function.Bijective (HRmap (borelHom (sampleFixHom (F := F) (M := M) ha hab)) q)) :
    Function.Bijective (HRmap (borelHom (toFixCross F D hDρ hDσ ha hab hT)) q) :=
  HK_commComp_bijective _ _ q
    (bijective_gHom (kPoly n M) _ _ _ _ _ _ _ _
      (fun m => lens_nativePull_in (Z := fixP n M) D (flow_fixP F D hDσ)
        (pow_le_pow_left₀ ha.le hab 2) hT m) q) hs

/-- The map from the fixed lens pair is bijective on reflection Borel cohomology if sampling
is. -/
theorem toFixCross_bijective_R (q : ℕ)
    (hs : Function.Bijective (HRmap (sampleFixHom (F := F) (M := M) ha hab).φ q)) :
    Function.Bijective (HRmap (toFixCross F D hDρ hDσ ha hab hT).φ q) :=
  HR_commComp_bijective _ _ q
    (BorelInvariance.bijective_HRmap _ _ _ (inclPair_restrict (kPoly n M).ρ _ _ _ _ _ _ _ _)
      (fun m => lens_nativePull_in (Z := fixP n M) D (flow_fixP F D hDσ)
        (pow_le_pow_left₀ ha.le hab 2) hT m) q) hs

/-- **Pieces of a crossing from a polygon model.** If sampling with 2M vertices is bijective on
the K-Borel cohomology of the crossing pair and on the K-Borel and reflection Borel cohomology of
the fixed crossing pair, then for an equivariant descent of the polygons, a time T ≥ 0, a level
a'' < a² and pairwise disjoint invariant open sets of polygons containing every polygon below b²
not taken below a'' in time T, windows of the parts of the lens pair (and of their fixed parts)
give pieces of the crossing. -/
def polyPieces (hg : Continuous (energy F (2 * M))) {a'' : ℝ} (ha'' : a'' < a ^ 2) {J : Type}
    (𝒲 : J → Set (Poly n (2 * M))) (h𝒲K : ∀ j, Inv (kPoly n M) (𝒲 j))
    (h𝒲 : ∀ j, IsOpen (𝒲 j)) (hdis : Pairwise fun i j => Disjoint (𝒲 i) (𝒲 j))
    (htrap : ∀ w, energy F (2 * M) w < b ^ 2 → a'' < energy F (2 * M) (D.flow T w) →
      ∃ j, w ∈ 𝒲 j)
    (hsK : ∀ q, Function.Bijective (HRmap (borelHom (sampleHom (F := F) (M := M) ha hab)) q))
    (hsF : ∀ q, Function.Bijective (HRmap (borelHom (sampleFixHom (F := F) (M := M) ha hab)) q))
    (hsR : ∀ q, Function.Bijective (HRmap (sampleFixHom (F := F) (M := M) ha hab).φ q))
    {c₀ A : ℝ} {S : Finset ℝ} (slope : J → ℝ) (hslope : ∀ j, slope j ∈ S)
    (hwin : ∀ j (i : ℕ), A < |(i : ℝ) - slope j * c₀| →
      ∀ z : HR (partComplex (kPoly n M) (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ
        a'' (a ^ 2) (b ^ 2) T 𝒲 h𝒲K j) i, z = 0)
    (hwinh : ∀ j (l : ℕ), 2 * A < |2 * (l : ℝ) - slope j * c₀| →
      ∀ z : HR (fixPartComplex (kPoly n M) inv_fixP (energy_reversePolygon F)
        (energy_rotPoly F _) D hDρ hDσ a'' (a ^ 2) (b ^ 2) T 𝒲 h𝒲K j) l, z = 0) :
    Pieces F hab c₀ A S where
  M := gComplex (kPoly n M) (lensY_subset D (a ^ 2) (b ^ 2) T)
    (inv_lensY (kPoly n M) (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ (a ^ 2)
      (b ^ 2) T) (inv_subPoly (b ^ 2))
  SM := mainS (kPoly n M) (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ (a ^ 2)
    (b ^ 2) T
  Mh := gComplex (kPoly n M) (lensY_inter_subset (Z := fixP n M) D (a := a ^ 2) (b := b ^ 2)
      (T := T))
    (inv_inter (inv_lensY (kPoly n M) (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ
      (a ^ 2) (b ^ 2) T) inv_fixP) (inv_fixSub (b ^ 2))
  SMh := fixMainS (kPoly n M) inv_fixP (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ
    (a ^ 2) (b ^ 2) T
  trivh := Finsler.SubspaceK.gCommuting_trivial (kPoly n M) _ _ _ fun _ hx => hx.2
  ρM := mainHom (kPoly n M) inv_fixP (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ
    (a ^ 2) (b ^ 2) T
  ι := toCross F D hDρ hDσ ha hab hT
  ιh := toFixCross F D hDρ hDσ ha hab hT
  commι := toCross_comm F D hDρ hDσ ha hab hT
  bijι q := toCross_bijective F D hDρ hDσ ha hab hT q (hsK q)
  bijιh q := toFixCross_bijective F D hDρ hDσ ha hab hT q (hsF q)
  bijιR l := toFixCross_bijective_R F D hDρ hDσ ha hab hT l (hsR l)
  split := polySplit (kPoly n M) inv_fixP (energy_reversePolygon F) (energy_rotPoly F _) D hDρ hDσ
    a'' (a ^ 2) (b ^ 2) T 𝒲 h𝒲K hg ha'' h𝒲 hdis htrap (fun _ hx => hx) slope hslope hwin hwinh

/-- **Pieces of a crossing from a polygon model with ordinary windows.** If the reversal exchanges
the points of each open set 𝒲 j inside and outside an open set U j (the neighbourhoods of the
positive and of the negative circles of an orbit), windows of the actual relative cohomology of
the parts of the lens pair (and of their fixed parts) give pieces of the crossing. -/
def polyPiecesNative (hg : Continuous (energy F (2 * M))) {a'' : ℝ} (ha'' : a'' < a ^ 2)
    {J : Type} (𝒲 : J → Set (Poly n (2 * M))) (h𝒲K : ∀ j, Inv (kPoly n M) (𝒲 j))
    (h𝒲 : ∀ j, IsOpen (𝒲 j)) (hdis : Pairwise fun i j => Disjoint (𝒲 i) (𝒲 j))
    (htrap : ∀ w, energy F (2 * M) w < b ^ 2 → a'' < energy F (2 * M) (D.flow T w) →
      ∃ j, w ∈ 𝒲 j)
    (hsK : ∀ q, Function.Bijective (HRmap (borelHom (sampleHom (F := F) (M := M) ha hab)) q))
    (hsF : ∀ q, Function.Bijective (HRmap (borelHom (sampleFixHom (F := F) (M := M) ha hab)) q))
    (hsR : ∀ q, Function.Bijective (HRmap (sampleFixHom (F := F) (M := M) ha hab).φ q))
    (U : J → Set (Poly n (2 * M))) (hU : ∀ j, IsOpen (U j))
    (hswap : ∀ j, ∀ x ∈ 𝒲 j, (kPoly n M).ρ x ∈ U j ↔ x ∉ U j)
    {c₀ A : ℝ} {S : Finset ℝ} (slope : J → ℝ) (hslope : ∀ j, slope j ∈ S)
    (hwin : ∀ j (i : ℕ), A < |(i : ℝ) - slope j * c₀| →
      ∀ z : native (pairOf (part_sub (inter_subset_inter_right (lensN D a'' T)
        (lensY_subset D (a ^ 2) (b ^ 2) T)) (𝒲 j))) i, z = 0)
    (hwinh : ∀ j (l : ℕ), 2 * A < |2 * (l : ℝ) - slope j * c₀| →
      ∀ z : native (pairOf (part_sub (inter_subset_inter_right (lensN D a'' T)
        (lensY_inter_subset (Z := fixP n M) D (a := a ^ 2) (b := b ^ 2) (T := T))) (𝒲 j))) l,
        z = 0) :
    Pieces F hab c₀ A S :=
  polyPieces F D hDρ hDσ ha hab hT hg ha'' 𝒲 h𝒲K h𝒲 hdis htrap hsK hsF hsR slope hslope
    (fun j i hi z => HR_gComplex_eq_zero (kPoly n M) _ _ _ (hU j) (fun x hx => hswap j x hx.2)
      (hwin j i hi) z)
    (fun j l hl z => HR_gComplex_eq_zero (kPoly n M) _ _ _ (hU j) (fun x hx => hswap j x hx.2)
      (hwinh j l hl) z)

end Pieces

end

end Finsler.PolyPieces
