module

public import Finsler.Topology.LensCutComparisonK

/-! actual ambient deformed lenses give loop-crossing pieces
once local windows are supplied. -/

@[expose] public section

namespace Finsler.AmbientLensPieces

open CategoryTheory Set Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientPenalty
open Finsler.AmbientK Finsler.AmbientNormalizeK Finsler.FixedAmbientNormalize
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelIterate
open Finsler.BorelDeformation Finsler.BorelComparison Finsler.InvPairs Finsler.FlowLens
open Finsler.LensFamily Finsler.LensK Finsler.FixedCutK Finsler.BorelLens
open Finsler.PolySplit Finsler.PolyPieces Finsler.OrbitAssembly Finsler.SubspaceK
open Finsler.SampleK Finsler.FixedSampleK Finsler.PairTriple Finsler.BorelCrossingK
open Finsler.LensFixed

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (M : ℕ) [NeZero M] (F : ReversibleMetric n) {lam : ℝ}
variable {g : Om n (2 * M) → ℝ}
variable (hgρ : ∀ Q, g ((ambK M).ρ Q) = g Q) (hgσ : ∀ Q, g ((ambK M).σ Q) = g Q)
variable (D : Descent (Om n (2 * M)) g)
variable (hDρ : ∀ t Q, D.flow t ((ambK M).ρ Q) = (ambK M).ρ (D.flow t Q))
variable (hDσ : ∀ t Q, D.flow t ((ambK M).σ Q) = (ambK M).σ (D.flow t Q))
variable {l u a b T τ : ℝ} (hl : 0 < l) (hlu : l ≤ u)
variable (hla : l ^ 2 ≤ a) (hab : a ≤ b) (hbu : b ≤ u ^ 2) (hT : 0 ≤ T)
variable (hsa : sub (penW F (2 * M) lam) (l ^ 2) = sub g (l ^ 2))
variable (hsb : sub (penW F (2 * M) lam) (u ^ 2) = sub g (u ^ 2))
variable (hτ : 0 ≤ τ) (hpush : ∀ Q, g Q < u ^ 2 → g (D.flow τ Q) < b)

abbrev lensToWide := LensCutComparisonK.toWide (ambK M) hgρ hgσ D hDρ hDσ hab hT hla hbu
  hsa hsb hτ hpush (pen_ρ M F lam) (pen_σ M F lam)

abbrev lensToWideIn := LensCutComparisonK.toWideIn (ambK M) hgρ hgσ D hDρ hDσ
  (fixOm_invariant M) (fun t Q _ hw => flow_fixed (ambK M) D hDσ t hw)
  hab hT hla hbu hsa hsb hτ hpush (pen_ρ M F lam) (pen_σ M F lam)

abbrev toCross := commComp
  (lensToWide M F hgρ hgσ D hDρ hDσ hla hab hbu hT hsa hsb hτ hpush)
  (AmbientInclusionK.toCross M F lam hl hlu)

abbrev toFixCross := commComp
  (lensToWideIn M F hgρ hgσ D hDρ hDσ hla hab hbu hT hsa hsb hτ hpush)
  (AmbientInclusionK.toFixCross M F lam hl hlu)

theorem toCross_comm (i : ℕ)
    (x : (cochains (pairOf (lensY_subset D a b T))).X i) :
    (crossHom F hlu).φ.f i
        ((toCross M F hgρ hgσ D hDρ hDσ hl hlu hla hab hbu hT hsa hsb hτ hpush).φ.f i x) =
      (toFixCross M F hgρ hgσ D hDρ hDσ hl hlu hla hab hbu hT hsa hsb hτ hpush).φ.f i
        ((mainHom (ambK M) (fixOm_invariant M) hgρ hgσ D hDρ hDσ a b T).φ.f i x) := by
  have h₁ := LensCutComparisonK.toWide_comm (ambK M) hgρ hgσ D hDρ hDσ
    (fixOm_invariant M) (fun t Q _ hw => flow_fixed (ambK M) D hDσ t hw)
    hab hT hla hbu hsa hsb hτ hpush (pen_ρ M F lam) (pen_σ M F lam) i x
  have h₂ := AmbientInclusionK.toCross_comm M F lam hl hlu i
    ((lensToWide M F hgρ hgσ D hDρ hDσ hla hab hbu hT hsa hsb hτ hpush).φ.f i x)
  exact h₂.trans (congrArg ((AmbientInclusionK.toFixCross M F lam hl hlu).φ.f i) h₁)

variable (hlam : 0 ≤ lam) {τl : ℝ} (hτl : 0 ≤ τl)
variable (hpushl : ∀ Q, g Q < a → g (D.flow τl Q) < l ^ 2)

include hlam hτl hpushl in
theorem toCross_bijective (q : ℕ)
    (hs : Function.Bijective (HRmap (borelHom (sampleHom (F := F) (M := M) hl hlu)) q)) :
    Function.Bijective (HRmap (borelHom
      (toCross M F hgρ hgσ D hDρ hDσ hl hlu hla hab hbu hT hsa hsb hτ hpush)) q) :=
  HK_commComp_bijective _ _ q
    (LensCutComparisonK.toWide_bijective (ambK M) hgρ hgσ D hDρ hDσ hab hT hla hbu
      hsa hsb hτ hpush (pen_ρ M F lam) (pen_σ M F lam) hτl hpushl q)
    (AmbientInclusionK.toCross_bijective M F hlam hl hlu q hs)

include hlam hτl hpushl in
theorem toFixCross_bijective (q : ℕ)
    (hs : Function.Bijective (HRmap (borelHom (sampleFixHom (F := F) (M := M) hl hlu)) q)) :
    Function.Bijective (HRmap (borelHom
      (toFixCross M F hgρ hgσ D hDρ hDσ hl hlu hla hab hbu hT hsa hsb hτ hpush)) q) :=
  HK_commComp_bijective _ _ q
    (LensCutComparisonK.toWideIn_bijective (ambK M) hgρ hgσ D hDρ hDσ
      (fixOm_invariant M) (fun t Q _ hw => flow_fixed (ambK M) D hDσ t hw)
      hab hT hla hbu hsa hsb hτ hpush (pen_ρ M F lam) (pen_σ M F lam) hτl hpushl q)
    (AmbientInclusionK.toFixCross_bijective M F hlam hl hlu q hs)

include hlam hτl hpushl in
theorem toFixCross_bijective_R (q : ℕ)
    (hs : Function.Bijective (HRmap (sampleFixHom (F := F) (M := M) hl hlu).φ q)) :
    Function.Bijective (HRmap
      (toFixCross M F hgρ hgσ D hDρ hDσ hl hlu hla hab hbu hT hsa hsb hτ hpush).φ q) :=
  HR_commComp_bijective _ _ q
    (LensCutComparisonK.toWideIn_bijective_R (ambK M) hgρ hgσ D hDρ hDσ
      (fixOm_invariant M) (fun t Q _ hw => flow_fixed (ambK M) D hDσ t hw)
      hab hT hla hbu hsa hsb hτ hpush (pen_ρ M F lam) (pen_σ M F lam) hτl hpushl q)
    (AmbientInclusionK.toFixCross_bijective_R M F hlam hl hlu q hs)

/-- Assemble pieces directly from this ambient descent. The local and fixed windows are
explicit hypotheses; no assertion about windows of arbitrary descents is used. -/
def pieces (hg : Continuous g) {a' : ℝ} (ha' : a' < a) {J : Type}
    (𝒲 : J → Set (Om n (2 * M))) (h𝒲K : ∀ j, Inv (ambK M) (𝒲 j))
    (h𝒲 : ∀ j, IsOpen (𝒲 j)) (hdis : Pairwise fun i j => Disjoint (𝒲 i) (𝒲 j))
    (htrap : ∀ Q, g Q < b → a' < g (D.flow T Q) → ∃ j, Q ∈ 𝒲 j)
    (hsK : ∀ q, Function.Bijective (HRmap (borelHom (sampleHom (F := F) (M := M) hl hlu)) q))
    (hsF : ∀ q, Function.Bijective (HRmap (borelHom (sampleFixHom (F := F) (M := M) hl hlu)) q))
    (hsR : ∀ q, Function.Bijective (HRmap (sampleFixHom (F := F) (M := M) hl hlu).φ q))
    {c₀ A : ℝ} {S : Finset ℝ} (slope : J → ℝ) (hslope : ∀ j, slope j ∈ S)
    (hwin : ∀ j (i : ℕ), A < |(i : ℝ) - slope j * c₀| →
      ∀ z : HR (partComplex (ambK M) hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j) i, z = 0)
    (hwinh : ∀ j (i : ℕ), 2 * A < |2 * (i : ℝ) - slope j * c₀| →
      ∀ z : HR (fixPartComplex (ambK M) (fixOm_invariant M) hgρ hgσ D hDρ hDσ
        a' a b T 𝒲 h𝒲K j) i, z = 0) : Pieces F hlu c₀ A S where
  M := gComplex (ambK M) (lensY_subset D a b T)
    (inv_lensY (ambK M) hgρ hgσ D hDρ hDσ a b T) (inv_sub (ambK M) hgρ hgσ b)
  SM := mainS (ambK M) hgρ hgσ D hDρ hDσ a b T
  Mh := gComplex (ambK M) (lensY_inter_subset (Z := fixOm M) D (a := a) (b := b) (T := T))
    (inv_inter (inv_lensY (ambK M) hgρ hgσ D hDρ hDσ a b T) (fixOm_invariant M))
    (inv_inter (inv_sub (ambK M) hgρ hgσ b) (fixOm_invariant M))
  SMh := fixMainS (ambK M) (fixOm_invariant M) hgρ hgσ D hDρ hDσ a b T
  trivh := gCommuting_trivial (ambK M) _ _ _ fun _ hx => hx.2
  ρM := mainHom (ambK M) (fixOm_invariant M) hgρ hgσ D hDρ hDσ a b T
  ι := toCross M F hgρ hgσ D hDρ hDσ hl hlu hla hab hbu hT hsa hsb hτ hpush
  ιh := toFixCross M F hgρ hgσ D hDρ hDσ hl hlu hla hab hbu hT hsa hsb hτ hpush
  commι := toCross_comm M F hgρ hgσ D hDρ hDσ hl hlu hla hab hbu hT hsa hsb hτ hpush
  bijι q := toCross_bijective M F hgρ hgσ D hDρ hDσ hl hlu hla hab hbu hT hsa hsb hτ hpush
    hlam hτl hpushl q (hsK q)
  bijιh q := toFixCross_bijective M F hgρ hgσ D hDρ hDσ hl hlu hla hab hbu hT hsa hsb hτ hpush
    hlam hτl hpushl q (hsF q)
  bijιR q := toFixCross_bijective_R M F hgρ hgσ D hDρ hDσ hl hlu hla hab hbu hT hsa hsb hτ hpush
    hlam hτl hpushl q (hsR q)
  split := polySplit (ambK M) (fixOm_invariant M) hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K
    hg ha' h𝒲 hdis htrap (fun _ hx => hx) slope hslope hwin hwinh

end

end Finsler.AmbientLensPieces
