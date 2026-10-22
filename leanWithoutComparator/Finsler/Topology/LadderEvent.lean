module

public import Finsler.Topology.FixedLadder
public import Finsler.Topology.GradedLadder

/-! The change of the potential of a cutoff across a crossing, for the actual groups. For a pair
(t, s) of invariant sets of loops with a pair (t₀, s₀) of loops fixed by the half rotation
inside, the normalized restrictions of a degree q map the K-Borel cohomology of (t, s) to the
reflection Borel cohomology of (t₀, s₀) in every root degree. With P the truncation to root
degrees at most j, the potential of the cutoff j in the degrees q, q + 1 is

  Φ = (dim L − dim PE_{q+1}) + (dim L − dim PE_q) + (dim A_{q+1} − dim PE_{q+1}),

L = image of P on the product of the reflection groups, PE = P(image of the normalized
restriction), A = K-Borel cohomology (`GradedLadder.gphi`).

For a triple s ⊆ t ⊆ u with a fixed triple s₀ ⊆ t₀ ⊆ u₀ inside, the normalized restrictions map
the K-Borel exact sequence of (u, t, s) to the reflection Borel exact sequence of (u₀, t₀, s₀),
and all squares commute (`FixedLadder`). Hence the two statements of `GradedLadder` apply: at a
far cutoff (the fixed connecting map vanishes on root degree j, the normalized restriction of
the crossing is bijective onto the root degrees at most j in degree q + 1, covers them in degree
q, and is injective into them in degree q + 2) the potential of (u, s) is at most that of
(t, s); in general the two potentials differ by at most six times a bound for the dimensions of
the total fixed crossing group and of the K-Borel crossing groups of the degrees q + 1 and
q + 2. The hypotheses on the crossing groups are local statements and are not proved here. -/

@[expose] public section

namespace Finsler.LadderEvent

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelExact Finsler.BorelFreeK
open Finsler.AvoidPoint Finsler.BorelDeformation Finsler.BorelLocalK Finsler.BorelCoverK
open Finsler.TrivialK Finsler.FixedGlobal Finsler.ThetaLadder Finsler.TripleK
open Finsler.TotalExact Finsler.FixedLadder Finsler.GradedLadder

noncomputable section

/-! ### Exactness as equalities of subspaces -/

section Exact

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''} (h : ShortExact ι π)

include h in
theorem ker_mid (q : ℕ) : LinearMap.ker (HRmap π q) = LinearMap.range (HRmap ι q) := by
  ext x
  constructor
  · intro hx
    exact exact_mid h q x (LinearMap.mem_ker.mp hx)
  · rintro ⟨z, rfl⟩
    exact LinearMap.mem_ker.mpr (comp_zero h q z)

theorem ker_delta (q : ℕ) : LinearMap.ker (delta h q) = LinearMap.range (HRmap π q) := by
  ext x
  constructor
  · intro hx
    exact exact_delta h q x (LinearMap.mem_ker.mp hx)
  · rintro ⟨y, rfl⟩
    exact LinearMap.mem_ker.mpr (delta_comp_zero h q y)

theorem ker_sub (q : ℕ) : LinearMap.ker (HRmap ι (q + 1)) = LinearMap.range (delta h q) := by
  ext y
  constructor
  · intro hy
    exact exact_sub h q y (LinearMap.mem_ker.mp hy)
  · rintro ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (comp_delta_zero h q x)

end Exact

variable {n : ℕ}

/-! ### The potential of a pair -/

section Pair

variable {s t s₀ t₀ : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t)
  (hst₀ : s₀ ⊆ t₀) (hs₀ : KInv s₀) (ht₀ : KInv t₀) (hss : s₀ ⊆ s) (htt : t₀ ⊆ t)
  (hfix : ∀ u : SphereLoop n, u ∈ t₀ → half +ᵥ u = u)

/-- The potential of the cutoff j in the degrees q and q + 1 for the pair (t, s) and the fixed
pair (t₀, s₀). -/
def phi (j q : ℕ) : ℤ :=
  gphi (fun l => HR (rComplex hst₀ hs₀ ht₀) l) j
    (fun l => eps hst hs ht hst₀ hs₀ ht₀ hss htt hfix (q + 1) l)
    (fun l => eps hst hs ht hst₀ hs₀ ht₀ hss htt hfix q l)

/-- The total normalized restriction of a degree, into the product of the reflection Borel
cohomology of the fixed pair over all root degrees. -/
def epsTot (q : ℕ) :=
  totMap (X := HR (borelInv (kCommuting hst hs ht)) q)
    (G := fun l => HR (rComplex hst₀ hs₀ ht₀) l)
    (fun l => eps hst hs ht hst₀ hs₀ ht₀ hss htt hfix q l)

end Pair

/-! ### The two statements for a triple -/

section Triple

variable {s t u s₀ t₀ u₀ : Set (Loops n)} (hst : s ⊆ t) (htu : t ⊆ u) (hs : KInv s)
  (ht : KInv t) (hu : KInv u) (hst₀ : s₀ ⊆ t₀) (htu₀ : t₀ ⊆ u₀) (hs₀ : KInv s₀) (ht₀ : KInv t₀)
  (hu₀ : KInv u₀) (hss : s₀ ⊆ s) (htt : t₀ ⊆ t) (huu : u₀ ⊆ u)
  (hfix : ∀ v : SphereLoop n, v ∈ u₀ → half +ᵥ v = v)

/-- A far cutoff: the potential does not increase from (t, s) to (u, s). -/
theorem phi_far (j q : ℕ)
    (hV : FinTot (fun l => HR (rComplex hst₀ hs₀ ht₀) l))
    (hV' : FinTot (fun l => HR (rComplex (hst₀.trans htu₀) hs₀ hu₀) l))
    (hWf : FinTot (fun l => HR (rComplex htu₀ ht₀ hu₀) l))
    (hAq : Module.Finite (ZMod 2) (HR (borelInv (kCommuting hst hs ht)) q))
    (hA : Module.Finite (ZMod 2) (HR (borelInv (kCommuting hst hs ht)) (q + 1)))
    (hA' : Module.Finite (ZMod 2) (HR (borelInv (kCommuting (hst.trans htu) hs hu)) (q + 1)))
    (hC : Module.Finite (ZMod 2) (HR (borelInv (kCommuting htu ht hu)) (q + 1)))
    (hd : ∀ x : HR (rComplex hst₀ hs₀ ht₀) j,
      delta (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀) j x = 0)
    (hl₀ : LinearMap.range (cut (fun l => HR (rComplex htu₀ ht₀ hu₀) l) j) ≤
      LinearMap.range (epsTot htu ht hu htu₀ ht₀ hu₀ htt huu hfix q))
    (hl₁ : Function.Injective (epsTot htu ht hu htu₀ ht₀ hu₀ htt huu hfix (q + 1)))
    (hl₁P : LinearMap.range (epsTot htu ht hu htu₀ ht₀ hu₀ htt huu hfix (q + 1)) =
      LinearMap.range (cut (fun l => HR (rComplex htu₀ ht₀ hu₀) l) j))
    (hl₂ : Function.Injective (epsTot htu ht hu htu₀ ht₀ hu₀ htt huu hfix (q + 1 + 1)))
    (hl₂P : LinearMap.range (epsTot htu ht hu htu₀ ht₀ hu₀ htt huu hfix (q + 1 + 1)) ≤
      LinearMap.range (cut (fun l => HR (rComplex htu₀ ht₀ hu₀) l) j)) :
    phi (hst.trans htu) hs hu (hst₀.trans htu₀) hs₀ hu₀ hss huu hfix j q ≤
      phi hst hs ht hst₀ hs₀ ht₀ hss htt (fun v hv => hfix v (htu₀ hv)) j q :=
  gphi_far (Vg := fun l => HR (rComplex hst₀ hs₀ ht₀) l)
    (V'g := fun l => HR (rComplex (hst₀.trans htu₀) hs₀ hu₀) l)
    (Wg := fun l => HR (rComplex htu₀ ht₀ hu₀) l)
    (A := HR (borelInv (kCommuting hst hs ht)) (q + 1))
    (A' := HR (borelInv (kCommuting (hst.trans htu) hs hu)) (q + 1))
    (B := HR (borelInv (kCommuting hst hs ht)) q)
    (B' := HR (borelInv (kCommuting (hst.trans htu) hs hu)) q)
    (C₀ := HR (borelInv (kCommuting htu ht hu)) q)
    (C₁ := HR (borelInv (kCommuting htu ht hu)) (q + 1))
    (C₂ := HR (borelInv (kCommuting htu ht hu)) (q + 1 + 1))
    (fun l => HRmap (kHom (hst₀.trans htu₀) hs₀ hu₀ htu₀ ht₀ hu₀ hst₀ subset_rfl).φ l)
    (fun l => HRmap (kHom hst₀ hs₀ ht₀ (hst₀.trans htu₀) hs₀ hu₀ subset_rfl htu₀).φ l)
    (fun l => delta (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀) l)
    (delta (shortExactK hst htu hs ht hu) q)
    (HRmap (borelHom (kHom (hst.trans htu) hs hu htu ht hu hst subset_rfl)) (q + 1))
    (HRmap (borelHom (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu)) (q + 1))
    (delta (shortExactK hst htu hs ht hu) (q + 1))
    (HRmap (borelHom (kHom (hst.trans htu) hs hu htu ht hu hst subset_rfl)) q)
    (HRmap (borelHom (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu)) q)
    (fun l => eps hst hs ht hst₀ hs₀ ht₀ hss htt (fun v hv => hfix v (htu₀ hv)) (q + 1) l)
    (fun l => eps (hst.trans htu) hs hu (hst₀.trans htu₀) hs₀ hu₀ hss huu hfix (q + 1) l)
    (fun l => eps hst hs ht hst₀ hs₀ ht₀ hss htt (fun v hv => hfix v (htu₀ hv)) q l)
    (fun l => eps (hst.trans htu) hs hu (hst₀.trans htu₀) hs₀ hu₀ hss huu hfix q l)
    (fun l => eps htu ht hu htu₀ ht₀ hu₀ htt huu hfix q l)
    (fun l => eps htu ht hu htu₀ ht₀ hu₀ htt huu hfix (q + 1) l)
    (fun l => eps htu ht hu htu₀ ht₀ hu₀ htt huu hfix (q + 1 + 1) l)
    hV hV' hWf
    (comp_zero (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀))
    (exact_mid (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀))
    (delta_comp_zero (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀))
    (exact_delta (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀))
    (injective_zero (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀))
    (comp_delta_zero (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀))
    (exact_sub (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀))
    (ker_sub (shortExactK hst htu hs ht hu) q)
    (ker_mid (shortExactK hst htu hs ht hu) (q + 1))
    (ker_delta (shortExactK hst htu hs ht hu) (q + 1))
    (ker_delta (shortExactK hst htu hs ht hu) q)
    (fun l y => (eps_natural hst hs ht (hst.trans htu) hs hu hst₀ hs₀ ht₀ (hst₀.trans htu₀)
      hs₀ hu₀ hss htt hss huu subset_rfl htu subset_rfl htu₀ hfix (q + 1) l y).symm)
    (fun l y => (eps_natural hst hs ht (hst.trans htu) hs hu hst₀ hs₀ ht₀ (hst₀.trans htu₀)
      hs₀ hu₀ hss htt hss huu subset_rfl htu subset_rfl htu₀ hfix q l y).symm)
    (fun l a => (eps_delta hst htu hs ht hu hst₀ htu₀ hs₀ ht₀ hu₀ hss htt huu hfix (q + 1) l
      a).symm)
    (eps_delta_zero hst htu hs ht hu hst₀ htu₀ hs₀ ht₀ hu₀ hss htt huu hfix (q + 1))
    (fun l a => (eps_delta hst htu hs ht hu hst₀ htu₀ hs₀ ht₀ hu₀ hss htt huu hfix q l a).symm)
    (eps_delta_zero hst htu hs ht hu hst₀ htu₀ hs₀ ht₀ hu₀ hss htt huu hfix q)
    (fun l c => eps_natural (hst.trans htu) hs hu htu ht hu (hst₀.trans htu₀) hs₀ hu₀ htu₀ ht₀
      hu₀ hss huu htt huu hst subset_rfl hst₀ subset_rfl hfix (q + 1) l c)
    (fun l c => eps_natural (hst.trans htu) hs hu htu ht hu (hst₀.trans htu₀) hs₀ hu₀ htu₀ ht₀
      hu₀ hss huu htt huu hst subset_rfl hst₀ subset_rfl hfix q l c)
    j hd hl₀ hl₁ hl₁P hl₂ hl₂P

/-- A general cutoff: the potentials of (u, s) and (t, s) differ by at most six times a bound
for the dimensions of the total fixed crossing group and of the K-Borel crossing groups of the
degrees q + 1 and q + 2. -/
theorem phi_near (j q : ℕ)
    (hV : FinTot (fun l => HR (rComplex hst₀ hs₀ ht₀) l))
    (hV' : FinTot (fun l => HR (rComplex (hst₀.trans htu₀) hs₀ hu₀) l))
    (hWf : FinTot (fun l => HR (rComplex htu₀ ht₀ hu₀) l))
    (hAq : Module.Finite (ZMod 2) (HR (borelInv (kCommuting hst hs ht)) q))
    (hA : Module.Finite (ZMod 2) (HR (borelInv (kCommuting hst hs ht)) (q + 1)))
    (hA' : Module.Finite (ZMod 2) (HR (borelInv (kCommuting (hst.trans htu) hs hu)) (q + 1)))
    (hC : Module.Finite (ZMod 2) (HR (borelInv (kCommuting htu ht hu)) (q + 1)))
    (hC₂ : Module.Finite (ZMod 2) (HR (borelInv (kCommuting htu ht hu)) (q + 1 + 1)))
    {M : ℕ} (hWM : totRank (fun l => HR (rComplex htu₀ ht₀ hu₀) l) ≤ M)
    (hM₁ : finrank (ZMod 2) (HR (borelInv (kCommuting htu ht hu)) (q + 1)) ≤ M)
    (hM₂ : finrank (ZMod 2) (HR (borelInv (kCommuting htu ht hu)) (q + 1 + 1)) ≤ M) :
    phi (hst.trans htu) hs hu (hst₀.trans htu₀) hs₀ hu₀ hss huu hfix j q ≤
        phi hst hs ht hst₀ hs₀ ht₀ hss htt (fun v hv => hfix v (htu₀ hv)) j q + 6 * (M : ℤ) ∧
      phi hst hs ht hst₀ hs₀ ht₀ hss htt (fun v hv => hfix v (htu₀ hv)) j q ≤
        phi (hst.trans htu) hs hu (hst₀.trans htu₀) hs₀ hu₀ hss huu hfix j q + 6 * (M : ℤ) :=
  gphi_near (Vg := fun l => HR (rComplex hst₀ hs₀ ht₀) l)
    (V'g := fun l => HR (rComplex (hst₀.trans htu₀) hs₀ hu₀) l)
    (Wg := fun l => HR (rComplex htu₀ ht₀ hu₀) l)
    (A := HR (borelInv (kCommuting hst hs ht)) (q + 1))
    (A' := HR (borelInv (kCommuting (hst.trans htu) hs hu)) (q + 1))
    (B := HR (borelInv (kCommuting hst hs ht)) q)
    (B' := HR (borelInv (kCommuting (hst.trans htu) hs hu)) q)
    (C₁ := HR (borelInv (kCommuting htu ht hu)) (q + 1))
    (C₂ := HR (borelInv (kCommuting htu ht hu)) (q + 1 + 1))
    (fun l => HRmap (kHom (hst₀.trans htu₀) hs₀ hu₀ htu₀ ht₀ hu₀ hst₀ subset_rfl).φ l)
    (fun l => HRmap (kHom hst₀ hs₀ ht₀ (hst₀.trans htu₀) hs₀ hu₀ subset_rfl htu₀).φ l)
    (fun l => delta (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀) l)
    (delta (shortExactK hst htu hs ht hu) q)
    (HRmap (borelHom (kHom (hst.trans htu) hs hu htu ht hu hst subset_rfl)) (q + 1))
    (HRmap (borelHom (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu)) (q + 1))
    (delta (shortExactK hst htu hs ht hu) (q + 1))
    (HRmap (borelHom (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu)) q)
    (fun l => eps hst hs ht hst₀ hs₀ ht₀ hss htt (fun v hv => hfix v (htu₀ hv)) (q + 1) l)
    (fun l => eps (hst.trans htu) hs hu (hst₀.trans htu₀) hs₀ hu₀ hss huu hfix (q + 1) l)
    (fun l => eps hst hs ht hst₀ hs₀ ht₀ hss htt (fun v hv => hfix v (htu₀ hv)) q l)
    (fun l => eps (hst.trans htu) hs hu (hst₀.trans htu₀) hs₀ hu₀ hss huu hfix q l)
    hV hV' hWf
    (comp_zero (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀))
    (exact_mid (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀))
    (delta_comp_zero (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀))
    (exact_delta (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀))
    (ker_mid (shortExactK hst htu hs ht hu) (q + 1))
    (ker_delta (shortExactK hst htu hs ht hu) (q + 1))
    (ker_delta (shortExactK hst htu hs ht hu) q)
    (fun l y => (eps_natural hst hs ht (hst.trans htu) hs hu hst₀ hs₀ ht₀ (hst₀.trans htu₀)
      hs₀ hu₀ hss htt hss huu subset_rfl htu subset_rfl htu₀ hfix (q + 1) l y).symm)
    (fun l y => (eps_natural hst hs ht (hst.trans htu) hs hu hst₀ hs₀ ht₀ (hst₀.trans htu₀)
      hs₀ hu₀ hss htt hss huu subset_rfl htu subset_rfl htu₀ hfix q l y).symm)
    j hWM hM₁ hM₂

end Triple

end

end Finsler.LadderEvent
