module

public import Finsler.Topology.FixedGlobal
public import Finsler.Topology.ThetaLadder

/-! The normalized restriction to fixed loops and its rules. For a pair (t, s) of sets of loops
invariant under the reversal and the half rotation and a pair (t₀, s₀) of invariant sets inside
whose loops are fixed by the half rotation, the normalized restriction in degree q and root
degree l sends a class of the K-Borel cohomology of (t, s) to the component of degree l of its
restriction to (t₀, s₀), a class of the reflection Borel cohomology of (t₀, s₀). It vanishes for
l > q, is unchanged by multiplication with the class v of the half rotation, and multiplication
with the reflection class raises the root degree by one. It is natural for restriction between
pairs. For a triple s ⊆ t ⊆ u with a fixed triple s₀ ⊆ t₀ ⊆ u₀ inside, the connecting map of
the K-Borel sequence of (u, t, s) corresponds to the connecting map of the reflection Borel
sequence of (u₀, t₀, s₀) and raises the root degree by one, and the root degree zero component
of a connecting class vanishes. These are the squares of the comparison between the ambient and
the fixed exact sequences. -/

@[expose] public section

namespace Finsler.FixedLadder

open CategoryTheory Set
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelExact Finsler.BorelFreeK
open Finsler.AvoidPoint Finsler.BorelDeformation Finsler.BorelLocalK Finsler.BorelCoverK
open Finsler.TrivialK Finsler.FixedGlobal Finsler.ThetaLadder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! ### Squares of cochain maps -/

/-- A commuting square of equivariant cochain maps commutes on Borel cohomology. -/
theorem HRmap_square {K L M N : InvComplex} (φ₁ : InvHom L N) (φ₂ : InvHom K L)
    (φ₃ : InvHom M N) (φ₄ : InvHom K M)
    (h : ∀ j x, φ₁.f j (φ₂.f j x) = φ₃.f j (φ₄.f j x)) (q : ℕ) (y : HR K q) :
    HRmap φ₁ q (HRmap φ₂ q y) = HRmap φ₃ q (HRmap φ₄ q y) := by
  rw [← HRmap_comp, ← HRmap_comp]
  exact HRmap_congr h q y

/-- A commuting square of maps commuting with the second involutions commutes on the iterated
Borel cochains. -/
theorem borelHom_square {K L M N : InvComplex} {SK : Commuting K} {SL : Commuting L}
    {SM : Commuting M} {SN : Commuting N} (Φ₁ : CommHom SL SN) (Φ₂ : CommHom SK SL)
    (Φ₃ : CommHom SM SN) (Φ₄ : CommHom SK SM)
    (h : ∀ j x, Φ₁.φ.f j (Φ₂.φ.f j x) = Φ₃.φ.f j (Φ₄.φ.f j x)) (j : ℕ)
    (x : (borelInv SK).C j) :
    (borelHom Φ₁).f j ((borelHom Φ₂).f j x) = (borelHom Φ₃).f j ((borelHom Φ₄).f j x) := by
  apply Subtype.ext
  funext m
  exact h m _

variable {n : ℕ}

/-- Restrictions between pairs of invariant sets of loops compose. -/
theorem kHom_comp {s t s' t' s'' t'' : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t)
    (hst' : s' ⊆ t') (hs' : KInv s') (ht' : KInv t') (hst'' : s'' ⊆ t'') (hs'' : KInv s'')
    (ht'' : KInv t'') (hss : s ⊆ s') (htt : t ⊆ t') (hss' : s' ⊆ s'') (htt' : t' ⊆ t'') (j : ℕ)
    (x : (cochains (pairOf hst'')).X j) :
    (kHom hst hs ht hst' hs' ht' hss htt).φ.f j
        ((kHom hst' hs' ht' hst'' hs'' ht'' hss' htt').φ.f j x) =
      (kHom hst hs ht hst'' hs'' ht'' (hss.trans hss') (htt.trans htt')).φ.f j x := by
  have h := pull_comp_apply (inclPair hst hst' hss htt) (inclPair hst' hst'' hss' htt') j x
  have e : inclPair hst hst' hss htt ≫ inclPair hst' hst'' hss' htt' =
      inclPair hst hst'' (hss.trans hss') (htt.trans htt') := by
    ext : 2 <;> rfl
  rw [e] at h
  exact h.symm

/-! ### The normalized restriction of a pair -/

section Pair

variable {s t s₀ t₀ : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t)
  (hst₀ : s₀ ⊆ t₀) (hs₀ : KInv s₀) (ht₀ : KInv t₀) (hss : s₀ ⊆ s) (htt : t₀ ⊆ t)
  (hfix : ∀ u : SphereLoop n, u ∈ t₀ → half +ᵥ u = u)

/-- The reflection cochains of a pair of invariant sets of loops. -/
abbrev rComplex : InvComplex :=
  ofPair (pairOf hst₀) (revSub hst₀ hs₀.rev_mem ht₀.rev_mem)
    (revSub_sq hst₀ hs₀.rev_mem ht₀.rev_mem)

/-- The normalized restriction: the component of root degree l of the restriction of a K-Borel
class of degree q of (t, s) to a pair (t₀, s₀) of loops fixed by the half rotation. -/
def eps (q l : ℕ) :
    HR (borelInv (kCommuting hst hs ht)) q →ₗ[ZMod 2] HR (rComplex hst₀ hs₀ ht₀) l :=
  theta (kCommuting hst₀ hs₀ ht₀) (kCommuting_trivial hst₀ hs₀ ht₀ hfix) q l ∘ₗ
    HRmap (borelHom (kHom hst₀ hs₀ ht₀ hst hs ht hss htt)) q

theorem eps_apply (q l : ℕ) (x : HR (borelInv (kCommuting hst hs ht)) q) :
    eps hst hs ht hst₀ hs₀ ht₀ hss htt hfix q l x =
      theta (kCommuting hst₀ hs₀ ht₀) (kCommuting_trivial hst₀ hs₀ ht₀ hfix) q l
        (HRmap (borelHom (kHom hst₀ hs₀ ht₀ hst hs ht hss htt)) q x) := rfl

/-- Multiplication by the class of the half rotation leaves the normalized restriction
unchanged. -/
theorem eps_w (q l : ℕ) (x : HR (borelInv (kCommuting hst hs ht)) q) :
    eps hst hs ht hst₀ hs₀ ht₀ hss htt hfix (q + 1) l
        (w (borelInv (kCommuting hst hs ht)) q x) =
      eps hst hs ht hst₀ hs₀ ht₀ hss htt hfix q l x := by
  rw [eps_apply, eps_apply, HRmap_w, theta_w]

/-- Multiplication by the reflection class raises the root degree by one. -/
theorem eps_innerStep (q l : ℕ) (x : HR (borelInv (kCommuting hst hs ht)) q) :
    eps hst hs ht hst₀ hs₀ ht₀ hss htt hfix (q + 1) (l + 1)
        (innerStep (kCommuting hst hs ht) q x) =
      w (rComplex hst₀ hs₀ ht₀) l (eps hst hs ht hst₀ hs₀ ht₀ hss htt hfix q l x) := by
  rw [eps_apply, eps_apply, HRmap_innerStep, theta_innerStep_succ]

/-- The normalized restriction of a class of degree q has root degrees at most q. -/
theorem eps_high (q l : ℕ) (hl : q < l) (x : HR (borelInv (kCommuting hst hs ht)) q) :
    eps hst hs ht hst₀ hs₀ ht₀ hss htt hfix q l x = 0 :=
  theta_high (kCommuting hst₀ hs₀ ht₀) (kCommuting_trivial hst₀ hs₀ ht₀ hfix) q l hl _

/-- A class whose normalized restriction vanishes restricts to zero on the fixed pair. -/
theorem res_eq_zero_of_eps (q : ℕ) (x : HR (borelInv (kCommuting hst hs ht)) q)
    (hx : ∀ l, l ≤ q → eps hst hs ht hst₀ hs₀ ht₀ hss htt hfix q l x = 0) :
    HRmap (borelHom (kHom hst₀ hs₀ ht₀ hst hs ht hss htt)) q x = 0 :=
  eq_zero_of_theta (kCommuting hst₀ hs₀ ht₀) (kCommuting_trivial hst₀ hs₀ ht₀ hfix) q _ hx

end Pair

/-! ### Naturality -/

section Natural

variable {s t s' t' s₀ t₀ s₀' t₀' : Set (Loops n)}
  (hst : s ⊆ t) (hs : KInv s) (ht : KInv t) (hst' : s' ⊆ t') (hs' : KInv s') (ht' : KInv t')
  (hst₀ : s₀ ⊆ t₀) (hs₀ : KInv s₀) (ht₀ : KInv t₀)
  (hst₀' : s₀' ⊆ t₀') (hs₀' : KInv s₀') (ht₀' : KInv t₀')
  (hss : s₀ ⊆ s) (htt : t₀ ⊆ t) (hss' : s₀' ⊆ s') (htt' : t₀' ⊆ t')
  (has : s ⊆ s') (hat : t ⊆ t') (hfs : s₀ ⊆ s₀') (hft : t₀ ⊆ t₀')
  (hfix' : ∀ u : SphereLoop n, u ∈ t₀' → half +ᵥ u = u)

/-- The normalized restriction is natural for restriction between pairs. -/
theorem eps_natural (q l : ℕ) (y : HR (borelInv (kCommuting hst' hs' ht')) q) :
    eps hst hs ht hst₀ hs₀ ht₀ hss htt (fun u hu => hfix' u (hft hu)) q l
        (HRmap (borelHom (kHom hst hs ht hst' hs' ht' has hat)) q y) =
      HRmap (kHom hst₀ hs₀ ht₀ hst₀' hs₀' ht₀' hfs hft).φ l
        (eps hst' hs' ht' hst₀' hs₀' ht₀' hss' htt' hfix' q l y) := by
  rw [eps_apply, eps_apply,
    HRmap_square (borelHom (kHom hst₀ hs₀ ht₀ hst hs ht hss htt))
      (borelHom (kHom hst hs ht hst' hs' ht' has hat))
      (borelHom (kHom hst₀ hs₀ ht₀ hst₀' hs₀' ht₀' hfs hft))
      (borelHom (kHom hst₀' hs₀' ht₀' hst' hs' ht' hss' htt'))
      (borelHom_square _ _ _ _ fun j x =>
        (kHom_comp hst₀ hs₀ ht₀ hst hs ht hst' hs' ht' hss htt has hat j x).trans
          (kHom_comp hst₀ hs₀ ht₀ hst₀' hs₀' ht₀' hst' hs' ht' hfs hft hss' htt' j x).symm) q y]
  exact theta_natural (kCommuting_trivial hst₀' hs₀' ht₀' hfix')
    (kCommuting_trivial hst₀ hs₀ ht₀ fun u hu => hfix' u (hft hu))
    (kHom hst₀ hs₀ ht₀ hst₀' hs₀' ht₀' hfs hft) q l _

end Natural

/-! ### Connecting maps -/

section Triple

variable {s t u s₀ t₀ u₀ : Set (Loops n)} (hst : s ⊆ t) (htu : t ⊆ u) (hs : KInv s)
  (ht : KInv t) (hu : KInv u) (hst₀ : s₀ ⊆ t₀) (htu₀ : t₀ ⊆ u₀) (hs₀ : KInv s₀) (ht₀ : KInv t₀)
  (hu₀ : KInv u₀) (hss : s₀ ⊆ s) (htt : t₀ ⊆ t) (huu : u₀ ⊆ u)
  (hfix : ∀ v : SphereLoop n, v ∈ u₀ → half +ᵥ v = v)

/-- The K-Borel cochains of (u, t), (u, s), (t, s) form a short exact sequence. -/
theorem shortExactK :
    ShortExact (borelHom (kHom (hst.trans htu) hs hu htu ht hu hst subset_rfl))
      (borelHom (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu)) :=
  BorelQuasiIso.shortExact_iterated _ _ (shortExact_incl hst htu hs ht hu)

/-- The connecting map of the K-Borel sequence of (u, t, s) is carried by restriction to the
connecting map of the K-Borel sequence of the fixed triple. -/
theorem res_delta (q : ℕ) (x : HR (borelInv (kCommuting hst hs ht)) q) :
    delta (shortExactK hst₀ htu₀ hs₀ ht₀ hu₀) q
        (HRmap (borelHom (kHom hst₀ hs₀ ht₀ hst hs ht hss htt)) q x) =
      HRmap (borelHom (kHom htu₀ ht₀ hu₀ htu ht hu htt huu)) (q + 1)
        (delta (shortExactK hst htu hs ht hu) q x) :=
  delta_natural (shortExactK hst htu hs ht hu) (shortExactK hst₀ htu₀ hs₀ ht₀ hu₀)
    (borelHom (kHom htu₀ ht₀ hu₀ htu ht hu htt huu))
    (borelHom (kHom (hst₀.trans htu₀) hs₀ hu₀ (hst.trans htu) hs hu hss huu))
    (borelHom (kHom hst₀ hs₀ ht₀ hst hs ht hss htt))
    (fun j z => borelHom_square _ _ _ _ (fun m y =>
      (kHom_comp (hst₀.trans htu₀) hs₀ hu₀ (hst.trans htu) hs hu htu ht hu hss huu hst
        subset_rfl m y).trans
        (kHom_comp (hst₀.trans htu₀) hs₀ hu₀ htu₀ ht₀ hu₀ htu ht hu hst₀ subset_rfl htt huu
          m y).symm) j z)
    (fun j y => borelHom_square _ _ _ _ (fun m z =>
      (kHom_comp hst₀ hs₀ ht₀ hst hs ht (hst.trans htu) hs hu hss htt subset_rfl htu m z).trans
        (kHom_comp hst₀ hs₀ ht₀ (hst₀.trans htu₀) hs₀ hu₀ (hst.trans htu) hs hu subset_rfl htu₀
          hss huu m z).symm) j y) q x

/-- The connecting maps raise the root degree by one: the normalized restriction of a connecting
class of the K-Borel sequence of (u, t, s) in root degree l + 1 is the connecting class, in the
reflection Borel sequence of the fixed triple, of the normalized restriction in root degree
l. -/
theorem eps_delta (q l : ℕ) (x : HR (borelInv (kCommuting hst hs ht)) q) :
    eps htu ht hu htu₀ ht₀ hu₀ htt huu hfix (q + 1) (l + 1)
        (delta (shortExactK hst htu hs ht hu) q x) =
      delta (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀) l
        (eps hst hs ht hst₀ hs₀ ht₀ hss htt (fun v hv => hfix v (htu₀ hv)) q l x) := by
  rw [eps_apply, eps_apply, ← res_delta hst htu hs ht hu hst₀ htu₀ hs₀ ht₀ hu₀ hss htt huu q x]
  exact theta_delta (kHom (hst₀.trans htu₀) hs₀ hu₀ htu₀ ht₀ hu₀ hst₀ subset_rfl)
    (kHom hst₀ hs₀ ht₀ (hst₀.trans htu₀) hs₀ hu₀ subset_rfl htu₀)
    (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀) (kCommuting_trivial htu₀ ht₀ hu₀ hfix)
    (kCommuting_trivial (hst₀.trans htu₀) hs₀ hu₀ hfix)
    (kCommuting_trivial hst₀ hs₀ ht₀ fun v hv => hfix v (htu₀ hv)) q l _

include hst₀ hs₀ hss in
/-- The root degree zero component of a connecting class vanishes. -/
theorem eps_delta_zero (q : ℕ) (x : HR (borelInv (kCommuting hst hs ht)) q) :
    eps htu ht hu htu₀ ht₀ hu₀ htt huu hfix (q + 1) 0
        (delta (shortExactK hst htu hs ht hu) q x) = 0 := by
  rw [eps_apply, ← res_delta hst htu hs ht hu hst₀ htu₀ hs₀ ht₀ hu₀ hss htt huu q x]
  exact theta_delta_zero (kHom (hst₀.trans htu₀) hs₀ hu₀ htu₀ ht₀ hu₀ hst₀ subset_rfl)
    (kHom hst₀ hs₀ ht₀ (hst₀.trans htu₀) hs₀ hu₀ subset_rfl htu₀)
    (shortExact_incl hst₀ htu₀ hs₀ ht₀ hu₀) (kCommuting_trivial htu₀ ht₀ hu₀ hfix)
    (kCommuting_trivial (hst₀.trans htu₀) hs₀ hu₀ hfix) q _

end Triple

end

end Finsler.FixedLadder
