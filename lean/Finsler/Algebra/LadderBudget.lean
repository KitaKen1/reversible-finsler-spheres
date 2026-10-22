module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The change of the four-term potential across a crossing, as linear algebra. The fixed side is
an exact sequence W → V' → V → W of finite dimensional spaces (the totals over root degrees of
the reflection groups of the crossing and of the two cuts), with a projection P on each (root
degrees at most the cutoff). The ambient side consists of the exact sequences
C_q → A'_q → A_q → C_{q+1} for the degrees q = J − 1 and q = J, with comparison maps
λ : C → W, ε' : A' → V', ε : A → V commuting with the rows. For a degree q let PE_q = P(ε(A_q))
and L = P(V). The potential is

  Φ = (dim L − dim PE_J) + (dim L − dim PE_{J−1}) + (dim A_J − dim PE_J).

* Far cutoff. If the three maps of the fixed sequence commute with P, λ_J is bijective onto
  P(W), λ_{J−1} covers P(W), and λ_J, λ_{J+1} are injective with images in P(W), then

    Φ' − Φ = −(rank(δ on L) − rank(δ on PE_J)) ≤ 0.

* General cutoff. If f and i commute with P and the spaces W, C_J, C_{J+1} have dimension at
  most M, then |Φ' − Φ| ≤ 6M.

Both statements use only rank–nullity; no topology enters. -/

@[expose] public section

namespace Finsler.LadderBudget

open Module

/-- The potential of a cutoff from the four dimensions dim L, dim PE_J, dim PE_{J−1}, dim A_J. -/
def potential (L PE PF A : ℕ) : ℤ := 2 * (L : ℤ) - 2 * (PE : ℤ) - (PF : ℤ) + (A : ℤ)

section

variable {𝕜 : Type*} [Field 𝕜]

/-- Rank–nullity on a subspace. -/
theorem finrank_eq_inf_ker_add_map {X Y : Type*} [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y] (g : X →ₗ[𝕜] Y) (S : Submodule 𝕜 X) [FiniteDimensional 𝕜 S] :
    finrank 𝕜 S = finrank 𝕜 (S ⊓ LinearMap.ker g : Submodule 𝕜 X) + finrank 𝕜 (S.map g) := by
  have h := LinearMap.finrank_range_add_finrank_ker (g.domRestrict S)
  rw [LinearMap.range_domRestrict] at h
  have e : finrank 𝕜 (LinearMap.ker (g.domRestrict S)) =
      finrank 𝕜 (S ⊓ LinearMap.ker g : Submodule 𝕜 X) := by
    rw [← Submodule.finrank_map_subtype_eq S (LinearMap.ker (g.domRestrict S)),
      LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  omega

/-- The image of a subspace has the dimension of the image of the kernel of a second map plus at
most the rank of that map. -/
theorem finrank_range_le_ker_map {X Y Z : Type*} [AddCommGroup X] [Module 𝕜 X]
    [FiniteDimensional 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y] [AddCommGroup Z] [Module 𝕜 Z]
    (T : X →ₗ[𝕜] Y) (d : X →ₗ[𝕜] Z) :
    finrank 𝕜 (LinearMap.range T) ≤
      finrank 𝕜 ((LinearMap.ker d).map T) + finrank 𝕜 (LinearMap.range d) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 := LinearMap.finrank_range_add_finrank_ker d
  have h3 := finrank_eq_inf_ker_add_map T (LinearMap.ker d)
  have h4 : finrank 𝕜 (LinearMap.ker d ⊓ LinearMap.ker T : Submodule 𝕜 X) ≤
      finrank 𝕜 (LinearMap.ker T) := Submodule.finrank_mono inf_le_right
  omega

end

/-! ### The fixed exact sequence -/

section Fixed

variable {𝕜 : Type*} [Field 𝕜] {V V' W : Type*}
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup V'] [Module 𝕜 V'] [AddCommGroup W] [Module 𝕜 W]
  (f : W →ₗ[𝕜] V') (i : V' →ₗ[𝕜] V) (δ : V →ₗ[𝕜] W)
  (PV : V →ₗ[𝕜] V) (PV' : V' →ₗ[𝕜] V') (PW : W →ₗ[𝕜] W)
  (hE1 : LinearMap.ker i = LinearMap.range f) (hE2 : LinearMap.ker δ = LinearMap.range i)
  (hE3 : LinearMap.ker f = LinearMap.range δ)
  (hPV : ∀ x, PV (PV x) = PV x) (hPV' : ∀ y, PV' (PV' y) = PV' y)
  (hPW : ∀ w, PW (PW w) = PW w)
  (hfP : ∀ w, f (PW w) = PV' (f w)) (hiP : ∀ y, i (PV' y) = PV (i y))
  (hδP : ∀ v, δ (PV v) = PW (δ v))

include hE1 hPV' hfP in
/-- The low part of V' meets the kernel of i in the image of the low part of W. -/
theorem low_inf_ker :
    LinearMap.range PV' ⊓ LinearMap.ker i = (LinearMap.range PW).map f := by
  ext y
  constructor
  · rintro ⟨⟨y0, rfl⟩, hy⟩
    rw [hE1] at hy
    obtain ⟨w, hw⟩ := hy
    refine ⟨PW w, ⟨w, rfl⟩, ?_⟩
    rw [hfP, hw, hPV']
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨⟨f w, (hfP w).symm⟩, ?_⟩
    rw [hE1]
    exact ⟨PW w, rfl⟩

include hE2 hPV hiP in
/-- The image of the low part of V' is the low part of the kernel of δ. -/
theorem low_map :
    (LinearMap.range PV').map i = LinearMap.range PV ⊓ LinearMap.ker δ := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨⟨i y, (hiP y).symm⟩, ?_⟩
    rw [hE2]
    exact ⟨PV' y, rfl⟩
  · rintro ⟨⟨x0, rfl⟩, hx⟩
    rw [hE2] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨PV' y, ⟨y, rfl⟩, ?_⟩
    rw [hiP, hy, hPV]

include hE3 hPW hδP in
/-- The low part of W meets the kernel of f in the image under δ of the low part of V. -/
theorem low_inf_ker_f :
    LinearMap.range PW ⊓ LinearMap.ker f = (LinearMap.range PV).map δ := by
  ext w
  constructor
  · rintro ⟨⟨w0, rfl⟩, hw⟩
    rw [hE3] at hw
    obtain ⟨v, hv⟩ := hw
    refine ⟨PV v, ⟨v, rfl⟩, ?_⟩
    rw [hδP, hv, hPW]
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨⟨δ v, (hδP v).symm⟩, ?_⟩
    rw [hE3]
    exact ⟨PV v, rfl⟩

include hE1 hE2 hPV hPV' hfP hiP in
/-- dim L' + rank(δ on L) = dim f(P W) + dim L. -/
theorem finrank_low [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 V'] :
    finrank 𝕜 (LinearMap.range PV') + finrank 𝕜 ((LinearMap.range PV).map δ) =
      finrank 𝕜 ((LinearMap.range PW).map f) + finrank 𝕜 (LinearMap.range PV) := by
  have h1 := finrank_eq_inf_ker_add_map i (LinearMap.range PV')
  rw [low_inf_ker f i PV' PW hE1 hPV' hfP, low_map i δ PV PV' hE2 hPV hiP] at h1
  have h2 := finrank_eq_inf_ker_add_map δ (LinearMap.range PV)
  omega

include hE3 hPW hδP in
/-- dim P W = dim f(P W) + rank(δ on L). -/
theorem finrank_lowW [FiniteDimensional 𝕜 W] :
    finrank 𝕜 (LinearMap.range PW) =
      finrank 𝕜 ((LinearMap.range PW).map f) + finrank 𝕜 ((LinearMap.range PV).map δ) := by
  have h := finrank_eq_inf_ker_add_map f (LinearMap.range PW)
  rw [low_inf_ker_f f δ PV PW hE3 hPW hδP] at h
  omega

include hE1 hE2 hPV hiP in
/-- Without a condition on δ: the dimensions of the low parts of V' and V differ by at most the
dimension of W. -/
theorem finrank_low_near [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 V']
    [FiniteDimensional 𝕜 W] :
    finrank 𝕜 (LinearMap.range PV') ≤ finrank 𝕜 (LinearMap.range PV) + finrank 𝕜 W ∧
      finrank 𝕜 (LinearMap.range PV) ≤ finrank 𝕜 (LinearMap.range PV') + finrank 𝕜 W := by
  have h1 := finrank_eq_inf_ker_add_map i (LinearMap.range PV')
  have h2 : finrank 𝕜 (LinearMap.range PV' ⊓ LinearMap.ker i : Submodule 𝕜 V') ≤
      finrank 𝕜 (LinearMap.range f) := by
    rw [← hE1]
    exact Submodule.finrank_mono inf_le_right
  have h3 := LinearMap.finrank_range_le f
  have h4 : finrank 𝕜 ((LinearMap.range PV').map i) ≤ finrank 𝕜 (LinearMap.range PV) := by
    rw [low_map i δ PV PV' hE2 hPV hiP]
    exact Submodule.finrank_mono inf_le_left
  have h5 := finrank_eq_inf_ker_add_map δ (LinearMap.range PV)
  rw [← low_map i δ PV PV' hE2 hPV hiP] at h5
  have h6 := Submodule.finrank_map_le i (LinearMap.range PV')
  have h7 := Submodule.finrank_map_le δ (LinearMap.range PV)
  have h8 := Submodule.finrank_le ((LinearMap.range PV).map δ)
  omega

/-! ### One ambient row -/

section Row

variable {X X' Cp Cn : Type*} [AddCommGroup X] [Module 𝕜 X] [AddCommGroup X'] [Module 𝕜 X']
  [AddCommGroup Cp] [Module 𝕜 Cp] [AddCommGroup Cn] [Module 𝕜 Cn]
  (ρ : X' →ₗ[𝕜] X) (d : X →ₗ[𝕜] Cn) (g : Cp →ₗ[𝕜] X')
  (ε : X →ₗ[𝕜] V) (ε' : X' →ₗ[𝕜] V') (lp : Cp →ₗ[𝕜] W) (ln : Cn →ₗ[𝕜] W)
  (hX : LinearMap.ker d = LinearMap.range ρ)
  (hiε : ∀ a', i (ε' a') = ε (ρ a')) (hδε : ∀ a, δ (ε a) = ln (d a))
  (hεg : ∀ c, ε' (g c) = f (lp c))
  (hlp : LinearMap.range PW ≤ LinearMap.range lp) (hln : Function.Injective ln)
  (hlnP : LinearMap.range ln ≤ LinearMap.range PW)

include hPW hδP hδε hlnP in
/-- On the image of ε the connecting map does not see the high part. -/
theorem delta_proj (a : X) : δ (PV (ε a)) = δ (ε a) := by
  obtain ⟨w, hw⟩ := hlnP ⟨d a, rfl⟩
  rw [hδP, hδε, ← hw, hPW]

include hE1 hPV' hfP hεg hlp in
/-- The projected image of ε' meets the kernel of i in the image of the low part of W. -/
theorem row_inf_ker :
    (LinearMap.range ε').map PV' ⊓ LinearMap.ker i = (LinearMap.range PW).map f := by
  apply le_antisymm
  · rw [← low_inf_ker f i PV' PW hE1 hPV' hfP]
    refine inf_le_inf_right _ ?_
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := hlp ⟨w, rfl⟩
    refine ⟨⟨ε' (g c), ⟨g c, rfl⟩, ?_⟩, ?_⟩
    · rw [hεg, hc, hfP, hPV']
    · rw [hE1]
      exact ⟨PW w, rfl⟩

include hE2 hPW hiP hδP hX hiε hδε hln hlnP in
/-- The image under i of the projected image of ε' is the kernel of δ on the projected image of
ε. -/
theorem row_map :
    ((LinearMap.range ε').map PV').map i =
      (LinearMap.range ε).map PV ⊓ LinearMap.ker δ := by
  ext x
  constructor
  · rintro ⟨_, ⟨_, ⟨a', rfl⟩, rfl⟩, rfl⟩
    refine ⟨⟨ε (ρ a'), ⟨ρ a', rfl⟩, ?_⟩, ?_⟩
    · rw [← hiε, hiP]
    · rw [hE2]
      exact ⟨_, rfl⟩
  · rintro ⟨⟨_, ⟨a, rfl⟩, rfl⟩, hx⟩
    have h0 : ln (d a) = 0 := by
      rw [← hδε, ← delta_proj δ PV PW hPW hδP d ε ln hδε hlnP a]
      exact LinearMap.mem_ker.mp hx
    have hda : d a = 0 := hln (h0.trans (map_zero ln).symm)
    have hmem : a ∈ LinearMap.range ρ := by
      rw [← hX]
      exact LinearMap.mem_ker.mpr hda
    obtain ⟨a', rfl⟩ := hmem
    refine ⟨PV' (ε' a'), ⟨ε' a', ⟨a', rfl⟩, rfl⟩, ?_⟩
    rw [hiP, hiε]

include hE1 hE2 hPV' hPW hfP hiP hδP hX hiε hδε hεg hlp hln hlnP in
/-- dim PE' + rank(δ on PE) = dim f(P W) + dim PE. -/
theorem finrank_row [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 V'] :
    finrank 𝕜 ((LinearMap.range ε').map PV') +
        finrank 𝕜 (((LinearMap.range ε).map PV).map δ) =
      finrank 𝕜 ((LinearMap.range PW).map f) + finrank 𝕜 ((LinearMap.range ε).map PV) := by
  have h1 := finrank_eq_inf_ker_add_map i ((LinearMap.range ε').map PV')
  rw [row_inf_ker f i PV' PW hE1 hPV' hfP g ε' lp hεg hlp,
    row_map i δ PV PV' PW hE2 hPW hiP hδP ρ d ε ε' ln hX hiε hδε hln hlnP] at h1
  have h2 := finrank_eq_inf_ker_add_map δ ((LinearMap.range ε).map PV)
  omega

include hPW hδP hδε hln hlnP in
/-- The rank of the ambient connecting map is the rank of δ on the projected image of ε. -/
theorem finrank_range_d [FiniteDimensional 𝕜 X] :
    finrank 𝕜 (LinearMap.range d) = finrank 𝕜 (((LinearMap.range ε).map PV).map δ) := by
  have h := finrank_eq_inf_ker_add_map ln (LinearMap.range d)
  rw [LinearMap.ker_eq_bot.mpr hln, inf_bot_eq, finrank_bot, zero_add] at h
  have e : (LinearMap.range d).map ln = ((LinearMap.range ε).map PV).map δ := by
    ext w
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨PV (ε a), ⟨ε a, ⟨a, rfl⟩, rfl⟩,
        (delta_proj δ PV PW hPW hδP d ε ln hδε hlnP a).trans (hδε a)⟩
    · rintro ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩
      exact ⟨d a, ⟨a, rfl⟩,
        ((delta_proj δ PV PW hPW hδP d ε ln hδε hlnP a).trans (hδε a)).symm⟩
  rw [h, e]

include hE1 hiP hX hiε in
/-- Without conditions on the comparison of the crossing groups: the dimensions of the projected
images of ε' and ε differ by at most the dimensions of W and of the next crossing group. -/
theorem finrank_row_near [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 V']
    [FiniteDimensional 𝕜 W] [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Cn] :
    finrank 𝕜 ((LinearMap.range ε').map PV') ≤
        finrank 𝕜 ((LinearMap.range ε).map PV) + finrank 𝕜 W ∧
      finrank 𝕜 ((LinearMap.range ε).map PV) ≤
        finrank 𝕜 ((LinearMap.range ε').map PV') + finrank 𝕜 Cn := by
  have e : ((LinearMap.range ε').map PV').map i = (LinearMap.ker d).map (PV ∘ₗ ε) := by
    rw [hX]
    ext x
    constructor
    · rintro ⟨_, ⟨_, ⟨a', rfl⟩, rfl⟩, rfl⟩
      exact ⟨ρ a', ⟨a', rfl⟩, by rw [hiP, hiε]; rfl⟩
    · rintro ⟨_, ⟨a', rfl⟩, rfl⟩
      exact ⟨PV' (ε' a'), ⟨ε' a', ⟨a', rfl⟩, rfl⟩, by rw [hiP, hiε]; rfl⟩
  have h1 := finrank_eq_inf_ker_add_map i ((LinearMap.range ε').map PV')
  have h2 : finrank 𝕜 ((LinearMap.range ε').map PV' ⊓ LinearMap.ker i : Submodule 𝕜 V') ≤
      finrank 𝕜 (LinearMap.range f) := by
    rw [← hE1]
    exact Submodule.finrank_mono inf_le_right
  have h3 := LinearMap.finrank_range_le f
  have h4 : finrank 𝕜 (((LinearMap.range ε').map PV').map i) ≤
      finrank 𝕜 ((LinearMap.range ε).map PV) := by
    rw [e, ← LinearMap.range_comp]
    exact Submodule.finrank_mono LinearMap.map_le_range
  have h5 := finrank_range_le_ker_map (PV ∘ₗ ε) d
  rw [← e, LinearMap.range_comp] at h5
  have h6 := Submodule.finrank_map_le i ((LinearMap.range ε').map PV')
  have h7 := Submodule.finrank_le (LinearMap.range d)
  omega

end Row

end Fixed

/-! ### The two rows of a cutoff -/

section Cutoff

variable {𝕜 : Type*} [Field 𝕜] {V V' W A A' B B' C₀ C₁ C₂ : Type*}
  [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
  [AddCommGroup V'] [Module 𝕜 V'] [FiniteDimensional 𝕜 V']
  [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W]
  [AddCommGroup A] [Module 𝕜 A] [FiniteDimensional 𝕜 A]
  [AddCommGroup A'] [Module 𝕜 A'] [FiniteDimensional 𝕜 A']
  [AddCommGroup B] [Module 𝕜 B] [FiniteDimensional 𝕜 B]
  [AddCommGroup B'] [Module 𝕜 B']
  [AddCommGroup C₀] [Module 𝕜 C₀]
  [AddCommGroup C₁] [Module 𝕜 C₁] [FiniteDimensional 𝕜 C₁]
  [AddCommGroup C₂] [Module 𝕜 C₂]
  (f : W →ₗ[𝕜] V') (i : V' →ₗ[𝕜] V) (δ : V →ₗ[𝕜] W)
  (PV : V →ₗ[𝕜] V) (PV' : V' →ₗ[𝕜] V') (PW : W →ₗ[𝕜] W)
  (d₀ : B →ₗ[𝕜] C₁) (g₁ : C₁ →ₗ[𝕜] A') (ρ : A' →ₗ[𝕜] A) (d₁ : A →ₗ[𝕜] C₂)
  (g₀ : C₀ →ₗ[𝕜] B') (ρ₀ : B' →ₗ[𝕜] B)
  (εA : A →ₗ[𝕜] V) (εA' : A' →ₗ[𝕜] V') (εB : B →ₗ[𝕜] V) (εB' : B' →ₗ[𝕜] V')
  (l₀ : C₀ →ₗ[𝕜] W) (l₁ : C₁ →ₗ[𝕜] W) (l₂ : C₂ →ₗ[𝕜] W)

/-- The far cutoff: the exact change of the dimensions entering the potential. -/
theorem far_change
    (hE1 : LinearMap.ker i = LinearMap.range f) (hE2 : LinearMap.ker δ = LinearMap.range i)
    (hE3 : LinearMap.ker f = LinearMap.range δ)
    (hPV : ∀ x, PV (PV x) = PV x) (hPV' : ∀ y, PV' (PV' y) = PV' y)
    (hPW : ∀ w, PW (PW w) = PW w)
    (hfP : ∀ w, f (PW w) = PV' (f w)) (hiP : ∀ y, i (PV' y) = PV (i y))
    (hδP : ∀ v, δ (PV v) = PW (δ v))
    (hC₁ : LinearMap.ker g₁ = LinearMap.range d₀) (hA' : LinearMap.ker ρ = LinearMap.range g₁)
    (hA : LinearMap.ker d₁ = LinearMap.range ρ) (hB : LinearMap.ker d₀ = LinearMap.range ρ₀)
    (hiεA : ∀ a', i (εA' a') = εA (ρ a')) (hiεB : ∀ b', i (εB' b') = εB (ρ₀ b'))
    (hδεA : ∀ a, δ (εA a) = l₂ (d₁ a)) (hδεB : ∀ b, δ (εB b) = l₁ (d₀ b))
    (hεgA : ∀ c, εA' (g₁ c) = f (l₁ c)) (hεgB : ∀ c, εB' (g₀ c) = f (l₀ c))
    (hl₀ : LinearMap.range PW ≤ LinearMap.range l₀)
    (hl₁ : Function.Injective l₁) (hl₁P : LinearMap.range l₁ = LinearMap.range PW)
    (hl₂ : Function.Injective l₂) (hl₂P : LinearMap.range l₂ ≤ LinearMap.range PW) :
    2 * finrank 𝕜 (LinearMap.range PV') + finrank 𝕜 A' +
        2 * finrank 𝕜 ((LinearMap.range εA).map PV) + finrank 𝕜 ((LinearMap.range εB).map PV) +
        finrank 𝕜 ((LinearMap.range PV).map δ) =
      2 * finrank 𝕜 (LinearMap.range PV) + finrank 𝕜 A +
        2 * finrank 𝕜 ((LinearMap.range εA').map PV') +
        finrank 𝕜 ((LinearMap.range εB').map PV') +
        finrank 𝕜 (((LinearMap.range εA).map PV).map δ) := by
  have hc := finrank_low f i δ PV PV' PW hE1 hE2 hPV hPV' hfP hiP
  have hd := finrank_lowW f δ PV PW hE3 hPW hδP
  have haA := finrank_row f i δ PV PV' PW hE1 hE2 hPV' hPW hfP hiP hδP ρ d₁ g₁ εA εA' l₁ l₂
    hA hiεA hδεA hεgA hl₁P.ge hl₂ hl₂P
  have haB := finrank_row f i δ PV PV' PW hE1 hE2 hPV' hPW hfP hiP hδP ρ₀ d₀ g₀ εB εB' l₀ l₁
    hB hiεB hδεB hεgB hl₀ hl₁ hl₁P.le
  have hbA := finrank_range_d δ PV PW hPW hδP d₁ εA l₂ hδεA hl₂ hl₂P
  have hbB := finrank_range_d δ PV PW hPW hδP d₀ εB l₁ hδεB hl₁ hl₁P.le
  have h1 := LinearMap.finrank_range_add_finrank_ker ρ
  have h2 := LinearMap.finrank_range_add_finrank_ker g₁
  have h3 := LinearMap.finrank_range_add_finrank_ker d₁
  rw [hA'] at h1
  rw [hC₁] at h2
  rw [hA] at h3
  have h4 : finrank 𝕜 C₁ = finrank 𝕜 (LinearMap.range PW) := by
    rw [← hl₁P]
    exact (LinearMap.finrank_range_of_inj hl₁).symm
  omega

/-- The far cutoff: the potential changes by minus the difference of the rank of δ on the low
part and on the projected image, and does not increase. -/
theorem far_potential
    (hE1 : LinearMap.ker i = LinearMap.range f) (hE2 : LinearMap.ker δ = LinearMap.range i)
    (hE3 : LinearMap.ker f = LinearMap.range δ)
    (hPV : ∀ x, PV (PV x) = PV x) (hPV' : ∀ y, PV' (PV' y) = PV' y)
    (hPW : ∀ w, PW (PW w) = PW w)
    (hfP : ∀ w, f (PW w) = PV' (f w)) (hiP : ∀ y, i (PV' y) = PV (i y))
    (hδP : ∀ v, δ (PV v) = PW (δ v))
    (hC₁ : LinearMap.ker g₁ = LinearMap.range d₀) (hA' : LinearMap.ker ρ = LinearMap.range g₁)
    (hA : LinearMap.ker d₁ = LinearMap.range ρ) (hB : LinearMap.ker d₀ = LinearMap.range ρ₀)
    (hiεA : ∀ a', i (εA' a') = εA (ρ a')) (hiεB : ∀ b', i (εB' b') = εB (ρ₀ b'))
    (hδεA : ∀ a, δ (εA a) = l₂ (d₁ a)) (hδεB : ∀ b, δ (εB b) = l₁ (d₀ b))
    (hεgA : ∀ c, εA' (g₁ c) = f (l₁ c)) (hεgB : ∀ c, εB' (g₀ c) = f (l₀ c))
    (hl₀ : LinearMap.range PW ≤ LinearMap.range l₀)
    (hl₁ : Function.Injective l₁) (hl₁P : LinearMap.range l₁ = LinearMap.range PW)
    (hl₂ : Function.Injective l₂) (hl₂P : LinearMap.range l₂ ≤ LinearMap.range PW) :
    potential (finrank 𝕜 (LinearMap.range PV')) (finrank 𝕜 ((LinearMap.range εA').map PV'))
        (finrank 𝕜 ((LinearMap.range εB').map PV')) (finrank 𝕜 A') =
      potential (finrank 𝕜 (LinearMap.range PV)) (finrank 𝕜 ((LinearMap.range εA).map PV))
        (finrank 𝕜 ((LinearMap.range εB).map PV)) (finrank 𝕜 A) -
        ((finrank 𝕜 ((LinearMap.range PV).map δ) : ℤ) -
          (finrank 𝕜 (((LinearMap.range εA).map PV).map δ) : ℤ)) ∧
    potential (finrank 𝕜 (LinearMap.range PV')) (finrank 𝕜 ((LinearMap.range εA').map PV'))
        (finrank 𝕜 ((LinearMap.range εB').map PV')) (finrank 𝕜 A') ≤
      potential (finrank 𝕜 (LinearMap.range PV)) (finrank 𝕜 ((LinearMap.range εA).map PV))
        (finrank 𝕜 ((LinearMap.range εB).map PV)) (finrank 𝕜 A) := by
  have h := far_change f i δ PV PV' PW d₀ g₁ ρ d₁ g₀ ρ₀ εA εA' εB εB' l₀ l₁ l₂ hE1 hE2 hE3
    hPV hPV' hPW hfP hiP hδP hC₁ hA' hA hB hiεA hiεB hδεA hδεB hεgA hεgB hl₀ hl₁ hl₁P hl₂ hl₂P
  have hle : finrank 𝕜 (((LinearMap.range εA).map PV).map δ) ≤
      finrank 𝕜 ((LinearMap.range PV).map δ) := by
    refine Submodule.finrank_mono (Submodule.map_mono ?_)
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  unfold potential
  constructor <;> omega

/-- A general cutoff: the potential changes by at most six times a bound for the dimensions of
W and of the crossing groups of degrees J and J + 1. -/
theorem near_potential [FiniteDimensional 𝕜 C₂]
    (hE1 : LinearMap.ker i = LinearMap.range f) (hE2 : LinearMap.ker δ = LinearMap.range i)
    (hPV : ∀ x, PV (PV x) = PV x)
    (hiP : ∀ y, i (PV' y) = PV (i y))
    (hA' : LinearMap.ker ρ = LinearMap.range g₁)
    (hA : LinearMap.ker d₁ = LinearMap.range ρ) (hB : LinearMap.ker d₀ = LinearMap.range ρ₀)
    (hiεA : ∀ a', i (εA' a') = εA (ρ a')) (hiεB : ∀ b', i (εB' b') = εB (ρ₀ b'))
    {M : ℕ} (hW : finrank 𝕜 W ≤ M) (hM₁ : finrank 𝕜 C₁ ≤ M) (hM₂ : finrank 𝕜 C₂ ≤ M) :
    potential (finrank 𝕜 (LinearMap.range PV')) (finrank 𝕜 ((LinearMap.range εA').map PV'))
        (finrank 𝕜 ((LinearMap.range εB').map PV')) (finrank 𝕜 A') ≤
      potential (finrank 𝕜 (LinearMap.range PV)) (finrank 𝕜 ((LinearMap.range εA).map PV))
        (finrank 𝕜 ((LinearMap.range εB).map PV)) (finrank 𝕜 A) + 6 * (M : ℤ) ∧
    potential (finrank 𝕜 (LinearMap.range PV)) (finrank 𝕜 ((LinearMap.range εA).map PV))
        (finrank 𝕜 ((LinearMap.range εB).map PV)) (finrank 𝕜 A) ≤
      potential (finrank 𝕜 (LinearMap.range PV')) (finrank 𝕜 ((LinearMap.range εA').map PV'))
        (finrank 𝕜 ((LinearMap.range εB').map PV')) (finrank 𝕜 A') + 6 * (M : ℤ) := by
  have hL := finrank_low_near f i δ PV PV' hE1 hE2 hPV hiP
  have hEA := finrank_row_near f i PV PV' hE1 hiP ρ d₁ εA εA' hA hiεA
  have hEB := finrank_row_near f i PV PV' hE1 hiP ρ₀ d₀ εB εB' hB hiεB
  have h1 := LinearMap.finrank_range_add_finrank_ker ρ
  have h3 := LinearMap.finrank_range_add_finrank_ker d₁
  rw [hA'] at h1
  rw [hA] at h3
  have h5 := LinearMap.finrank_range_le g₁
  have h6 := Submodule.finrank_le (LinearMap.range d₁)
  unfold potential
  constructor <;> omega

end Cutoff

end Finsler.LadderBudget
