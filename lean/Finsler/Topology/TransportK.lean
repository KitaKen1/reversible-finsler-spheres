module

public import Finsler.Topology.OrbitAssembly

/-! Transport of the windowed localization. Let X, Xh and X', Xh' be commuting complexes with
restrictions R : X → Xh and R' : X' → Xh', the half rotation acting trivially on Xh and Xh', and
let ι : X' → X and ιh : Xh' → Xh be maps commuting with the restrictions, ι bijective on K-Borel
cohomology and ιh bijective on reflection Borel cohomology in every degree. The family of
components of the restriction, a map from the K-Borel cohomology of degree q to the product of
the reflection Borel groups of the fixed complex, is natural for ι, ιh. Hence it is injective with
image the families of root degrees at most j for X if and only if this holds for X'. This
transports the windowed localization of single crossings along restrictions which are
isomorphisms, for instance from tight cuts around a critical level to wide regular cuts, and from
polygon models to loops. -/

@[expose] public section

namespace Finsler.TransportK

open CategoryTheory Set Module
open Finsler.BorelCochain Finsler.BorelIterate Finsler.TrivialK Finsler.FixedGlobal
open Finsler.FixedLadder Finsler.GradedLadder Finsler.TotalExact Finsler.CrossLocalize

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Xh X' Xh' : InvComplex} {SX : Commuting X} {SXh : Commuting Xh}
  {SX' : Commuting X'} {SXh' : Commuting Xh'} (R : CommHom SX SXh) (R' : CommHom SX' SXh')
  (hXh : ∀ i x, SXh.s i x = x) (hXh' : ∀ i x, SXh'.s i x = x)
  (ι : CommHom SX' SX) (ιh : CommHom SXh' SXh)
  (comm : ∀ i x, R.φ.f i (ι.φ.f i x) = ιh.φ.f i (R'.φ.f i x))

/-- The family of components of the restriction in degree q. -/
abbrev epsK (q : ℕ) :=
  totMap (X := HR (borelInv SXh) q) (G := fun l => HR Xh l) (fun l => theta SXh hXh q l) ∘ₗ
    HRmap (borelHom R) q

include comm in
/-- Naturality of the family of components. -/
theorem epsK_natural (q : ℕ) (x : HR (borelInv SX') q) (l : ℕ) :
    epsK R hXh q (HRmap (borelHom ι) q x) l = HRmap ιh.φ l (epsK R' hXh' q x l) := by
  change theta SXh hXh q l (HRmap (borelHom R) q (HRmap (borelHom ι) q x)) =
    HRmap ιh.φ l (theta SXh' hXh' q l (HRmap (borelHom R') q x))
  rw [← theta_natural hXh' hXh ιh q l]
  congr 1
  exact HRmap_square _ _ _ _ (fun i z => borelHom_square _ _ _ _ (fun m y => comm m y) i z) q x

include comm in
/-- **Transport of the windowed localization.** -/
theorem loc_iff (bijι : ∀ q, Function.Bijective (HRmap (borelHom ι) q))
    (bijιR : ∀ l, Function.Bijective (HRmap ιh.φ l)) (q j : ℕ) :
    (Function.Injective (epsK R hXh q) ∧
      LinearMap.range (epsK R hXh q) = LinearMap.range (cut (fun l => HR Xh l) j)) ↔
    (Function.Injective (epsK R' hXh' q) ∧
      LinearMap.range (epsK R' hXh' q) = LinearMap.range (cut (fun l => HR Xh' l) j)) := by
  have hnat := epsK_natural R R' hXh hXh' ι ιh comm q
  -- the componentwise map of the fixed groups
  have hcut : ∀ y : (l : ℕ) → HR Xh' l,
      (fun l => HRmap ιh.φ l (y l)) ∈ LinearMap.range (cut (fun l => HR Xh l) j) ↔
        y ∈ LinearMap.range (cut (fun l => HR Xh' l) j) := by
    intro y
    rw [mem_range_cut, mem_range_cut]
    refine ⟨fun h l hl => (bijιR l).1 ((h l hl).trans (map_zero _).symm), fun h l hl => ?_⟩
    change HRmap ιh.φ l (y l) = 0
    rw [h l hl, map_zero]
  constructor
  · rintro ⟨hinj, hrange⟩
    refine ⟨fun x y hxy => (bijι q).1 (hinj ?_), ?_⟩
    · funext l
      rw [hnat x l, hnat y l, congrFun hxy l]
    · ext y
      constructor
      · rintro ⟨x, rfl⟩
        rw [← hcut]
        have : epsK R hXh q (HRmap (borelHom ι) q x) ∈ LinearMap.range (epsK R hXh q) := ⟨_, rfl⟩
        rw [hrange] at this
        convert this using 1
        funext l
        exact (hnat x l).symm
      · intro hy
        rw [← hcut, ← hrange] at hy
        obtain ⟨x, hx⟩ := hy
        obtain ⟨x', rfl⟩ := (bijι q).2 x
        refine ⟨x', funext fun l => (bijιR l).1 ?_⟩
        rw [← hnat x' l]
        exact congrFun hx l
  · rintro ⟨hinj, hrange⟩
    refine ⟨fun x y hxy => ?_, ?_⟩
    · obtain ⟨x', rfl⟩ := (bijι q).2 x
      obtain ⟨y', rfl⟩ := (bijι q).2 y
      have : epsK R' hXh' q x' = epsK R' hXh' q y' := funext fun l => (bijιR l).1 (by
        rw [← hnat x' l, ← hnat y' l, hxy])
      rw [hinj this]
    · ext y
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨x', rfl⟩ := (bijι q).2 x
        have h1 : epsK R' hXh' q x' ∈ LinearMap.range (cut (fun l => HR Xh' l) j) := by
          rw [← hrange]
          exact ⟨x', rfl⟩
        rw [← hcut] at h1
        convert h1 using 1
        funext l
        exact hnat x' l
      · intro hy
        let y' : (l : ℕ) → HR Xh' l := fun l => (LinearEquiv.ofBijective _ (bijιR l)).symm (y l)
        have hy' : (fun l => HRmap ιh.φ l (y' l)) = y := funext fun l =>
          (LinearEquiv.ofBijective _ (bijιR l)).apply_symm_apply (y l)
        have hmem : y' ∈ LinearMap.range (cut (fun l => HR Xh' l) j) := by
          rw [← hcut, hy']
          exact hy
        rw [← hrange] at hmem
        obtain ⟨x', hx'⟩ := hmem
        refine ⟨HRmap (borelHom ι) q x', ?_⟩
        rw [← hy']
        funext l
        rw [hnat x' l, hx']

end

end Finsler.TransportK
