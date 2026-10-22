module

public import Finsler.Topology.PieceAdditive

/-! Pairs of invariant sets for two commuting involutions of a space. Let ρ and σ be commuting
involutive continuous self-maps of a space X (for instance the reversal and the half rotation of
the vertices of polygons). For subsets s ⊆ t invariant under both, they restrict to commuting
involutions of the pair (t, s), so the relative cochains carry two commuting involutions
(`gCommuting`), and inclusions of such pairs commute with them (`gHom`). An inclusion inducing
isomorphisms on actual relative cohomology induces isomorphisms on the iterated Borel cohomology
(the comparison principle of `BorelInvariance`; homotopies need not be equivariant), and for
pairwise disjoint invariant open sets covering t the restrictions to the parts are jointly
bijective on cochains and on the iterated Borel cohomology (`PieceAdditive`, `OrbitAssembly`).
This is the setting for the K-Borel cohomology of pairs of polygons. -/

@[expose] public section

namespace Finsler.InvPairs

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelDeformation Finsler.BorelIterate Finsler.PairAdditive Finsler.PieceAdditive
open Finsler.BorelComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Two commuting involutive continuous self-maps of a space. -/
structure KAct (X : TopCat.{0}) where
  ρ : C(X, X)
  σ : C(X, X)
  ρρ : ∀ x, ρ (ρ x) = x
  σσ : ∀ x, σ (σ x) = x
  ρσ : ∀ x, ρ (σ x) = σ (ρ x)

variable {X : TopCat.{0}} (k : KAct X)

/-- A set invariant under both involutions. -/
structure Inv (A : Set X) : Prop where
  ρ_mem : ∀ x ∈ A, k.ρ x ∈ A
  σ_mem : ∀ x ∈ A, k.σ x ∈ A

variable {k}

theorem inv_inter {A B : Set X} (hA : Inv k A) (hB : Inv k B) : Inv k (A ∩ B) :=
  ⟨fun x hx => ⟨hA.ρ_mem x hx.1, hB.ρ_mem x hx.2⟩, fun x hx => ⟨hA.σ_mem x hx.1, hB.σ_mem x hx.2⟩⟩

/-- A continuous self-map restricted to an invariant set. -/
def restrictSet (f : C(X, X)) {t : Set X} (ht : ∀ x ∈ t, f x ∈ t) : C(t, t) :=
  ⟨fun u => ⟨f u, ht _ u.2⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- A continuous self-map as a map of a pair of invariant sets. -/
def restrictPair (f : C(X, X)) {s t : Set X} (hst : s ⊆ t) (hs : ∀ x ∈ s, f x ∈ s)
    (ht : ∀ x ∈ t, f x ∈ t) : pairOf hst ⟶ pairOf hst :=
  pairMap hst hst (restrictSet f ht) (fun _ hx => hs _ hx)

theorem restrictPair_sq (f : C(X, X)) (hf : ∀ x, f (f x) = x) {s t : Set X} (hst : s ⊆ t)
    (hs : ∀ x ∈ s, f x ∈ s) (ht : ∀ x ∈ t, f x ∈ t) :
    restrictPair f hst hs ht ≫ restrictPair f hst hs ht = 𝟙 (pairOf hst) := by
  have h : (restrictSet f ht).comp (restrictSet f ht) = ContinuousMap.id t := by
    ext u
    exact hf _
  exact (pairMap_comp hst hst hst (restrictSet f ht) (restrictSet f ht) (fun _ hx => hs _ hx)
    (fun _ hx => hs _ hx)).symm.trans ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans
      (pairMap_id _))

theorem restrictPair_comm (f g : C(X, X)) (hfg : ∀ x, f (g x) = g (f x)) {s t : Set X}
    (hst : s ⊆ t) (hfs : ∀ x ∈ s, f x ∈ s) (hft : ∀ x ∈ t, f x ∈ t) (hgs : ∀ x ∈ s, g x ∈ s)
    (hgt : ∀ x ∈ t, g x ∈ t) :
    restrictPair g hst hgs hgt ≫ restrictPair f hst hfs hft =
      restrictPair f hst hfs hft ≫ restrictPair g hst hgs hgt := by
  ext x
  · exact Subtype.ext (hfg _)
  · exact Subtype.ext (hfg _)

theorem inclPair_restrict (f : C(X, X)) {s t s' t' : Set X} (hst : s ⊆ t) (hst' : s' ⊆ t')
    (hss : s ⊆ s') (htt : t ⊆ t') (hfs : ∀ x ∈ s, f x ∈ s) (hft : ∀ x ∈ t, f x ∈ t)
    (hfs' : ∀ x ∈ s', f x ∈ s') (hft' : ∀ x ∈ t', f x ∈ t') :
    inclPair hst hst' hss htt ≫ restrictPair f hst' hfs' hft' =
      restrictPair f hst hfs hft ≫ inclPair hst hst' hss htt := by
  ext : 2 <;> rfl

variable (k)

/-- The involutive cochains of a pair of invariant sets, for the first involution. -/
abbrev gComplex {s t : Set X} (hst : s ⊆ t) (hs : Inv k s) (ht : Inv k t) : InvComplex :=
  ofPair (pairOf hst) (restrictPair k.ρ hst hs.ρ_mem ht.ρ_mem)
    (restrictPair_sq k.ρ k.ρρ hst hs.ρ_mem ht.ρ_mem)

/-- The second involution on the cochains of a pair of invariant sets. -/
def gCommuting {s t : Set X} (hst : s ⊆ t) (hs : Inv k s) (ht : Inv k t) :
    Commuting (gComplex k hst hs ht) :=
  BorelInvariance.commuting (restrictPair_sq k.ρ k.ρρ hst hs.ρ_mem ht.ρ_mem)
    (restrictPair k.σ hst hs.σ_mem ht.σ_mem) (restrictPair_sq k.σ k.σσ hst hs.σ_mem ht.σ_mem)
    (restrictPair_comm k.ρ k.σ k.ρσ hst hs.ρ_mem ht.ρ_mem hs.σ_mem ht.σ_mem)

/-- Restriction between pairs of invariant sets. -/
def gHom {s t s' t' : Set X} (hst : s ⊆ t) (hs : Inv k s) (ht : Inv k t) (hst' : s' ⊆ t')
    (hs' : Inv k s') (ht' : Inv k t') (hss : s ⊆ s') (htt : t ⊆ t') :
    CommHom (gCommuting k hst' hs' ht') (gCommuting k hst hs ht) :=
  BorelInvariance.commHom (restrictPair_sq k.ρ k.ρρ hst hs.ρ_mem ht.ρ_mem)
    (restrictPair_sq k.ρ k.ρρ hst' hs'.ρ_mem ht'.ρ_mem) (inclPair hst hst' hss htt)
    (inclPair_restrict k.ρ hst hst' hss htt hs.ρ_mem ht.ρ_mem hs'.ρ_mem ht'.ρ_mem)
    (restrictPair_sq k.σ k.σσ hst hs.σ_mem ht.σ_mem)
    (restrictPair_sq k.σ k.σσ hst' hs'.σ_mem ht'.σ_mem)
    (restrictPair_comm k.ρ k.σ k.ρσ hst hs.ρ_mem ht.ρ_mem hs.σ_mem ht.σ_mem)
    (restrictPair_comm k.ρ k.σ k.ρσ hst' hs'.ρ_mem ht'.ρ_mem hs'.σ_mem ht'.σ_mem)
    (inclPair_restrict k.σ hst hst' hss htt hs.σ_mem ht.σ_mem hs'.σ_mem ht'.σ_mem)

/-- **Comparison.** An inclusion of pairs of invariant sets inducing isomorphisms on actual
relative cohomology induces isomorphisms on the iterated Borel cohomology. -/
theorem bijective_gHom {s t s' t' : Set X} (hst : s ⊆ t) (hs : Inv k s) (ht : Inv k t)
    (hst' : s' ⊆ t') (hs' : Inv k s') (ht' : Inv k t') (hss : s ⊆ s') (htt : t ⊆ t')
    (h : ∀ m, Function.Bijective (nativePull (inclPair hst hst' hss htt) m)) :
    ∀ m, Function.Bijective (HRmap (borelHom (gHom k hst hs ht hst' hs' ht' hss htt)) m) :=
  BorelInvariance.bijective_iterated _ _ _ _ _ _ _ _ _ h

/-- **Additivity.** For a pair of invariant sets and pairwise disjoint invariant open sets
covering t, restriction to the parts is jointly bijective on the iterated Borel cohomology. -/
theorem HK_parts_bijective {s t : Set X} (hst : s ⊆ t) (hs : Inv k s) (ht : Inv k t) {J : Type}
    (O : J → Set X) (hOK : ∀ j, Inv k (O j)) (hO : ∀ j, IsOpen (O j))
    (hdis : Pairwise fun i j => Disjoint (O i) (O j)) (hcov : t ⊆ ⋃ j, O j) (q : ℕ) :
    Function.Bijective (LinearMap.pi fun j => HRmap (borelHom
      (gHom k (part_sub hst (O j)) (inv_inter hs (hOK j)) (inv_inter ht (hOK j)) hst hs ht
        inter_subset_left inter_subset_left)) q) :=
  Finsler.OrbitAssembly.HK_pi_bijective _ (pullback_pi_bijective hst O hO hdis hcov) q

/-- Additivity on reflection Borel cohomology. -/
theorem HR_parts_bijective {s t : Set X} (hst : s ⊆ t) (hs : Inv k s) (ht : Inv k t) {J : Type}
    (O : J → Set X) (hOK : ∀ j, Inv k (O j)) (hO : ∀ j, IsOpen (O j))
    (hdis : Pairwise fun i j => Disjoint (O i) (O j)) (hcov : t ⊆ ⋃ j, O j) (q : ℕ) :
    Function.Bijective (LinearMap.pi fun j => HRmap
      (gHom k (part_sub hst (O j)) (inv_inter hs (hOK j)) (inv_inter ht (hOK j)) hst hs ht
        inter_subset_left inter_subset_left).φ q) :=
  Finsler.OrbitAssembly.HR_pi_bijective _ (pullback_pi_bijective hst O hO hdis hcov) q

end

end Finsler.InvPairs
