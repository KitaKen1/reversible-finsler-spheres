module

public import Finsler.Topology.BorelCoverK

/-! Equivariant maps of pairs of invariant sets of loops on K-Borel cohomology. A continuous map
between sets of loops which commutes with the reversal and the half rotation and maps a subset
into a subset induces a map of K-Borel cochains of the pairs. Maps of iterated Borel complexes
which commute on cochains commute on Borel cohomology. An equivariant self-map of a pair which
is homotopic to the identity through maps of the pair is bijective on K-Borel cohomology; the
homotopy need not be equivariant. Consequently, if such a self-map r of (X, T) maps an
invariant set N ⊇ T into an invariant set O ⊇ T whose K-Borel cohomology relative to T vanishes,
then restriction from (X, T) to (N, T) vanishes on K-Borel cohomology: restriction to (N, T)
after r is r after restriction to (O, T). -/

@[expose] public section

namespace Finsler.EquivariantK

open CategoryTheory Set Topology
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelComparison
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.BorelDeformation Finsler.AvoidPoint Finsler.BorelIterate Finsler.BorelK
open Finsler.BorelLocalK Finsler.BorelCoverK

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-! ### Squares of maps of iterated complexes -/

section Algebra

variable {K₁ K₂ K₃ K₄ : InvComplex} {S₁ : Commuting K₁} {S₂ : Commuting K₂}
  {S₃ : Commuting K₃} {S₄ : Commuting K₄} (Φ₁ : CommHom S₁ S₂) (Φ₂ : CommHom S₂ S₄)
  (Ψ₁ : CommHom S₁ S₃) (Ψ₂ : CommHom S₃ S₄)
  (hcomm : ∀ j x, Φ₂.φ.f j (Φ₁.φ.f j x) = Ψ₂.φ.f j (Ψ₁.φ.f j x))

include hcomm in
/-- Maps of complexes with commuting involutions which commute on cochains commute on the
iterated Borel cohomology. -/
theorem HRmap_borelHom_comm (q : ℕ) (y : HR (borelInv S₁) q) :
    HRmap (borelHom Φ₂) q (HRmap (borelHom Φ₁) q y) =
      HRmap (borelHom Ψ₂) q (HRmap (borelHom Ψ₁) q y) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change (Submodule.Quotient.mk (bcocycleMap (borelHom Φ₂) q (bcocycleMap (borelHom Φ₁) q c)) :
      HR (borelInv S₄) q) =
    Submodule.Quotient.mk (bcocycleMap (borelHom Ψ₂) q (bcocycleMap (borelHom Ψ₁) q c))
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  funext j
  apply Subtype.ext
  funext i
  exact hcomm i _

include hcomm in
/-- In a commuting square, if the first map is onto in degree q and the Borel cohomology of the
other corner vanishes in degree q, the second map vanishes in degree q. -/
theorem HRmap_eq_zero_of_square (q : ℕ) (hsurj : Function.Surjective (HRmap (borelHom Φ₁) q))
    (hzero : ∀ z : HR (borelInv S₃) q, z = 0) (y : HR (borelInv S₂) q) :
    HRmap (borelHom Φ₂) q y = 0 := by
  obtain ⟨y', rfl⟩ := hsurj y
  rw [HRmap_borelHom_comm Φ₁ Φ₂ Ψ₁ Ψ₂ hcomm, hzero (HRmap (borelHom Ψ₁) q y'), map_zero]

end Algebra

/-! ### Equivariant maps of pairs -/

section Maps

variable {s t s' t' : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t)
  (hst' : s' ⊆ t') (hs' : KInv s') (ht' : KInv t') (g : C(t, t'))
  (hg : ∀ x : t, (x : Loops n) ∈ s → (g x : Loops n) ∈ s')
  (hrev : ∀ x : t, (g ⟨reverseSphere (x : SphereLoop n), ht.rev_mem _ x.2⟩ : Loops n) =
    reverseSphere (g x : SphereLoop n))
  (hhalf : ∀ x : t, (g ⟨half +ᵥ (x : SphereLoop n), ht.half_mem _ x.2⟩ : Loops n) =
    half +ᵥ (g x : SphereLoop n))

include hrev in
theorem pairMap_rev :
    pairMap hst hst' g hg ≫ revSub hst' hs'.rev_mem ht'.rev_mem =
      revSub hst hs.rev_mem ht.rev_mem ≫ pairMap hst hst' g hg := by
  have h : (revSet ht'.rev_mem).comp g = g.comp (revSet ht.rev_mem) := by
    ext x
    exact congrArg Subtype.val (Subtype.ext (hrev x).symm :
      (⟨reverseSphere ((g x : t') : SphereLoop n), ht'.rev_mem _ (g x).2⟩ : t') =
        g ⟨reverseSphere (x : SphereLoop n), ht.rev_mem _ x.2⟩)
  exact (pairMap_comp hst hst' hst' g (revSet ht'.rev_mem) hg
    (fun _ hx => hs'.rev_mem _ hx)).symm.trans
    ((pairMap_congr hst hst' h _ (fun x hx => hg _ (hs.rev_mem _ hx))).trans
      (pairMap_comp hst hst hst' (revSet ht.rev_mem) g (fun _ hx => hs.rev_mem _ hx) hg))

include hhalf in
theorem pairMap_half :
    pairMap hst hst' g hg ≫ halfSub hst' hs'.half_mem ht'.half_mem =
      halfSub hst hs.half_mem ht.half_mem ≫ pairMap hst hst' g hg := by
  have h : (halfSet ht'.half_mem).comp g = g.comp (halfSet ht.half_mem) := by
    ext x
    exact congrArg Subtype.val (Subtype.ext (hhalf x).symm :
      (⟨half +ᵥ ((g x : t') : SphereLoop n), ht'.half_mem _ (g x).2⟩ : t') =
        g ⟨half +ᵥ (x : SphereLoop n), ht.half_mem _ x.2⟩)
  exact (pairMap_comp hst hst' hst' g (halfSet ht'.half_mem) hg
    (fun _ hx => hs'.half_mem _ hx)).symm.trans
    ((pairMap_congr hst hst' h _ (fun x hx => hg _ (hs.half_mem _ hx))).trans
      (pairMap_comp hst hst hst' (halfSet ht.half_mem) g (fun _ hx => hs.half_mem _ hx) hg))

/-- The map of K-Borel cochains induced by an equivariant map of pairs of invariant sets of
loops. -/
def eqHom : CommHom (kCommuting hst' hs' ht') (kCommuting hst hs ht) :=
  BorelInvariance.commHom (revSub_sq hst hs.rev_mem ht.rev_mem)
    (revSub_sq hst' hs'.rev_mem ht'.rev_mem) (pairMap hst hst' g hg)
    (pairMap_rev hst hs ht hst' hs' ht' g hg hrev)
    (halfSub_sq hst hs.half_mem ht.half_mem) (halfSub_sq hst' hs'.half_mem ht'.half_mem)
    (halfSub_rev hst hs.rev_mem ht.rev_mem hs.half_mem ht.half_mem)
    (halfSub_rev hst' hs'.rev_mem ht'.rev_mem hs'.half_mem ht'.half_mem)
    (pairMap_half hst hs ht hst' hs' ht' g hg hhalf)

theorem eqHom_f (j : ℕ) (x : (cochains (pairOf hst')).X j) :
    (eqHom hst hs ht hst' hs' ht' g hg hrev hhalf).φ.f j x =
      ((pull (pairMap hst hst' g hg)).f j).hom x := rfl

end Maps

section SelfMaps

variable {s t : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t) (g : C(t, t))
  (hg : ∀ x : t, (x : Loops n) ∈ s → (g x : Loops n) ∈ s)
  (hrev : ∀ x : t, (g ⟨reverseSphere (x : SphereLoop n), ht.rev_mem _ x.2⟩ : Loops n) =
    reverseSphere (g x : SphereLoop n))
  (hhalf : ∀ x : t, (g ⟨half +ᵥ (x : SphereLoop n), ht.half_mem _ x.2⟩ : Loops n) =
    half +ᵥ (g x : SphereLoop n))
  (G : (ContinuousMap.id t).Homotopy g)
  (hG : ∀ (τ : _root_.unitInterval) (x : t), (x : Loops n) ∈ s → (G (τ, x) : Loops n) ∈ s)

include G hG in
/-- An equivariant self-map of a pair of invariant sets of loops which is homotopic to the
identity through maps of the pair is bijective on K-Borel cohomology. The homotopy need not be
equivariant. -/
theorem bijective_eqHom_of_homotopy :
    ∀ q, Function.Bijective
      (HRmap (borelHom (eqHom hst hs ht hst hs ht g hg hrev hhalf)) q) := by
  have hF : ∀ (τ : _root_.unitInterval) (x : t), (x : Loops n) ∈ s → (G.symm (τ, x) : Loops n) ∈ s :=
    fun τ x hx => hG _ x hx
  have H := pairHomotopy hst hst G.symm hF
  have e1 : pairMap hst hst g hg ≫ 𝟙 (pairOf hst) =
      pairMap hst hst g (fun x hx => G.symm.apply_zero x ▸ hF 0 x hx) := Category.comp_id _
  have e1' : 𝟙 (pairOf hst) ≫ pairMap hst hst g hg =
      pairMap hst hst g (fun x hx => G.symm.apply_zero x ▸ hF 0 x hx) := Category.id_comp _
  have e2 : 𝟙 (pairOf hst) = pairMap hst hst (ContinuousMap.id t)
      (fun x hx => G.symm.apply_one x ▸ hF 1 x hx) := (pairMap_id hst).symm
  have H₁ : Nonempty (TopPair.Homotopy (pairMap hst hst g hg ≫ 𝟙 (pairOf hst))
      (𝟙 (pairOf hst))) := by
    rw [e1, e2]
    exact ⟨H⟩
  have H₂ : Nonempty (TopPair.Homotopy (𝟙 (pairOf hst) ≫ pairMap hst hst g hg)
      (𝟙 (pairOf hst))) := by
    rw [e1', e2]
    exact ⟨H⟩
  obtain ⟨H₁⟩ := H₁
  obtain ⟨H₂⟩ := H₂
  exact BorelInvariance.bijective_iterated_of_homotopyEquiv
    (revSub_sq hst hs.rev_mem ht.rev_mem) (revSub_sq hst hs.rev_mem ht.rev_mem)
    (pairMap hst hst g hg) (pairMap_rev hst hs ht hst hs ht g hg hrev)
    (halfSub_sq hst hs.half_mem ht.half_mem) (halfSub_sq hst hs.half_mem ht.half_mem)
    (halfSub_rev hst hs.rev_mem ht.rev_mem hs.half_mem ht.half_mem)
    (halfSub_rev hst hs.rev_mem ht.rev_mem hs.half_mem ht.half_mem)
    (pairMap_half hst hs ht hst hs ht g hg hhalf) (𝟙 (pairOf hst)) H₁ H₂

end SelfMaps

/-! ### Restriction to a set which a deformation maps into a set with vanishing cohomology -/

section Square

variable {T N O X : Set (Loops n)} (hTN : T ⊆ N) (hNX : N ⊆ X) (hTO : T ⊆ O) (hOX : O ⊆ X)
  (hT : KInv T) (hN : KInv N) (hO : KInv O) (hX : KInv X) (r : C(X, X))
  (hrT : ∀ x : X, (x : Loops n) ∈ T → (r x : Loops n) ∈ T)
  (hrN : ∀ x : X, (x : Loops n) ∈ N → (r x : Loops n) ∈ O)
  (hrev : ∀ x : X, (r ⟨reverseSphere (x : SphereLoop n), hX.rev_mem _ x.2⟩ : Loops n) =
    reverseSphere (r x : SphereLoop n))
  (hhalf : ∀ x : X, (r ⟨half +ᵥ (x : SphereLoop n), hX.half_mem _ x.2⟩ : Loops n) =
    half +ᵥ (r x : SphereLoop n))

/-- The restriction of r to N, with values in O. -/
def restr : C(N, O) :=
  ⟨fun x => ⟨r ⟨x, hNX x.2⟩, hrN _ x.2⟩,
    (continuous_subtype_val.comp (r.continuous.comp (continuous_inclusion hNX))).subtype_mk _⟩

/-- Inclusion of (N, T) followed by r is r on N followed by the inclusion of (O, T). -/
theorem square :
    inclPair hTN (hTN.trans hNX) subset_rfl hNX ≫ pairMap (hTN.trans hNX) (hTN.trans hNX) r hrT =
      pairMap hTN hTO (restr hNX r hrN) (fun x hx => hrT ⟨x, hNX x.2⟩ hx) ≫
        inclPair hTO (hTN.trans hNX) subset_rfl hOX := by
  ext : 2 <;> rfl

variable (G : (ContinuousMap.id X).Homotopy r)
  (hG : ∀ (τ : _root_.unitInterval) (x : X), (x : Loops n) ∈ T → (G (τ, x) : Loops n) ∈ T)
  (hzero : ∀ (q : ℕ) (z : HR (borelInv (kCommuting hTO hT hO)) q), z = 0)

include hTO hOX hO hrT hrN hrev hhalf G hG hzero in
/-- If an equivariant self-map r of (X, T), homotopic to the identity through maps of the pair,
maps N into a set O whose K-Borel cohomology relative to T vanishes, then restriction from
(X, T) to (N, T) vanishes on K-Borel cohomology. -/
theorem restriction_eq_zero (q : ℕ) (y : HR (borelInv (kCommuting (hTN.trans hNX) hT hX)) q) :
    HRmap (borelHom (kHom hTN hT hN (hTN.trans hNX) hT hX subset_rfl hNX)) q y = 0 := by
  refine HRmap_eq_zero_of_square
    (eqHom (hTN.trans hNX) hT hX (hTN.trans hNX) hT hX r hrT hrev hhalf)
    (kHom hTN hT hN (hTN.trans hNX) hT hX subset_rfl hNX)
    (kHom hTO hT hO (hTN.trans hNX) hT hX subset_rfl hOX)
    (eqHom hTN hT hN hTO hT hO (restr hNX r hrN) (fun x hx => hrT ⟨x, hNX x.2⟩ hx)
      (fun x => hrev ⟨x, hNX x.2⟩) (fun x => hhalf ⟨x, hNX x.2⟩))
    (fun j x => ?_) q
    ((bijective_eqHom_of_homotopy (hTN.trans hNX) hT hX r hrT hrev hhalf G hG q).2)
    (hzero q) y
  have h1 := pull_comp_apply (inclPair hTN (hTN.trans hNX) subset_rfl hNX)
    (pairMap (hTN.trans hNX) (hTN.trans hNX) r hrT) j x
  have h2 := pull_comp_apply (pairMap hTN hTO (restr hNX r hrN)
    (fun x hx => hrT ⟨x, hNX x.2⟩ hx)) (inclPair hTO (hTN.trans hNX) subset_rfl hOX) j x
  rw [square hTN hNX hTO hOX r hrT hrN] at h1
  exact h1.symm.trans h2

end Square

end

end Finsler.EquivariantK
