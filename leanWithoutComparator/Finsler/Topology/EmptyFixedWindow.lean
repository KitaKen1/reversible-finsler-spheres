module

public import Finsler.Topology.OddCirclePacket
public import Finsler.Topology.PacketSymmetry
public import Finsler.Topology.FixedAmbientNormalize
public import Finsler.Topology.PolyPieces

/-! a region disjoint from the
half-fixed set contributes no fixed piece. Apply this to half-fixed-free packet tubes and
their reversal pairs. No fixed-label comparison for even iterates is asserted. -/

@[expose] public section

namespace Finsler.EmptyFixedWindow

open CategoryTheory Set Finsler.SphereGeometry Finsler.Geometry Finsler.LocalLabelPacket
open Finsler.AmbientPenalty Finsler.AmbientK Finsler.FixedAmbientNormalize
open Finsler.FlowLens Finsler.InvPairs Finsler.PolySplit Finsler.BorelIterate
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.BorelFreeK Finsler.BorelComparison Finsler.LensFamily Finsler.LensK
open Finsler.AmbientSymmetry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem HR_gComplex_eq_zero {X : TopCat.{0}} (k : KAct X) {s t : Set X}
    (hst : s ⊆ t) (hts : t ⊆ s) (hs : Inv k s) (ht : Inv k t) (q : ℕ)
    (x : HR (gComplex k hst hs ht) q) : x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mk_eq_zero_iff_bcoboundary]
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [map_zero]
  funext j
  exact (Finsler.SmallLevel.relative_eq_zero hst hts j _).symm

theorem HK_gComplex_eq_zero {X : TopCat.{0}} (k : KAct X) {s t : Set X}
    (hst : s ⊆ t) (hts : t ⊆ s) (hs : Inv k s) (ht : Inv k t) (q : ℕ)
    (x : HR (borelInv (gCommuting k hst hs ht)) q) : x = 0 :=
  HR_borelInv_eq_zero (gCommuting k hst hs ht)
    (fun j => HR_gComplex_eq_zero k hst hts hs ht j) q x

theorem fixedPart_eq_zero {W : TopCat.{0}} (k : KAct W) {Z : Set W} (hZ : Inv k Z)
    {g : W → ℝ} (hgρ : ∀ w, g (k.ρ w) = g w) (hgσ : ∀ w, g (k.σ w) = g w)
    (D : Descent W g)
    (hDρ : ∀ t w, D.flow t (k.ρ w) = k.ρ (D.flow t w))
    (hDσ : ∀ t w, D.flow t (k.σ w) = k.σ (D.flow t w))
    (a' a b T : ℝ) {J : Type} (U : J → Set W) (hU : ∀ i, Inv k (U i))
    (i : J) (hempty : U i ∩ Z = ∅) (q : ℕ)
    (x : HR (fixPartComplex k hZ hgρ hgσ D hDρ hDσ a' a b T U hU i) q) : x = 0 := by
  apply HR_gComplex_eq_zero k _ _ _ _ q x
  intro w hw
  exact False.elim (Set.notMem_empty w (hempty ▸ ⟨hw.2, hw.1.2.2⟩))

variable {n M : ℕ} [NeZero M] {F : ReversibleMetric n}
variable {c η : ℝ} {Γ : Set (ZMod (2 * M) → Ambient n)} {d : Packet n (2 * M)}

theorem big_fixed_empty (hd : Analytic F c η Γ d)
    (hfree : ∀ y ∈ d.U, rotA (2 * M) (M : ZMod (2 * M)) y ≠ y) :
    d.big ∩ fixOm M = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro Q hQ
  have h := Finsler.OddCirclePacket.big_fixed_empty F hd (M : ZMod (2 * M)) hfree
  have hm : Q ∈ {Q : Om n (2 * M) | Q ∈ d.big ∧
      rotA (2 * M) (M : ZMod (2 * M)) Q.1 = Q.1} :=
    ⟨hQ.1, congrArg Subtype.val hQ.2⟩
  exact Set.notMem_empty Q (h ▸ hm)

theorem orbitBig_fixed_empty {ι : Type*} (d : ι → Packet n (2 * M)) (i : ι)
    (hempty : (d i).big ∩ fixOm M = ∅) :
    Finsler.PacketSymmetry.orbitBig d i ∩ fixOm M = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro Q hQ
  rcases hQ.1 with hp | hn
  · exact Set.notMem_empty Q (hempty ▸ ⟨hp, hQ.2⟩)
  · have hρ : (ambK M).ρ Q ∈ (d i).big ∩ fixOm M :=
      ⟨hn, (fixOm_invariant M).ρ_mem Q hQ.2⟩
    exact Set.notMem_empty ((ambK M).ρ Q) (hempty ▸ hρ)

end

end Finsler.EmptyFixedWindow
