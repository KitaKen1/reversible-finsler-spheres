module

public import Finsler.Topology.JoinThomCocycle

/-! An actual far-supported primitive compares the normalized join Thom
cochain with the specified original representative. The correction cap
also factors through the same bounded near-pair domain. -/

@[expose] public section
namespace Finsler.JoinThomPrimitive

open CategoryTheory AlgebraicTopology HomologicalComplex SphereOddDegree MonoidalCategory
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedFilteredJoinComparison Finsler.JoinThomCocycle
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.PairDistanceCover Finsler.CompactH1Alignment
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {n : ℕ} (F : ReversibleMetric n) (p q : ℝ)

def specified (hn : 1 ≤ n) :
    singularCochainGroup (ZMod 2) (lengthSpace F p ⊗ lengthSpace F q) n :=
  cochainPullback (evaluation F p q) n (DiagonalCocycle.ambientCocycle n hn)

def primitive (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    singularCochainGroup (ZMod 2) (lengthSpace F p ⊗ lengthSpace F q) (n - 1) :=
  cochainPullback (evaluation F p q) (n - 1)
    (NormalizedThomComparison.ambientPrimitive n hn hρ hρ2)

theorem primitive_boundary (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    ((cochainCxZMod2 (lengthSpace F p ⊗ lengthSpace F q)).d (n - 1) n).hom
      (primitive F p q hn hρ hρ2) =
        cocycle F p q (by omega) hρ - specified F p q (by omega) := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (evaluation F p q).op).comm (n - 1) n)
    (NormalizedThomComparison.ambientPrimitive n hn hρ hρ2)
  change ((cochainCxZMod2 (lengthSpace F p ⊗ lengthSpace F q)).d (n - 1) n).hom
      (primitive F p q hn hρ hρ2) =
    ((singularCochainComplexZMod2.map (evaluation F p q).op).f n).hom
      (((cochainCxZMod2 (DiagonalCohomology.product n)).d (n - 1) n).hom
        (NormalizedThomComparison.ambientPrimitive n hn hρ hρ2)) at he
  rw [he, NormalizedThomComparison.ambientPrimitive_boundary, map_sub]
  rfl

theorem primitive_far_zero (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    cochainPullback (SupportedCap.subspaceMap (lengthSpace F p ⊗ lengthSpace F q)
      (NearFarCapComparison.far (basePoint F p) (basePoint F q) ρ)) (n - 1)
      (primitive F p q hn hρ hρ2) = 0 := by
  apply pullback_support (evaluation F p q)
    (NearFarCapComparison.far (basePoint F p) (basePoint F q) ρ)
    (DiagonalAvoidanceCocycle.far n ρ) ?_ (n - 1)
    (NormalizedThomComparison.ambientPrimitive n hn hρ hρ2)
    (NormalizedThomComparison.ambientPrimitive_supported n hn hρ hρ2)
  intro z hz
  change ρ ≤ ‖basepoint z.2.val - basepoint z.1.val‖
  change ρ ≤ dist (basepoint z.1.val) (basepoint z.2.val) at hz
  simpa only [dist_eq_norm, norm_sub_rev] using hz

variable (hp : 0 ≤ p) (hq : 0 ≤ q) {ε : ℝ} (hε : 0 < ε)

theorem witnessRadius_le_two : witnessRadius F p q hp hq hε ≤ 2 := by
  have h := (FilteredOriginalJoin.radius_spec F p q hp hq hε).2.1
  change FilteredOriginalJoin.radius F p q hp hq hε / 2 ≤ 2
  linarith

theorem cap_factor (hn : 2 ≤ n) (i j t : ℕ) (h : (n - 1) + t = i + j + 1)
    (σ : ((lengthSpace F p).smallSingularSubcomplex
      (cover (basePoint F p) (witnessRadius F p q hp hq hε / 4)) : SSet) _⦋i⦌)
    (τ : ((lengthSpace F q).smallSingularSubcomplex
      (cover (basePoint F q) (witnessRadius F p q hp hq hε / 4)) : SSet) _⦋j⦌) :
    ∃ d : coeff ⟶ (chains (TopCat.of (JoinRectangleComparison.flatDomain F p q hp hq hε))).X t,
      d ≫ (push (SupportedCap.subspaceMap (JoinRectangleComparison.pairSpace n)
        (JoinRectangleComparison.flatDomain F p q hp hq hε))).f t =
      NearFarCapComparison.prism (basePoint F p) (basePoint_continuous F p)
        (basePoint F q) (basePoint_continuous F q) (witnessRadius F p q hp hq hε)
        (witnessRadius_pos F p q hp hq hε) i j σ.val τ.val ≫
          absoluteChain (lengthSpace F p ⊗ lengthSpace F q) (n - 1) t (i + j + 1) h
            (primitive F p q hn (witnessRadius_pos F p q hp hq hε)
              (witnessRadius_le_two F p q hp hq hε)) ≫
              (push (SupportedFilteredJoinComparison.inputMap F p q)).f t :=
  SupportedFilteredJoinComparison.cap_factor F p q hp hq hε i j (n - 1) t h σ τ
    (primitive F p q hn (witnessRadius_pos F p q hp hq hε)
      (witnessRadius_le_two F p q hp hq hε))
    (primitive_far_zero F p q hn (witnessRadius_pos F p q hp hq hε)
      (witnessRadius_le_two F p q hp hq hε))

end
end Finsler.JoinThomPrimitive
