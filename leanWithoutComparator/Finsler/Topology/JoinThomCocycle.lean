module

public import Finsler.Topology.SupportedFilteredJoinComparison
public import Finsler.Topology.NormalizedThomComparison

/-! The actual normalized diagonal Thom cochain on the two bounded input
spaces. Its restriction to the actual far subspace is literally zero, so
the geometric one-cap comparison needs no assumed support witness. -/

@[expose] public section
namespace Finsler.JoinThomCocycle

open CategoryTheory AlgebraicTopology HomologicalComplex SphereOddDegree MonoidalCategory
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SupportedFilteredJoinComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.PairDistanceCover
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {n : ℕ} (F : ReversibleMetric n) (p q : ℝ)

def evaluation : lengthSpace F p ⊗ lengthSpace F q ⟶ DiagonalCohomology.product n :=
  TopCat.ofHom ⟨fun z => (point z.1.val, point z.2.val),
    (continuous_point.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      (continuous_point.comp (continuous_subtype_val.comp continuous_snd))⟩

def cocycle (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    singularCochainGroup (ZMod 2) (lengthSpace F p ⊗ lengthSpace F q) n :=
  cochainPullback (evaluation F p q) n (NormalizedDiagonalCocycle.ambient n hn hρ)

theorem cocycle_closed (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainCoboundary (ZMod 2) (lengthSpace F p ⊗ lengthSpace F q) n
      (cocycle F p q hn hρ) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 (DiagonalCohomology.product n))
    (singularCochainComplexZMod2.map (evaluation F p q).op) n
    (NormalizedDiagonalCocycle.ambient n hn hρ) (NormalizedDiagonalCocycle.ambient_closed n hn hρ)

theorem cocycle_normalized (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    DoldKan.DegeneraciesVanish
      (X := SingularNormalization.linearization (lengthSpace F p ⊗ lengthSpace F q))
      (cocycle F p q hn hρ) := by
  have he : cocycle F p q hn hρ =
      SingularNormalization.normalize (lengthSpace F p ⊗ lengthSpace F q) n
        (cochainPullback (evaluation F p q) n (DiagonalAvoidanceCocycle.ambientCocycle n hn hρ)) :=
    SingularNormalization.normalize_natural (evaluation F p q) n _
  rw [he]
  exact SingularNormalization.normalize_degeneracies _ n _

theorem cocycle_far_zero (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (lengthSpace F p ⊗ lengthSpace F q)
      (NearFarCapComparison.far (basePoint F p) (basePoint F q) ρ)) n
      (cocycle F p q hn hρ) = 0 := by
  rw [cocycle, ← SupportedCapNaturality.pullback_comp]
  apply NormalizedDiagonalCocycle.pullback_zero_of_far hn hρ
  intro z
  change ρ ≤ ‖basepoint z.val.2.val - basepoint z.val.1.val‖
  have hz := z.property
  change ρ ≤ dist (basepoint z.val.1.val) (basepoint z.val.2.val) at hz
  simpa only [dist_eq_norm, norm_sub_rev] using hz

theorem cocycle_class (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    CochainClass.classOf (cochainCxZMod2 (lengthSpace F p ⊗ lengthSpace F q)) n
      (cocycle F p q hn hρ) (cocycle_closed F p q hn hρ) =
      (cohPullback (evaluation F p q) n).hom (DiagonalCohomology.ambientClass n hn) := by
  rw [← NormalizedDiagonalCocycle.ambient_class n hn hρ]
  exact (CochainClass.classOf_map (cochainCxZMod2 (DiagonalCohomology.product n))
    (singularCochainComplexZMod2.map (evaluation F p q).op) n
    (NormalizedDiagonalCocycle.ambient n hn hρ) (NormalizedDiagonalCocycle.ambient_closed n hn hρ)
    (cocycle_closed F p q hn hρ)).symm

variable (hp : 0 ≤ p) (hq : 0 ≤ q) {ε : ℝ} (hε : 0 < ε)

theorem cap_factor (hn : 1 ≤ n) (i j t : ℕ) (h : n + t = i + j + 1)
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
          absoluteChain (lengthSpace F p ⊗ lengthSpace F q) n t (i + j + 1) h
            (cocycle F p q hn (witnessRadius_pos F p q hp hq hε)) ≫
              (push (inputMap F p q)).f t :=
  SupportedFilteredJoinComparison.cap_factor F p q hp hq hε i j n t h σ τ
    (cocycle F p q hn (witnessRadius_pos F p q hp hq hε))
    (cocycle_far_zero F p q hn (witnessRadius_pos F p q hp hq hε))

end
end Finsler.JoinThomCocycle
