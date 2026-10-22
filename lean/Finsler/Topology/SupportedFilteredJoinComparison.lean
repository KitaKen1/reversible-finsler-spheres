module

public import Finsler.Topology.NearFarCapComparison
public import Finsler.Topology.JoinRectangleComparison

/-! Actual Finsler length-bounded inputs and concrete distance covers.
A cochain vanishing on the actual far subspace sends the capped rectangle
comparison prism into the actual bounded near-pair domain. The genuine
original-join chain homotopy then stays in length <p+q+epsilon. -/

@[expose] public section
namespace Finsler.SupportedFilteredJoinComparison

open CategoryTheory AlgebraicTopology HomologicalComplex SphereOddDegree MonoidalCategory
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SobolevLength Finsler.SupportedCapNaturality Finsler.RelativeCapAssociativity
open Finsler.PairDistanceCover Finsler.VariableJoinContinuity
open scoped Topology Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {n : ℕ}

def lengthSpace (F : ReversibleMetric n) (p : ℝ) : TopCat.{0} :=
  TopCat.of {u : SphereLoop n // length F u ≤ p}

def basePoint (F : ReversibleMetric n) (p : ℝ) (u : lengthSpace F p) : Ambient n := basepoint u.val

theorem basePoint_continuous (F : ReversibleMetric n) (p : ℝ) : Continuous (basePoint F p) :=
  H1AlignmentHomotopy.basepoint_continuous.comp continuous_subtype_val

def inputMap (F : ReversibleMetric n) (p q : ℝ) :
    lengthSpace F p ⊗ lengthSpace F q ⟶ JoinRectangleComparison.pairSpace n :=
  TopCat.ofHom ⟨fun z => (z.1.val, z.2.val),
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)⟩

variable (F : ReversibleMetric n) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
  {ε : ℝ} (hε : 0 < ε)

def witnessRadius : ℝ := FilteredOriginalJoin.radius F p q hp hq hε / 2

theorem witnessRadius_pos : 0 < witnessRadius F p q hp hq hε :=
  half_pos (FilteredOriginalJoin.radius_spec F p q hp hq hε).1

theorem cap_factor (i j k t : ℕ) (h : k + t = i + j + 1)
    (σ : ((lengthSpace F p).smallSingularSubcomplex
      (cover (basePoint F p) (witnessRadius F p q hp hq hε / 4)) : SSet) _⦋i⦌)
    (τ : ((lengthSpace F q).smallSingularSubcomplex
      (cover (basePoint F q) (witnessRadius F p q hp hq hε / 4)) : SSet) _⦋j⦌)
    (φ : singularCochainGroup (ZMod 2) (lengthSpace F p ⊗ lengthSpace F q) k)
    (hφ : cochainPullback (SupportedCap.subspaceMap (lengthSpace F p ⊗ lengthSpace F q)
      (NearFarCapComparison.far (basePoint F p) (basePoint F q) (witnessRadius F p q hp hq hε))) k φ = 0) :
    ∃ d : coeff ⟶ (chains (TopCat.of (JoinRectangleComparison.flatDomain F p q hp hq hε))).X t,
      d ≫ (push (SupportedCap.subspaceMap (JoinRectangleComparison.pairSpace n)
        (JoinRectangleComparison.flatDomain F p q hp hq hε))).f t =
      NearFarCapComparison.prism (basePoint F p) (basePoint_continuous F p)
        (basePoint F q) (basePoint_continuous F q) (witnessRadius F p q hp hq hε)
        (witnessRadius_pos F p q hp hq hε) i j σ.val τ.val ≫
          absoluteChain (lengthSpace F p ⊗ lengthSpace F q) k t (i + j + 1) h φ ≫
            (push (inputMap F p q)).f t := by
  apply NearFarCapComparison.cap_factor (basePoint F p) (basePoint_continuous F p)
    (basePoint F q) (basePoint_continuous F q) (witnessRadius F p q hp hq hε)
    (witnessRadius_pos F p q hp hq hε) i j k t h σ τ φ hφ (inputMap F p q)
    (JoinRectangleComparison.flatDomain F p q hp hq hε)
  intro u _ v _ hnear
  refine ⟨?_, u.property, v.property⟩
  change dist (basepoint u.val) (basepoint v.val) < FilteredOriginalJoin.radius F p q hp hq hε
  change dist (basepoint u.val) (basepoint v.val) < 2 *
    (FilteredOriginalJoin.radius F p q hp hq hε / 2) at hnear
  linarith

def chainHomotopy (a : Splits) : Homotopy
    (push (TopCat.ofHom (JoinRectangleComparison.toDomain F p q hp hq hε)) ≫
      push (TopCat.ofHom (FilteredOriginalJoin.atTime F p q hp hq hε a 0)))
    (push (TopCat.ofHom (JoinRectangleComparison.toDomain F p q hp hq hε)) ≫
      push (TopCat.ofHom (FilteredOriginalJoin.atTime F p q hp hq hε a 1))) :=
  (FilteredOriginalJoin.chainHomotopy F p q hp hq hε a).compLeft
    (push (TopCat.ofHom (JoinRectangleComparison.toDomain F p q hp hq hε)))

theorem homology_eq (a : Splits) (s : ℕ) :
    homologyMap (push (TopCat.ofHom (JoinRectangleComparison.toDomain F p q hp hq hε)) ≫
      push (TopCat.ofHom (FilteredOriginalJoin.atTime F p q hp hq hε a 0))) s =
    homologyMap (push (TopCat.ofHom (JoinRectangleComparison.toDomain F p q hp hq hε)) ≫
      push (TopCat.ofHom (FilteredOriginalJoin.atTime F p q hp hq hε a 1))) s :=
  (chainHomotopy F p q hp hq hε a).homologyMap_eq s

end
end Finsler.SupportedFilteredJoinComparison
