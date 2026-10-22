module

public import Finsler.Loop.DiagonalComplementCut
public import Finsler.Topology.NormalizedSelfCut
public import Finsler.Topology.DiagonalSymmetry

/-! Extend the ACTUAL complementary cut to ALL original H1 cut parameters,
not only coincidence points. It swaps the original evaluation pair and
preserves exactly the SAME exterior/neighborhood at EVERY radius. -/
@[expose] public section
namespace Finsler.WholeSelfCutComplement
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SelfCutThomCocycle Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase
open Finsler.SobolevShift Finsler.SobolevCircleAction Finsler.SobolevCircleRepresentative
open Finsler.NativeTripleSelfEvaluation Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

def complement (n : ℕ) : parameters n ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => (unitInterval.symm z.1, shiftSphere z.2 (z.1 : ℝ)), by
    have hs := (H1LoopRotation.homotopy n).continuous
    have ht : Continuous (fun z : parameters n => unitInterval.symm z.1) := by fun_prop
    exact ht.prodMk (hs.congr (fun _ => rfl))⟩

theorem involution (n : ℕ) : complement n ≫ complement n = 𝟙 (parameters n) := by
  ext z : 1
  apply Prod.ext
  · apply Subtype.ext
    change 1 - (1 - (z.1 : ℝ)) = (z.1 : ℝ)
    ring
  · change shiftSphere (shiftSphere z.2 (z.1 : ℝ)) (1 - (z.1 : ℝ)) = z.2
    rw [shiftSphere_add, show (1 - (z.1 : ℝ)) + (z.1 : ℝ) = 1 by ring]
    simpa only [zero_add, shiftSphere_zero] using shiftSphere_periodic z.2 0

theorem point_complement (n : ℕ) (z : parameters n) : point (complement n z).2 = endpoint z := by
  change point (shiftSphere z.2 (z.1 : ℝ)) = endpoint z
  rw [point_shift, sphereCircleMap_coe]
  rfl

theorem endpoint_complement (n : ℕ) (z : parameters n) : endpoint (complement n z) = point z.2 := by
  change sphereRepresentative (shiftSphere z.2 (z.1 : ℝ)) (unitInterval.symm z.1) = point z.2
  rw [endpoint_shift]
  have ha : ((z.1 : ℝ) : SobolevCircleRepresentative.Circle) +
      ((unitInterval.symm z.1 : ℝ) : SobolevCircleRepresentative.Circle) = 0 := by
    rw [← AddCircle.coe_add]
    change (((z.1 : ℝ) + (1 - (z.1 : ℝ)) : ℝ) : SobolevCircleRepresentative.Circle) = 0
    rw [show (z.1 : ℝ) + (1 - (z.1 : ℝ)) = 1 by ring, AddCircle.coe_period]
  rw [ha]
  exact sphereCircleMap_coe z.2 0

theorem selfEvaluation_exchange (n : ℕ) :
    complement n ≫ selfEvaluation n = selfEvaluation n ≫ DiagonalSymmetry.exchange n := by
  ext z : 1
  exact Prod.ext (point_complement n z) (endpoint_complement n z)

theorem distance_complement (n : ℕ) (z : parameters n) : distance n (complement n z) = distance n z := by
  unfold distance
  rw [endpoint_complement, point_complement, norm_sub_rev]

theorem exterior_mapsTo (n : ℕ) (ρ : ℝ) : Set.MapsTo (complement n) (exterior n ρ) (exterior n ρ) := by
  intro z hz
  change ρ < distance n (complement n z)
  rw [distance_complement]
  exact hz

theorem neighborhood_mapsTo (n : ℕ) (r : ℝ) :
    Set.MapsTo (complement n) (neighborhood n r) (neighborhood n r) := by
  intro z hz
  change distance n (complement n z) < r
  rw [distance_complement]
  exact hz

def neighborhoodMap (n : ℕ) (r : ℝ) : TopCat.of (neighborhood n r) ⟶ TopCat.of (neighborhood n r) :=
  SupportedCapNaturality.restriction (complement n) _ _ (neighborhood_mapsTo n r)

theorem neighborhood_involution (n : ℕ) (r : ℝ) :
    neighborhoodMap n r ≫ neighborhoodMap n r = 𝟙 (TopCat.of (neighborhood n r)) := by
  ext z : 1
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (involution n) z.val

def diagonalInclusion (n : ℕ) : DiagonalSelfCutRepresentatives.domain n ⟶ parameters n :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem diagonal_complement (n : ℕ) :
    diagonalInclusion n ≫ complement n = DiagonalComplementCut.complement n ≫ diagonalInclusion n := by
  ext z : 1
  rfl

end
end Finsler.WholeSelfCutComplement
