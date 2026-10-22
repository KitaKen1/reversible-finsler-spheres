module

public import Finsler.Loop.OrthogonalRelativeThomZero

/-! A genuine cochain primitive for the SAME normalized original
Thom cocycle after orthogonal escape. It lies in the REAL relative
complex, so its ambient representative is literally zero on the
actual exterior carrier. Diagonal-seam vanishing is not inferred. -/
@[expose] public section
namespace Finsler.OrthogonalThomPrimitive
open CategoryTheory SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.BorelEvaluation Finsler.CochainComparison
open Finsler.OrthogonalRelativeThomZero
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable {n : ℕ} {X : TopCat.{0}} (f g w : X ⟶ sphere n)
  (hgw : ∀ x, ⟪(g x : Ambient n), (w x : Ambient n)⟫ = 0)
  (hfw : ∀ x, ⟪(f x : Ambient n), (w x : Ambient n)⟫ = 0)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hn : 1 ≤ n)

def cocycle : RelativeCupCochain.relative (source f g (ρ := ρ)) n :=
  RelativeCupCochain.pullback (pairMap f g (ρ := ρ)) n (NormalizedDiagonalCocycle.relativeCocycle n hn hρ)

theorem cocycle_closed : RelativeCupCochain.differential (source f g (ρ := ρ)) n (cocycle f g hρ hn) = 0 :=
  CochainClass.closed_map (RelativeCup.cx (FarDiagonalCohomology.farPair n ρ))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (pairMap f g (ρ := ρ)))
    n (NormalizedDiagonalCocycle.relativeCocycle n hn hρ) (NormalizedDiagonalCocycle.relative_closed n hn hρ)

include w hgw hfw hρ1 in
theorem class_zero : CochainClass.classOf (RelativeCup.cx (source f g (ρ := ρ))) n
    (cocycle f g hρ hn) (cocycle_closed f g hρ hn) = 0 :=
  (CochainClass.classOf_map (RelativeCup.cx (FarDiagonalCohomology.farPair n ρ))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (pairMap f g (ρ := ρ)))
    n (NormalizedDiagonalCocycle.relativeCocycle n hn hρ) (NormalizedDiagonalCocycle.relative_closed n hn hρ)
    (cocycle_closed f g hρ hn)).symm.trans
      (thom_pullback_zero f g w hgw hfw hρ hρ1 hn)

def primitive : RelativeCupCochain.relative (source f g (ρ := ρ)) (n - 1) :=
  CochainClassExact.primitive (RelativeCup.cx (source f g (ρ := ρ))) n hn (cocycle f g hρ hn) 0
    (cocycle_closed f g hρ hn) (map_zero _)
    ((class_zero f g w hgw hfw hρ hρ1 hn).trans
      (CochainClass.classOf_zero (RelativeCup.cx (source f g (ρ := ρ))) n (map_zero _)).symm)

theorem primitive_d : ((RelativeCup.cx (source f g (ρ := ρ))).d (n - 1) n).hom
    (primitive f g w hgw hfw hρ hρ1 hn) = cocycle f g hρ hn := by
  have h := CochainClassExact.primitive_d (RelativeCup.cx (source f g (ρ := ρ))) n hn (cocycle f g hρ hn) 0
    (cocycle_closed f g hρ hn) (map_zero _)
    ((class_zero f g w hgw hfw hρ hρ1 hn).trans
      (CochainClass.classOf_zero (RelativeCup.cx (source f g (ρ := ρ))) n (map_zero _)).symm)
  exact h.trans (sub_zero _)

theorem primitive_far_zero :
    cochainPullback (SupportedCap.subspaceMap X (exterior f g (ρ := ρ))) (n - 1)
      (RelativeCupCochain.toAmbient (source f g (ρ := ρ)) (n - 1) (primitive f g w hgw hfw hρ hρ1 hn)) = 0 :=
  RelativeCupCochain.restriction_toAmbient (source f g (ρ := ρ)) (n - 1) (primitive f g w hgw hfw hρ hρ1 hn)

end
end Finsler.OrthogonalThomPrimitive
