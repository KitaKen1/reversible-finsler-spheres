module

public import Finsler.Loop.PrismCapFront
public import Finsler.Loop.CompactJoinCocycle

/-! Apply the actual early-prism front degeneracy to any normalized
cochain and specifically to the actual join Thom cochain. No zero
front coefficient is assumed. -/

@[expose] public section
namespace Finsler.NormalizedPrismCapFront

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.IntervalSobolev Finsler.SmallChainCarrier
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem normalize_eq (Y : TopCat.{0}) (a : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization Y) φ) :
    SingularNormalization.normalize Y a φ = φ := by
  have hq := (DoldKan.degeneraciesVanish_iff_QInfty_f_comp
    (X := SingularNormalization.linearization Y) φ).mp hφ
  have he := congrArg (fun f : (chains Y).X a ⟶ (chains Y).X a => f ≫ φ)
    (DoldKan.PInfty_f_add_QInfty_f (X := SingularNormalization.linearization Y) a)
  simp only [Preadditive.add_comp, hq, add_zero] at he
  exact he.trans (Category.id_comp φ)

theorem early_zero (p a : ℕ) (ha : a ≤ p + 1)
    (i : Fin (p + 1)) (hi : i.val < a) (Y : TopCat.{0})
    (g : (Δ[p] : SSet.{0}) ⟶ TopCat.toSSet.obj Y)
    (φ : singularCochainGroup (ZMod 2) Y a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization Y) φ) :
    (TopCat.toSSet.obj Y).ιChainComplex (g.app _ (PrismCapFront.front p a ha i)) ≫ φ = 0 := by
  rw [← normalize_eq Y a φ hφ]
  exact PrismCapFront.early_normalized_zero p a ha i hi Y g φ

theorem actual_join_early_zero {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    {n : ℕ} (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
    (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (p : ℕ) (hnp : n ≤ p + 1)
    (i : Fin (p + 1)) (hi : i.val < n)
    (g : (Δ[p] : SSet.{0}) ⟶ TopCat.toSSet.obj (TopCat.of (P × Q))) :
    (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex
      (g.app _ (PrismCapFront.front p n hnp i)) ≫ CompactJoinCocycle.cocycle α β hn hρ = 0 :=
  early_zero p n hnp i hi (TopCat.of (P × Q)) g
    (CompactJoinCocycle.cocycle α β hn hρ) (CompactJoinCocycle.cocycle_normalized α β hn hρ)

end
end Finsler.NormalizedPrismCapFront
