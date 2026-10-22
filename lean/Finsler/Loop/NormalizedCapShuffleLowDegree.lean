module

public import Finsler.Loop.NormalizedCapShuffleTensor

/-! A normalized first-factor cochain kills every external cross whose
first degree is too small. This supplies the homogeneous degrees absent
from the usual cap/shuffle formula with first degree a+p. -/

@[expose] public section
namespace Finsler.NormalizedCapShuffleLowDegree

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.MappedShuffleWordCap Finsler.ShuffleWords
open scoped Simplicial DoldKan BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem horizontal_replicate (a : ℕ) : horizontal (List.replicate a false) = a := by
  induction a with
  | zero => rfl
  | succ a ih => simpa only [List.replicate_succ, horizontal] using congrArg Nat.succ ih

theorem word_prefix_ne (p j a : ℕ) (hp : p < a) (w : List Bool) (hw : w ∈ words p j) :
    w.take a ≠ List.replicate a false := by
  intro he
  have hh := horizontal_take_le w a
  rw [he, horizontal_replicate, (mem_words p j w).mp hw |>.1] at hh
  omega

theorem word_cap_zero (X Y : TopCat.{0}) (a p j q : ℕ) (hN : a + q = p + j)
    (hp : p < a) (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌)
    (w : List Bool) (hw : w ∈ words p j)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y p j (p + j) σ τ w) ≫
      absoluteChain (X ⊗ Y) a q (p + j) hN
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) = 0 := by
  rw [SmallCapCarrier.cap_simplex]
  have hz : SmallCapCarrier.weight (X ⊗ Y) a q (p + j) hN
      (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ)
        (simplex X Y p j (p + j) σ τ w) = 0 := by
    dsimp only [SmallCapCarrier.weight]
    rw [bad_coefficient_zero X Y p j (p + j) a (by omega) σ τ w
      (word_prefix_ne p j a hp w hw) φ hφ,
      MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]
  rw [hz, zero_comp]

theorem right_cap_zero (X Y : TopCat.{0}) (a p j q : ℕ) (hN : a + q = p + j) (hp : p < a)
    (τ : TopCat.toSSet.obj Y _⦋j⦌) (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    SingularChainCross.right X Y p j τ ≫
      absoluteChain (X ⊗ Y) a q (p + j) hN
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) = 0 := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  rw [← Category.assoc, NormalizedCapShuffle.right_simplex_sum, Preadditive.sum_comp]
  simp only [comp_zero]
  apply Finset.sum_eq_zero
  intro w hw
  exact word_cap_zero X Y a p j q hN hp σ τ w hw φ hφ

theorem component_cap_zero (X Y : TopCat.{0}) (a p j q : ℕ) (hN : a + q = p + j) (hp : p < a)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    SingularChainCross.component X Y p j ≫
      absoluteChain (X ⊗ Y) a q (p + j) hN
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) = 0 := by
  apply SSet.tensorChainComplexX_hom_ext
  intro σ τ
  apply (cancel_epi (ρ_ coeff).inv).mp
  have hp' := NormalizedCapShuffleTensor.pair_right X Y p j ((TopCat.toSSet.obj X).ιChainComplex σ) τ
  have hc := congrArg (fun f => f ≫ absoluteChain (X ⊗ Y) a q (p + j) hN
    (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ)) hp'.symm
  simpa only [Category.assoc, right_cap_zero X Y a p j q hN hp τ φ hφ, comp_zero] using hc

end
end Finsler.NormalizedCapShuffleLowDegree
