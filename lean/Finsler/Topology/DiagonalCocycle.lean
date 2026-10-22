module

public import Finsler.Topology.DiagonalUniqueness
public import Finsler.Topology.RelativeCup

/-! A genuine closed relative diagonal cochain and its supported ambient cochain,
in the project's pre-existing F₂ model. The geometric cut and interchange
operations are not constructed by choosing this cocycle. -/

@[expose] public section

namespace Finsler.DiagonalCocycle

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison
open Finsler.DiagonalCohomology Finsler.DiagonalUniqueness

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def relativeCocycle (n : ℕ) (hn : 1 ≤ n) : RelativeCupCochain.relative (diagonalPair n) n :=
  CochainClass.representative (RelativeCup.cx (diagonalPair n)) n (relativeClass n hn)

theorem relative_closed (n : ℕ) (hn : 1 ≤ n) :
    RelativeCupCochain.differential (diagonalPair n) n (relativeCocycle n hn) = 0 :=
  CochainClass.representative_closed (RelativeCup.cx (diagonalPair n)) n (relativeClass n hn)

theorem relative_cocycle_class (n : ℕ) (hn : 1 ≤ n) :
    CochainClass.classOf (RelativeCup.cx (diagonalPair n)) n (relativeCocycle n hn)
      (relative_closed n hn) = relativeClass n hn :=
  CochainClass.classOf_representative (RelativeCup.cx (diagonalPair n)) n (relativeClass n hn)

def ambientCocycle (n : ℕ) (hn : 1 ≤ n) : singularCochainGroup (ZMod 2) (product n) n :=
  RelativeCupCochain.toAmbient (diagonalPair n) n (relativeCocycle n hn)

theorem ambient_closed (n : ℕ) (hn : 1 ≤ n) :
    cochainCoboundary (ZMod 2) (product n) n (ambientCocycle n hn) = 0 :=
  RelativeCup.toAmbient_closed (diagonalPair n) n (relativeCocycle n hn) (relative_closed n hn)

theorem supported_on_diagonal (n : ℕ) (hn : 1 ≤ n) :
    cochainPullback (diagonalPair n).map n (ambientCocycle n hn) = 0 :=
  RelativeCupCochain.restriction_toAmbient (diagonalPair n) n (relativeCocycle n hn)

theorem ambient_cocycle_class (n : ℕ) (hn : 1 ≤ n) :
    CochainClass.classOf (cochainCxZMod2 (product n)) n (ambientCocycle n hn)
      (ambient_closed n hn) = ambientClass n hn := by
  calc
    _ = (relativeToPool (diagonalPair n) n).hom
        (CochainClass.classOf (RelativeCup.cx (diagonalPair n)) n (relativeCocycle n hn)
          (relative_closed n hn)) :=
      (RelativeCup.relativeToPool_classOf (diagonalPair n) n (relativeCocycle n hn)
        (relative_closed n hn)).symm
    _ = (relativeToPool (diagonalPair n) n).hom (relativeClass n hn) :=
      congrArg _ (relative_cocycle_class n hn)
    _ = ambientClass n hn := relativeClass_pool_image n hn

theorem ambient_cocycle_ne_zero (n : ℕ) (hn : 1 ≤ n) : ambientCocycle n hn ≠ 0 := by
  intro h
  have he := ambient_cocycle_class n hn
  have hz : CochainClass.classOf (cochainCxZMod2 (product n)) n (ambientCocycle n hn)
      (ambient_closed n hn) = 0 :=
    (CochainClass.classOf_congr (cochainCxZMod2 (product n)) n h (ambient_closed n hn)
      (by simp)).trans (CochainClass.classOf_zero (cochainCxZMod2 (product n)) n (by simp))
  exact ambientClass_ne_zero n hn (he.symm.trans hz)


end
end Finsler.DiagonalCocycle
