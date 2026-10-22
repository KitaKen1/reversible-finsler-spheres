module

public import Finsler.Topology.SelfCutThomCocycle
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-! A genuine time-cylinder prism on the original H1 loop space. Endpoint
annihilation after supported Thom capping and comparison with the specified
shuffle rectangle are separate obligations. -/

@[expose] public section
namespace Finsler.SelfCutTimePrism

open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def cylinder (n : ℕ) : TopCat.Homotopy (atTime n 0) (atTime n 1) where
  toFun z := (⟨z.1.val, z.1.property⟩, z.2)
  continuous_toFun := continuous_fst.prodMk continuous_snd
  map_zero_left _ := rfl
  map_one_left _ := rfl

def chainHomotopy (n : ℕ) :
    _root_.Homotopy (SupportedCapNaturality.push (atTime n 0))
      (SupportedCapNaturality.push (atTime n 1)) :=
  (cylinder n).toSSet.chainComplexMap coeff

def prism (n q : ℕ) : (chains (TopCat.of (SphereLoop n))).X q ⟶
    (chains (parameters n)).X (q + 1) := (chainHomotopy n).hom q (q + 1)

theorem prism_boundary_succ (n q : ℕ) :
    (SupportedCapNaturality.push (atTime n 0)).f (q + 1) =
      (chains (TopCat.of (SphereLoop n))).d (q + 1) q ≫ prism n q +
        prism n (q + 1) ≫ (chains (parameters n)).d (q + 2) (q + 1) +
          (SupportedCapNaturality.push (atTime n 1)).f (q + 1) := by
  simpa only [prism, Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] using
    (chainHomotopy n).comm (q + 1)

theorem prism_boundary_zero (n : ℕ) :
    (SupportedCapNaturality.push (atTime n 0)).f 0 =
      prism n 0 ≫ (chains (parameters n)).d 1 0 +
        (SupportedCapNaturality.push (atTime n 1)).f 0 := by
  simpa only [prism, Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] using
    (chainHomotopy n).comm 0

end
end Finsler.SelfCutTimePrism
