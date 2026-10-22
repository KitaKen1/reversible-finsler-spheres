module

public import Finsler.Loop.LocalOriginalRelativeOutputPrimitive
public import Finsler.Topology.RelativeKronecker

/-! The original complete cap is a boundary in the ACTUAL relative
cochain complex of the whole-ball chart and its original Thom exterior.
This strengthens absolute local vanishing to the specified relative
support condition. Global source/time faces are a separate condition. -/
@[expose] public section
namespace Finsler.LocalOriginalRelativeOutputRelative
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

def pair {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (ρ : ℝ) : TopPair.{0} :=
  TopPair.ofSubset (LocalNativeSupportedCap.exterior P v₀ b ρ)

variable (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
  (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1))

def cocycle : RelativeCupCochain.relative (pair P v₀ b ρ) ((m + 1) + (m + (m + 1))) :=
  Classical.choose (RelativeCupCochain.exists_lift (pair P v₀ b ρ) ((m + 1) + (m + (m + 1)))
    (LocalOriginalRelativeOutputClass.original m P v₀ b hρ hρr hr a)
    (LocalRelativeOutputCapSupport.original_exterior_zero m P v₀ b hρ hρr hr a))

theorem cocycle_toAmbient : RelativeCupCochain.toAmbient (pair P v₀ b ρ) ((m + 1) + (m + (m + 1)))
    (cocycle m P v₀ b hρ hρr hr a) = LocalOriginalRelativeOutputClass.original m P v₀ b hρ hρr hr a :=
  Classical.choose_spec (RelativeCupCochain.exists_lift (pair P v₀ b ρ) ((m + 1) + (m + (m + 1)))
    (LocalOriginalRelativeOutputClass.original m P v₀ b hρ hρr hr a)
    (LocalRelativeOutputCapSupport.original_exterior_zero m P v₀ b hρ hρr hr a))

def primitive : RelativeCupCochain.relative (pair P v₀ b ρ) ((m + 1) + (m + m)) :=
  Classical.choose (RelativeCupCochain.exists_lift (pair P v₀ b ρ) ((m + 1) + (m + m))
    (LocalOriginalRelativeOutputPrimitive.primitive m hm P v₀ b hρ hρr hr a)
    (LocalOriginalRelativeOutputPrimitive.primitive_exterior_zero m hm P v₀ b hρ hρr hr a))

theorem primitive_toAmbient : RelativeCupCochain.toAmbient (pair P v₀ b ρ) ((m + 1) + (m + m))
    (primitive m hm P v₀ b hρ hρr hr a) = LocalOriginalRelativeOutputPrimitive.primitive m hm P v₀ b hρ hρr hr a :=
  Classical.choose_spec (RelativeCupCochain.exists_lift (pair P v₀ b ρ) ((m + 1) + (m + m))
    (LocalOriginalRelativeOutputPrimitive.primitive m hm P v₀ b hρ hρr hr a)
    (LocalOriginalRelativeOutputPrimitive.primitive_exterior_zero m hm P v₀ b hρ hρr hr a))

theorem primitive_boundary : RelativeCupCochain.differential (pair P v₀ b ρ) ((m + 1) + (m + m))
    (primitive m hm P v₀ b hρ hρr hr a) = cocycle m P v₀ b hρ hρr hr a := by
  apply RelativeCupCochain.toAmbient_injective (pair P v₀ b ρ) ((m + 1) + (m + (m + 1)))
  have hd := RelativeCupCochain.toAmbient_differential (pair P v₀ b ρ) ((m + 1) + (m + m))
    (primitive m hm P v₀ b hρ hρr hr a)
  change RelativeCupCochain.toAmbient (pair P v₀ b ρ) ((m + 1) + (m + (m + 1)))
    (RelativeCupCochain.differential (pair P v₀ b ρ) ((m + 1) + (m + m))
      (primitive m hm P v₀ b hρ hρr hr a)) = _ at hd
  rw [hd, primitive_toAmbient, cocycle_toAmbient]
  exact LocalOriginalRelativeOutputPrimitive.primitive_boundary m hm P v₀ b hρ hρr hr a

theorem closed : RelativeCupCochain.differential (pair P v₀ b ρ) ((m + 1) + (m + (m + 1)))
    (cocycle m P v₀ b hρ hρr hr a) = 0 := by
  apply RelativeCupCochain.toAmbient_injective (pair P v₀ b ρ) (((m + 1) + (m + (m + 1))) + 1)
  rw [RelativeCupCochain.toAmbient_differential, cocycle_toAmbient, map_zero]
  exact LocalOriginalRelativeOutputClass.closed m P v₀ b hρ hρr hr a

def originalClass : RelativeCup.cohomology (pair P v₀ b ρ) ((m + 1) + (m + (m + 1))) :=
  CochainClass.classOf (RelativeCup.cx (pair P v₀ b ρ)) ((m + 1) + (m + (m + 1)))
    (cocycle m P v₀ b hρ hρr hr a) (closed m P v₀ b hρ hρr hr a)

include hm in
theorem originalClass_zero : originalClass m P v₀ b hρ hρr hr a = 0 := by
  have he := primitive_boundary m hm P v₀ b hρ hρr hr a
  have hc := CochainClass.closed_boundary (RelativeCup.cx (pair P v₀ b ρ))
    ((m + 1) + (m + m)) ((m + 1) + (m + (m + 1))) (primitive m hm P v₀ b hρ hρr hr a)
  exact (CochainClass.classOf_congr _ _ he.symm _ hc).trans
    (CochainClass.classOf_boundary _ ((m + 1) + (m + m)) ((m + 1) + (m + (m + 1))) _ hc)

include hm in
theorem pairing_zero (z : ((pair P v₀ b ρ).singularHomology coeff ((m + 1) + (m + (m + 1))) : ModuleCat.{0} (ZMod 2))) :
    RelativeKronecker.comparison (pair P v₀ b ρ) ((m + 1) + (m + (m + 1)))
      (originalClass m P v₀ b hρ hρr hr a) z = 0 := by
  rw [originalClass_zero m hm P v₀ b hρ hρr hr a, map_zero]
  rfl

end
end Finsler.LocalOriginalRelativeOutputRelative
