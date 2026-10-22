module

public import Finsler.Loop.NativeOrderedDoubleCutCochain
public import Finsler.Loop.SupportedCutCochainCarrierZero
public import Finsler.Loop.DegreeLoweringCochainPullback

/-! A GLOBAL common ordered two-cut cochain from TWO ORIGINAL supported
Thom-cap operations and the three actual output tests. Closure uses the
actual supported chain maps; diagonalZERO uses whole-parent carrier
preservation TWICE. No closed zero-extension assertion is made. Equality
with the original sequential-cut operations is still separate. -/
@[expose] public section
namespace Finsler.NativeOrderedDoubleCutSupported
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

section Stage
variable {n : ℕ} {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters n)

def far (ρ : ℝ) : Set X := f ⁻¹' SupportedSelfCut.exterior n ρ

def near (r : ℝ) : Set X := f ⁻¹' SupportedSelfCut.neighborhood n r

theorem far_open (ρ : ℝ) : IsOpen (far f ρ) :=
  (SupportedSelfCut.exterior_open n ρ).preimage f.hom.continuous

theorem near_open (r : ℝ) : IsOpen (near f r) :=
  (SupportedSelfCut.neighborhood_open n r).preimage f.hom.continuous

theorem cover {ρ r : ℝ} (hρr : ρ < r) : far f ρ ∪ near f r = Set.univ := by
  rw [far, near, ← Set.preimage_union, SupportedSelfCut.cover n hρr, Set.preimage_univ]

variable (hn : 1 ≤ n) {ρ r : ℝ} (hρ : 0 < ρ)

def thom : singularCochainGroup (ZMod 2) X n :=
  cochainPullback f n (NormalizedSelfCut.cocycle n hn hρ)

theorem thom_closed : cochainCoboundary (ZMod 2) X n (thom f hn hρ) = 0 :=
  pullback_closed f n _ (NormalizedSelfCut.cocycle_closed n hn hρ)

theorem thom_supported : cochainPullback (SupportedCap.subspaceMap X (far f ρ)) n
    (thom f hn hρ) = 0 :=
  pullback_support f (far f ρ) (SupportedSelfCut.exterior n ρ) (fun _ h => h) n _
    (NormalizedSelfCut.cocycle_supported n hn hρ)

def operation (hρr : ρ < r) := SupportedCapHomology.operation X (far f ρ) (near f r)
  (far_open f ρ) (near_open f r) (cover f hρr) n
  (thom f hn hρ) (thom_supported f hn hρ) (thom_closed f hn hρ)
end Stage

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
abbrev source := NativeOrderedDoubleCutGeometry.source (m + 1)
abbrev radius := NativeClosingArcPowerVanishing.radius m hm F

def thomRadius : ℝ := radius m hm F / 2

theorem thomRadius_pos : 0 < thomRadius m hm F :=
  div_pos (NativeClosingArcPowerVanishing.radius_pos m hm F) (by norm_num)

theorem thomRadius_lt : thomRadius m hm F < radius m hm F := by
  have h := NativeClosingArcPowerVanishing.radius_pos m hm F
  unfold thomRadius
  linarith

abbrev firstSpace := TopCat.of (near (NativeOrderedDoubleCutGeometry.firstParameter (m + 1)) (radius m hm F))

def firstOperation := operation (NativeOrderedDoubleCutGeometry.firstParameter (m + 1))
  (by omega) (thomRadius_pos m hm F) (thomRadius_lt m hm F)

def secondParameter : firstSpace m hm F ⟶ SelfCutThomCocycle.parameters (m + 1) :=
  SupportedCap.subspaceMap (source m)
    (near (NativeOrderedDoubleCutGeometry.firstParameter (m + 1)) (radius m hm F)) ≫
      NativeOrderedDoubleCutGeometry.lastParameter (m + 1)

def secondOperation := operation (secondParameter m hm F) (by omega)
  (thomRadius_pos m hm F) (thomRadius_lt m hm F)

def jointMap : TopCat.of (near (secondParameter m hm F) (radius m hm F)) ⟶
    NativeOrderedDoubleCutCochain.domain m hm F := TopCat.ofHom
  ⟨fun z => ⟨z.val.val, z.val.property, z.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def diagonal : Set (source m) := {z | z.2.val.1.down = z.2.val.2.down}

def firstDiagonal : Set (firstSpace m hm F) :=
  (SupportedCap.subspaceMap (source m)
    (near (NativeOrderedDoubleCutGeometry.firstParameter (m + 1)) (radius m hm F))) ⁻¹' diagonal m

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

abbrev testDegree := NativeGHPowers.degree m a + (NativeGHPowers.degree m b + k)

def secondCochain : singularCochainGroup (ZMod 2) (firstSpace m hm F)
    ((m + 1) + testDegree m a b k) :=
  (secondOperation m hm F).component (testDegree m a b k) ≫
    cochainPullback (jointMap m hm F) _ (NativeOrderedDoubleCutCochain.tests m hm F a b k E)

theorem second_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (firstSpace m hm F) _ (secondCochain m hm F a b k E) = 0 :=
  DegreeLoweringCochainPullback.closed (secondOperation m hm F) _ _
    (pullback_closed _ _ _ (NativeOrderedDoubleCutCochain.tests_closed m hm F a b k E hE))

theorem second_diagonal_zero :
    cochainPullback (SupportedCap.subspaceMap (firstSpace m hm F) (firstDiagonal m hm F)) _
      (secondCochain m hm F a b k E) = 0 := by
  let C := firstDiagonal m hm F
  let B := near (secondParameter m hm F) (radius m hm F)
  let f := restriction (SupportedCap.subspaceMap (firstSpace m hm F) C)
    ((SupportedCap.subspaceMap (firstSpace m hm F) C) ⁻¹' B) B (fun _ h => h)
  let d : TopCat.of ((SupportedCap.subspaceMap (firstSpace m hm F) C) ⁻¹' B) ⟶
      NativeOrderedDoubleCutDiagonal.diagonalDomain (m + 1) (radius m hm F) := TopCat.ofHom
    ⟨fun z => ⟨jointMap m hm F (f z), z.val.property⟩,
      ((jointMap m hm F).hom.continuous.comp f.hom.continuous).subtype_mk _⟩
  have he : f ≫ jointMap m hm F = d ≫
      NativeOrderedDoubleCutDiagonal.inclusion (m + 1) (radius m hm F) := rfl
  have hz : cochainPullback f (testDegree m a b k)
      (cochainPullback (jointMap m hm F) _ (NativeOrderedDoubleCutCochain.tests m hm F a b k E)) = 0 := by
    rw [← pullback_comp, he, pullback_comp, NativeOrderedDoubleCutCochain.tests_diagonal_zero]
    change (push d).f _ ≫ 0 = 0
    exact comp_zero
  exact SupportedCutCochainCarrierZero.subspace_cochain_zero (firstSpace m hm F)
    (far (secondParameter m hm F) (thomRadius m hm F)) B C
    (far_open _ _) (near_open _ _) (cover _ (thomRadius_lt m hm F)) (m + 1) (testDegree m a b k)
    (thom (secondParameter m hm F) (by omega) (thomRadius_pos m hm F))
    (thom_supported _ _ _) _ hz

abbrev totalDegree := (m + 1) + ((m + 1) + testDegree m a b k)

def cochain : singularCochainGroup (ZMod 2) (source m) (totalDegree m a b k) :=
  (firstOperation m hm F).component ((m + 1) + testDegree m a b k) ≫ secondCochain m hm F a b k E

theorem cochain_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source m) _ (cochain m hm F a b k E) = 0 :=
  DegreeLoweringCochainPullback.closed (firstOperation m hm F) _ _ (second_closed m hm F a b k E hE)

theorem cochain_diagonal_zero :
    cochainPullback (SupportedCap.subspaceMap (source m) (diagonal m)) _ (cochain m hm F a b k E) = 0 := by
  let C := diagonal m
  let B := near (NativeOrderedDoubleCutGeometry.firstParameter (m + 1)) (radius m hm F)
  let f := restriction (SupportedCap.subspaceMap (source m) C)
    ((SupportedCap.subspaceMap (source m) C) ⁻¹' B) B (fun _ h => h)
  let d : TopCat.of ((SupportedCap.subspaceMap (source m) C) ⁻¹' B) ⟶
      TopCat.of (firstDiagonal m hm F) := TopCat.ofHom
    ⟨fun z => ⟨f z, z.val.property⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = d ≫ SupportedCap.subspaceMap (firstSpace m hm F) (firstDiagonal m hm F) := rfl
  have hz : cochainPullback f ((m + 1) + testDegree m a b k) (secondCochain m hm F a b k E) = 0 := by
    rw [he, pullback_comp, second_diagonal_zero]
    change (push d).f _ ≫ 0 = 0
    exact comp_zero
  exact SupportedCutCochainCarrierZero.subspace_cochain_zero (source m)
    (far (NativeOrderedDoubleCutGeometry.firstParameter (m + 1)) (thomRadius m hm F)) B C
    (far_open _ _) (near_open _ _) (cover _ (thomRadius_lt m hm F)) (m + 1) ((m + 1) + testDegree m a b k)
    (thom (NativeOrderedDoubleCutGeometry.firstParameter (m + 1)) (by omega) (thomRadius_pos m hm F))
    (thom_supported _ _ _) _ hz

def normalized := SingularNormalization.normalize (source m) _ (cochain m hm F a b k E)

theorem normalized_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source m) _ (normalized m hm F a b k E) = 0 :=
  SingularNormalization.normalize_closed _ _ _ (cochain_closed m hm F a b k E hE)

theorem normalized_degeneracies : DoldKan.DegeneraciesVanish
    (X := SingularNormalization.linearization (source m)) (normalized m hm F a b k E) :=
  SingularNormalization.normalize_degeneracies _ _ _

theorem normalized_diagonal_zero :
    cochainPullback (SupportedCap.subspaceMap (source m) (diagonal m)) _ (normalized m hm F a b k E) = 0 :=
  SingularNormalization.normalize_supported _ _ _ (cochain_diagonal_zero m hm F a b k E)

end
end Finsler.NativeOrderedDoubleCutSupported
