module

public import Finsler.Loop.NativeSourceThomProjection
public import Finsler.Loop.IntervalCupLeftProjection
public import Finsler.Loop.SelfCutPrismCoboundary
public import Finsler.Loop.NativeRawOriginalScalarReduction
public import Finsler.Loop.NativeInnerRetainedComparison
public import Finsler.Loop.NativeBVRelativeCochain

/-! The actual source-cup projection formula THROUGH the original Thom
and full time operation. A normalized closed source factor and a closed
near cochain give an explicit constant-relative boundary. -/
@[expose] public section
namespace Finsler.NativeSourceTimeProjection
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem integrate_source_cup (m a b N : ℕ) (h : a + b = N)
    (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) a)
    (hE : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (Loops (m + 1))) E)
    (K : singularCochainGroup (ZMod 2) (parameters (m + 1)) (b + 1)) :
    SelfCutTimePrism.prism (m + 1) N ≫ CupOne.cup _ a (b + 1) (N + 1) (by omega)
      (NativeSourceThomProjection.alpha m a E) K =
    CupOne.cup _ a b N h E (SelfCutTimePrism.prism (m + 1) b ≫ K) := by
  simp only [SelfCutTimePrism.prism, SelfCutTimePrism.chainHomotopy,
    ← TimeShuffleComparison.rectangle_eq_prism, TimeShuffleComparison.rectangle, Category.assoc]
  change TimeTriangleSplit.interval (Loops (m + 1)) N ≫
    cochainPullback (SelfCutTimePrism.cylinder (m + 1)).h (N + 1)
      (CupOne.cup _ a (b + 1) (N + 1) _ (NativeSourceThomProjection.alpha m a E) K) = _
  rw [CupCapOrder.naturality, NativeSourceThomProjection.alpha, ← pullback_comp]
  change TimeTriangleSplit.interval (Loops (m + 1)) N ≫
    CupOne.cup _ a (b + 1) (N + 1) _
      (cochainPullback (CartesianMonoidalCategory.fst (Loops (m + 1)) TopCat.I) a E)
      (cochainPullback (SelfCutTimePrism.cylinder (m + 1)).h (b + 1) K) = _
  exact IntervalCupLeftProjection.at_degree _ a b N h E hE _

theorem integrate_original (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (q N : ℕ) (h : N = m + q)
    (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q) :
    SelfCutTimePrism.prism (m + 1) N ≫
      CochainDegreeTransport.pre _ (show N + 1 = (m + 1) + q by omega)
        (NativeBVThomBoundary.parameter m hρ hρr q K) =
    CochainDegreeTransport.pre _ h (NativeBVThomBoundary.source m hρ hρr q K) := by
  subst N
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]
  rfl

variable (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (p q : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) (p + 1))
  (B : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)

abbrev lowDegree := (p + m) + q

def parameterPrimitive : singularCochainGroup (ZMod 2) (parameters (m + 1)) (lowDegree m p q + 1) :=
  CochainDegreeTransport.pre _ (show lowDegree m p q + 1 = ((p + 1) + m) + q by dsimp [lowDegree]; omega)
    (NativeSourceThomProjection.primitive m hρ hρr (p + 1) q E B)

def parameterOutside : singularCochainGroup (ZMod 2) (parameters (m + 1)) (lowDegree m p q + 2) :=
  CupOne.cup _ (p + 1) ((m + 1) + q) (lowDegree m p q + 2) (by dsimp [lowDegree]; omega)
    (NativeSourceThomProjection.alpha m (p + 1) E) (NativeBVThomBoundary.parameter m hρ hρr q B)

def parameterInside : singularCochainGroup (ZMod 2) (parameters (m + 1)) (lowDegree m p q + 2) :=
  CochainDegreeTransport.pre _ (show lowDegree m p q + 2 = (m + 1) + ((p + 1) + q) by dsimp [lowDegree]; omega)
    (NativeBVThomBoundary.parameter m hρ hρr ((p + 1) + q) (NativeSourceThomProjection.near m (p + 1) q E B))

private theorem pre_cup (X : TopCat.{0}) (a b i j : ℕ) (h : i = j) (hj : a + b = j)
    (A : singularCochainGroup (ZMod 2) X a) (B : singularCochainGroup (ZMod 2) X b) :
    CochainDegreeTransport.pre X h (CupOne.cup X a b j hj A B) =
      CupOne.cup X a b i (by omega) A B := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

private theorem pre_pre (X : TopCat.{0}) {i j k : ℕ} (h : i = j) (h' : j = k)
    (K : singularCochainGroup (ZMod 2) X k) :
    CochainDegreeTransport.pre X h (CochainDegreeTransport.pre X h' K) =
      CochainDegreeTransport.pre X (h.trans h') K := by
  subst k j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

private theorem boundary_pre {X : TopCat.{0}} {i j a b : ℕ} (hi : i = a) (hj : j = b)
    (K : singularCochainGroup (ZMod 2) X a) (T : singularCochainGroup (ZMod 2) X b)
    (h : (chains X).d b a ≫ K = T) :
    (chains X).d j i ≫ CochainDegreeTransport.pre X hi K = CochainDegreeTransport.pre X hj T := by
  subst a b
  simpa only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using h

theorem parameter_boundary (hE : cochainCoboundary (ZMod 2) _ (p + 1) E = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0) :
    cochainCoboundary (ZMod 2) _ (lowDegree m p q + 1) (parameterPrimitive m hρ hρr p q E B) =
      parameterOutside m hρ hρr p q E B - parameterInside m hρ hρr p q E B := by
  unfold parameterPrimitive
  rw [NativeRawOriginalScalarReduction.pre_boundary, NativeSourceThomProjection.boundary m hρ hρr (p + 1) q E B hE hB,
    NativeRawOriginalScalarReduction.pre_sub]
  unfold NativeSourceThomProjection.outside NativeSourceThomProjection.inside
  rw [pre_cup, pre_pre]
  rfl

theorem parameter_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (atTime (m + 1) t) (lowDegree m p q + 1) (parameterPrimitive m hρ hρr p q E B) = 0 := by
  unfold parameterPrimitive
  rw [← NormalizedCutScalarPullback.pre_pullback, NativeSourceThomProjection.primitive_endpoint m hρ hρr (p + 1) q E B t ht]
  exact comp_zero

def primitive := SelfCutPrismCoboundary.primitive (m + 1) (lowDegree m p q) (parameterPrimitive m hρ hρr p q E B)

def outside : singularCochainGroup (ZMod 2) (Loops (m + 1)) (lowDegree m p q + 1) :=
  CupOne.cup _ (p + 1) (m + q) (lowDegree m p q + 1) (by dsimp [lowDegree]; omega)
    E (NativeBVThomBoundary.source m hρ hρr q B)

def inside : singularCochainGroup (ZMod 2) (Loops (m + 1)) (lowDegree m p q + 1) :=
  CochainDegreeTransport.pre _ (show lowDegree m p q + 1 = m + ((p + 1) + q) by dsimp [lowDegree]; omega)
    (NativeBVThomBoundary.source m hρ hρr ((p + 1) + q) (NativeSourceThomProjection.near m (p + 1) q E B))

theorem integrate_outside (hE : DoldKan.DegeneraciesVanish
    (X := SingularNormalization.linearization (Loops (m + 1))) E) :
    SelfCutTimePrism.prism (m + 1) (lowDegree m p q + 1) ≫ parameterOutside m hρ hρr p q E B =
      outside m hρ hρr p q E B := by
  unfold parameterOutside outside
  rw [← NativeInnerRetainedComparison.cup_right_pre _ (show m + q + 1 = (m + 1) + q by omega)
    (show (p + 1) + (m + q + 1) = lowDegree m p q + 2 by dsimp [lowDegree]; omega)]
  rw [integrate_source_cup _ _ _ _ (by dsimp [lowDegree]; omega) _ hE, integrate_original _ _ _ _ _ rfl]
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem integrate_inside : SelfCutTimePrism.prism (m + 1) (lowDegree m p q + 1) ≫
    parameterInside m hρ hρr p q E B = inside m hρ hρr p q E B :=
  integrate_original _ _ _ _ _ _ _

theorem boundary (hEn : DoldKan.DegeneraciesVanish
    (X := SingularNormalization.linearization (Loops (m + 1))) E)
    (hE : cochainCoboundary (ZMod 2) _ (p + 1) E = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0) :
    cochainCoboundary (ZMod 2) _ (lowDegree m p q) (primitive m hρ hρr p q E B) =
      outside m hρ hρr p q E B - inside m hρ hρr p q E B := by
  have h := SelfCutPrismCoboundary.comparison (m + 1) (lowDegree m p q)
    (parameterPrimitive m hρ hρr p q E B) (parameterOutside m hρ hρr p q E B) (parameterInside m hρ hρr p q E B)
    (parameter_boundary m hρ hρr p q E B hE hB)
    (parameter_endpoint m hρ hρr p q E B 0 (Or.inl rfl))
    (parameter_endpoint m hρ hρr p q E B 1 (Or.inr rfl))
  rw [integrate_outside m hρ hρr p q E B hEn, integrate_inside] at h
  exact h

theorem primitive_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (lowDegree m p q) (primitive m hρ hρr p q E B) = 0 := by
  have hz : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (lowDegree m p q)
      (SelfCutTimePrism.prism (m + 1) (lowDegree m p q) ≫ parameterPrimitive m hρ hρr p q E B) = 0 := by
    apply DoublePrismCochainBoundary.prism_pre_zero (SelfCutTimePrism.cylinder (m + 1))
    unfold parameterPrimitive
    rw [← NormalizedCutScalarPullback.pre_pullback]
    have hh := NativeSourceThomProjection.primitive_diagonal m hρ hρr (p + 1) q E B
      ((SelfCutTimePrism.cylinder (m + 1)).comp (TopCat.Homotopy.refl (GlobalTimeCupConstantsVanish.inclusion (m + 1)))).h
      (fun z => GlobalTimeCupConstantsVanish.cylinder_diagonal (m + 1) (z.2.down, z.1))
    rw [hh]
    exact comp_zero
  change (push (GlobalTimeCupConstantsVanish.inclusion (m + 1))).f _ ≫
    (-(SelfCutTimePrism.prism (m + 1) _ ≫ parameterPrimitive m hρ hρr p q E B)) = 0
  rw [Preadditive.comp_neg]
  exact (congrArg Neg.neg hz).trans neg_zero

theorem relative_cycle_values (hEn : DoldKan.DegeneraciesVanish
    (X := SingularNormalization.linearization (Loops (m + 1))) E)
    (hE : cochainCoboundary (ZMod 2) _ (p + 1) E = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0)
    {M : ModuleCat.{0} (ZMod 2)} (u : M ⟶ (chains (Loops (m + 1))).X (lowDegree m p q + 1))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f (lowDegree m p q + 1)) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d (lowDegree m p q + 1) (lowDegree m p q) = 0) :
    u ≫ outside m hρ hρr p q E B = u ≫ inside m hρ hρr p q E B := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← boundary m hρ hρr p q E B hEn hE hB]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1)))
    _ _ u hu _ (primitive_constants_zero m hρ hρr p q E B)

theorem exists_boundary_at_degree (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (a q d : ℕ) (ha : 0 < a) (hd : d = a + (m + q))
    (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) a)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)
    (hEn : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (Loops (m + 1))) E)
    (hE : cochainCoboundary (ZMod 2) _ a E = 0) (hB : cochainCoboundary (ZMod 2) _ q B = 0) :
    ∃ K : singularCochainGroup (ZMod 2) (Loops (m + 1)) (d - 1),
      cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (d - 1) K = 0 ∧
      (chains (Loops (m + 1))).d d (d - 1) ≫ K =
        CupOne.cup _ a (m + q) d hd.symm E (NativeBVThomBoundary.source m hρ hρr q B) -
        CochainDegreeTransport.pre _ (show d = m + (a + q) by omega)
          (NativeBVThomBoundary.source m hρ hρr (a + q) (NativeSourceThomProjection.near m a q E B)) := by
  cases a with
  | zero => omega
  | succ p =>
    obtain rfl : d = lowDegree m p q + 1 := by dsimp [lowDegree]; omega
    refine ⟨CochainDegreeTransport.pre _ (show lowDegree m p q + 1 - 1 = lowDegree m p q by omega)
      (primitive m hρ hρr p q E B), ?_, ?_⟩
    · rw [← NormalizedCutScalarPullback.pre_pullback, primitive_constants_zero m hρ hρr p q E B]
      exact comp_zero
    · exact boundary_pre (show lowDegree m p q + 1 - 1 = lowDegree m p q by omega) rfl _ _
        (boundary m hρ hρr p q E B hEn hE hB)

end
end Finsler.NativeSourceTimeProjection
