module

public import Finsler.Topology.TransportK
public import Finsler.Topology.EventRanks
public import Finsler.Topology.RegularInterval

/-! From tight to wide cuts. Let 0 < a ≤ a' ≤ b' ≤ b with no critical level in [2a, 2a'] and in
[2b', 2b]. Restriction from the crossing pair (t_{2b}, t_{2a}) to (t_{2b'}, t_{2a}), and from the
tight crossing pair (t_{2b'}, t_{2a'}) to (t_{2b'}, t_{2a}), are isomorphisms on actual relative
cohomology (the regular strips deform), hence on K-Borel cohomology. On the fixed crossing pairs
they are isomorphisms too: doubling identifies them with the restrictions of the crossing pairs at
half the cuts, which are isomorphisms because the half strips [a, a'] and [b', b] contain no
critical level either. All restrictions commute with the restrictions to the fixed parts. So the
windowed localization of the tight crossing and of the wide crossing are equivalent
(`TransportK.loc_iff` twice). -/

@[expose] public section

namespace Finsler.StripK

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelFixed Finsler.FixedLadder Finsler.CutPotential Finsler.AvoidPoint
open Finsler.BorelIterate Finsler.BorelCrossingK Finsler.GradedLadder Finsler.BorelExact
open Finsler.CriticalLevels Finsler.BorelK Finsler.TotalExact Finsler.BorelCoverK
open Finsler.LocalCoverK Finsler.TrivialK Finsler.FixedGlobal Finsler.BorelDeformation
open Finsler.BorelComparison Finsler.BorelLocalK Finsler.BorelLens Finsler.EventRanks
open Finsler.RegularInterval Finsler.TransportK Finsler.OrbitAssembly Finsler.RelativeCohomology
open Finsler.CrossLocalize

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem nativePull_id (P : TopPair.{0}) (k : ℕ) (x : native P k) : nativePull (𝟙 P) k x = x := by
  have h := TopPair.singularCohomologyMap_id (R := coeff) (k := ZMod 2) (M := coeff) P k
  exact congrArg (fun φ => φ.hom x) h

/-- A map of pairs with a two-sided inverse is bijective on actual relative cohomology. -/
theorem nativePull_bijective_of_inverse {P Q : TopPair.{0}} (f : P ⟶ Q) (g : Q ⟶ P)
    (hfg : f ≫ g = 𝟙 P) (hgf : g ≫ f = 𝟙 Q) (k : ℕ) : Function.Bijective (nativePull f k) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨nativePull g k y, ?_⟩⟩
  · have hx : nativePull g k (nativePull f k x) = x := by
      rw [← nativePull_comp, hgf, nativePull_id]
    have hy : nativePull g k (nativePull f k y) = y := by
      rw [← nativePull_comp, hgf, nativePull_id]
    rw [← hx, ← hy, hxy]
  · rw [← nativePull_comp, hfg, nativePull_id]

variable {n : ℕ} (F : ReversibleMetric n)

theorem dblCross_bijective {a b : ℝ} (hab : a ≤ b) (hab2 : 2 * a ≤ 2 * b) (k : ℕ) :
    Function.Bijective (nativePull (dblCross F hab hab2) k) :=
  nativePull_bijective_of_inverse _ _ (dbl_root_cross F hab hab2) (root_dbl_cross F hab hab2) k

/-- Fixed pairs inherit isomorphisms from the pairs at half the cuts through doubling. -/
theorem fix_nativePull_bijective {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b') (hab2 : 2 * a ≤ 2 * b)
    (hab2' : 2 * a' ≤ 2 * b') (haa : a ≤ a') (hbb : b ≤ b')
    (h : ∀ k, Function.Bijective (nativePull (inclPair (lev_mono F hab) (lev_mono F hab')
      (lev_mono F haa) (lev_mono F hbb)) k)) (k : ℕ) :
    Function.Bijective (nativePull (inclPair (fixLev_mono F hab2) (fixLev_mono F hab2')
      (fixLev_mono F (by linarith : 2 * a ≤ 2 * a')) (fixLev_mono F (by linarith : 2 * b ≤ 2 * b')))
      k) := by
  have hsq : dblCross F hab hab2 ≫ inclPair (fixLev_mono F hab2) (fixLev_mono F hab2')
      (fixLev_mono F (by linarith : 2 * a ≤ 2 * a')) (fixLev_mono F (by linarith : 2 * b ≤ 2 * b')) =
      inclPair (lev_mono F hab) (lev_mono F hab') (lev_mono F haa) (lev_mono F hbb) ≫
        dblCross F hab' hab2' := by
    ext : 2 <;> rfl
  have e : ⇑(nativePull (inclPair (fixLev_mono F hab2) (fixLev_mono F hab2')
      (fixLev_mono F (by linarith : 2 * a ≤ 2 * a')) (fixLev_mono F (by linarith : 2 * b ≤ 2 * b')))
      k) = ⇑(LinearEquiv.ofBijective _ (dblCross_bijective F hab hab2 k)).symm ∘
        ⇑(nativePull (inclPair (lev_mono F hab) (lev_mono F hab') (lev_mono F haa)
          (lev_mono F hbb)) k) ∘ ⇑(nativePull (dblCross F hab' hab2' ) k) := by
    funext x
    apply (LinearEquiv.ofBijective _ (dblCross_bijective F hab hab2 k)).injective
    rw [Function.comp_apply, Function.comp_apply, LinearEquiv.apply_symm_apply]
    change nativePull (dblCross F hab hab2) k (nativePull (inclPair _ _ _ _) k x) = _
    rw [← nativePull_comp, hsq, nativePull_comp]
  rw [e]
  exact (LinearEquiv.ofBijective _ (dblCross_bijective F hab hab2 k)).symm.bijective.comp
    ((h k).comp (dblCross_bijective F hab' hab2' k))

/-- Restriction between crossing pairs of loops, with its fixed part. -/
abbrev resK {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b') (haa : a ≤ a') (hbb : b ≤ b') :
    CommHom (crossS F hab') (crossS F hab) :=
  kHom (lev_mono F hab) (kInv_lev F a) (kInv_lev F b) (lev_mono F hab') (kInv_lev F a')
    (kInv_lev F b') (lev_mono F haa) (lev_mono F hbb)

abbrev resKh {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b') (haa : a ≤ a') (hbb : b ≤ b') :
    CommHom (fixS F hab') (fixS F hab) :=
  kHom (fixLev_mono F hab) (kInv_fixLev F a) (kInv_fixLev F b) (fixLev_mono F hab')
    (kInv_fixLev F a') (kInv_fixLev F b') (fixLev_mono F haa) (fixLev_mono F hbb)

theorem resK_comm {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b') (haa : a ≤ a') (hbb : b ≤ b')
    (i : ℕ) (x : (cochains (pairOf (lev_mono F hab'))).X i) :
    (crossHom F hab).φ.f i ((resK F hab hab' haa hbb).φ.f i x) =
      (resKh F hab hab' haa hbb).φ.f i ((crossHom F hab').φ.f i x) :=
  (kHom_comp (fixLev_mono F hab) (kInv_fixLev F a) (kInv_fixLev F b) (lev_mono F hab)
    (kInv_lev F a) (kInv_lev F b) (lev_mono F hab') (kInv_lev F a') (kInv_lev F b')
    (fixLev_subset_lev F a) (fixLev_subset_lev F b) (lev_mono F haa) (lev_mono F hbb) i x).trans
  (kHom_comp (fixLev_mono F hab) (kInv_fixLev F a) (kInv_fixLev F b) (fixLev_mono F hab')
    (kInv_fixLev F a') (kInv_fixLev F b') (lev_mono F hab') (kInv_lev F a') (kInv_lev F b')
    (fixLev_mono F haa) (fixLev_mono F hbb) (fixLev_subset_lev F a') (fixLev_subset_lev F b')
    i x).symm

theorem crossEps_eq_epsK {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    crossEps F hab q = epsK (crossHom F hab) (kCommuting_trivial (fixLev_mono F hab)
      (kInv_fixLev F a) (kInv_fixLev F b) (half_fixLev F b)) q :=
  crossEps_eq F hab q

/-- **From tight to wide cuts.** For 0 < a ≤ a' ≤ b' ≤ b with no critical level in [2a, 2a'] and
[2b', 2b], the windowed localization statement in degree q with cutoff j holds for the crossing
pair (t_{2b}, t_{2a}) if and only if it holds for (t_{2b'}, t_{2a'}). -/
theorem loc_tight_iff_wide (hn : 1 ≤ n) {a a' b' b : ℝ} (ha : 0 < a) (haa : a ≤ a')
    (hab' : a' ≤ b') (hbb : b' ≤ b) (hreg1 : ∀ x ∈ Icc (2 * a) (2 * a'), x ∉ crit F)
    (hreg2 : ∀ x ∈ Icc (2 * b') (2 * b), x ∉ crit F) (q j : ℕ) :
    (Function.Injective (crossEps F (by linarith : 2 * a ≤ 2 * b) q) ∧
      LinearMap.range (crossEps F (by linarith : 2 * a ≤ 2 * b) q) =
        LinearMap.range (cut (crossR F (by linarith : 2 * a ≤ 2 * b)) j)) ↔
    (Function.Injective (crossEps F (by linarith : 2 * a' ≤ 2 * b') q) ∧
      LinearMap.range (crossEps F (by linarith : 2 * a' ≤ 2 * b') q) =
        LinearMap.range (cut (crossR F (by linarith : 2 * a' ≤ 2 * b')) j)) := by
  have hw : 2 * a ≤ 2 * b := by linarith
  have hm : 2 * a ≤ 2 * b' := by linarith
  have ht : 2 * a' ≤ 2 * b' := by linarith
  have h2a : 0 < 2 * a := by linarith
  -- half-level strips are regular too
  have hreg1' : ∀ x ∈ Icc a a', x ∉ crit F := fun x hx hc =>
    hreg1 (2 * x) ⟨by linarith [hx.1], by linarith [hx.2]⟩ (crit_double F hc)
  have hreg2' : ∀ x ∈ Icc b' b, x ∉ crit F := fun x hx hc =>
    hreg2 (2 * x) ⟨by linarith [hx.1], by linarith [hx.2]⟩ (crit_double F hc)
  obtain ⟨D₂⟩ := Finsler.CrossingW.levelDeformation_of_regular F hn (2 * b') (2 * b) (2 * b)
    (by linarith) (by linarith) le_rfl hreg2
  obtain ⟨D₁⟩ := Finsler.CrossingW.levelDeformation_of_regular F hn (2 * a) (2 * a') (2 * b') h2a
    (by linarith) (by linarith) hreg1
  obtain ⟨E₂⟩ := Finsler.CrossingW.levelDeformation_of_regular F hn b' b b (by linarith)
    hbb le_rfl hreg2'
  obtain ⟨E₁⟩ := Finsler.CrossingW.levelDeformation_of_regular F hn a a' b' ha haa hab' hreg1'
  -- wide to middle
  have hι₁ : ∀ k, Function.Bijective (HRmap (borelHom (resK F hm hw le_rfl (by linarith))) k) :=
    bijective_subCommHom _ _ _ _ _ _ _ _ _ _ _ _ fun k =>
      bijective_nativePull (lev_mono F hm) (lev_mono F (by linarith : 2 * b' ≤ 2 * b))
        (toDeformation D₂ (2 * a)) k
  have hιh₁ : ∀ l, Function.Bijective (HRmap (resKh F hm hw le_rfl (by linarith)).φ l) :=
    BorelInvariance.bijective_HRmap
      (revSub_sq (fixLev_mono F hm) (kInv_fixLev F (2 * a)).rev_mem (kInv_fixLev F (2 * b')).rev_mem)
      (revSub_sq (fixLev_mono F hw) (kInv_fixLev F (2 * a)).rev_mem (kInv_fixLev F (2 * b)).rev_mem)
      (inclPair (fixLev_mono F hm) (fixLev_mono F hw) (fixLev_mono F le_rfl)
        (fixLev_mono F (by linarith : 2 * b' ≤ 2 * b)))
      (inclPair_equivariant (fixLev_mono F hm) (fixLev_mono F hw) (kInv_fixLev F (2 * a)).rev_mem
        (kInv_fixLev F (2 * b')).rev_mem (kInv_fixLev F (2 * a)).rev_mem
        (kInv_fixLev F (2 * b)).rev_mem (fixLev_mono F le_rfl)
        (fixLev_mono F (by linarith : 2 * b' ≤ 2 * b)))
      (fix_nativePull_bijective F (by linarith : a ≤ b')
      (by linarith : a ≤ b) hm hw le_rfl hbb fun k =>
        bijective_nativePull (lev_mono F (by linarith : a ≤ b')) (lev_mono F hbb)
          (toDeformation E₂ a) k)
  -- tight to middle
  have hι₂ : ∀ k, Function.Bijective (HRmap (borelHom (resK F hm ht (by linarith) le_rfl)) k) :=
    bijective_subCommHom _ _ _ _ _ _ _ _ _ _ _ _ fun k =>
      bijective_nativePull_inclPair (lev_mono F hm) (lev_mono F ht)
        (lev_mono F (by linarith : 2 * a ≤ 2 * a')) subset_rfl
        (toPairDeformation D₁) k
  have hιh₂ : ∀ l, Function.Bijective (HRmap (resKh F hm ht (by linarith) le_rfl).φ l) :=
    BorelInvariance.bijective_HRmap
      (revSub_sq (fixLev_mono F hm) (kInv_fixLev F (2 * a)).rev_mem (kInv_fixLev F (2 * b')).rev_mem)
      (revSub_sq (fixLev_mono F ht) (kInv_fixLev F (2 * a')).rev_mem
        (kInv_fixLev F (2 * b')).rev_mem)
      (inclPair (fixLev_mono F hm) (fixLev_mono F ht) (fixLev_mono F (by linarith : 2 * a ≤ 2 * a'))
        (fixLev_mono F le_rfl))
      (inclPair_equivariant (fixLev_mono F hm) (fixLev_mono F ht) (kInv_fixLev F (2 * a)).rev_mem
        (kInv_fixLev F (2 * b')).rev_mem (kInv_fixLev F (2 * a')).rev_mem
        (kInv_fixLev F (2 * b')).rev_mem (fixLev_mono F (by linarith : 2 * a ≤ 2 * a'))
        (fixLev_mono F le_rfl))
      (fix_nativePull_bijective F (by linarith : a ≤ b')
      hab' hm ht haa le_rfl fun k =>
        bijective_nativePull_inclPair (lev_mono F (by linarith : a ≤ b')) (lev_mono F hab')
          (lev_mono F haa) subset_rfl (toPairDeformation E₁) k)
  have hS : ∀ {c d : ℝ} (hcd : c ≤ d), ∀ i x, (fixS F hcd).s i x = x := fun hcd =>
    kCommuting_trivial (fixLev_mono F hcd) _ _ (half_fixLev F _)
  have e1 := loc_iff (crossHom F hm) (crossHom F hw) (hS hm) (hS hw)
    (resK F hm hw le_rfl (by linarith)) (resKh F hm hw le_rfl (by linarith))
    (resK_comm F hm hw le_rfl (by linarith)) hι₁ hιh₁ q j
  have e2 := loc_iff (crossHom F hm) (crossHom F ht) (hS hm) (hS ht)
    (resK F hm ht (by linarith) le_rfl) (resKh F hm ht (by linarith) le_rfl)
    (resK_comm F hm ht (by linarith) le_rfl) hι₂ hιh₂ q j
  rw [crossEps_eq_epsK, crossEps_eq_epsK]
  exact e1.symm.trans e2

end

end Finsler.StripK
