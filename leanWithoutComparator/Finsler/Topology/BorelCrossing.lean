module

public import Finsler.Topology.BorelExact
public import Finsler.Topology.SpherePuncturedEvaluation
public import Finsler.Topology.FirstAppearance

/-! The actual crossing sequence of the reflection Borel cohomology of Finsler sublevels. For nested
subsets s ⊆ t ⊆ u the relative F₂ singular cochains form a degreewise short exact sequence
0 → C(u, t) → C(u, s) → C(t, s) → 0, proved from Tau Ceti's short exact sequence of a pair. For
levels a ≤ b this gives the crossing pair (t_b, t_a) with the reversal, the long exact sequence
⋯ → H_R^q(t_b, t_a) → B_b^q → B_a^q → H_R^{q+1}(t_b, t_a) → ⋯, and the canonical evaluation action e
on the crossing group, natural for (t_b, M) → (t_b, t_a). Along an increasing sequence of cuts
these maps realize the first-appearance interface: at the first cut where a global class becomes
nonzero it comes from the crossing group, so its e-multiple vanishes there if e acts as zero on
the crossing groups. The same construction for (Λ, t_a) gives the tail sequence
⋯ → H_R^q(Λ, t_a) → B_∞^q → B_a^q → H_R^{q+1}(Λ, t_a) → ⋯, so the kernel of the global restriction is
the image of the tail group and its cokernel embeds in the tail group. Vanishing of e on a
crossing group is a separate geometric input. -/

@[expose] public section

namespace Finsler.BorelCrossing

open CategoryTheory Set SphereOddDegree Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelEvaluation Finsler.SphereTopClass Finsler.RelativeCupCochain

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem cochain_id {Y : TopCat.{0}} (p : ℕ) (α : singularCochainGroup (ZMod 2) Y p) :
    cochainPullback (𝟙 Y) p α = α := by
  have h := congrArg (fun φ => (φ.f p).hom α)
    (singularCochainComplexZMod2.map_id (Opposite.op Y))
  exact h

section Triple

variable {X : TopCat.{0}} {s t u : Set X} (hst : s ⊆ t) (htu : t ⊆ u)

/-- The inclusion of pairs (t, s) → (u, s). -/
def incPair : pairOf hst ⟶ pairOf (hst.trans htu) :=
  pairMap hst (hst.trans htu) (ContinuousMap.inclusion htu) (fun _ hx => hx)

/-- The map of pairs (u, s) → (u, t) which is the identity of u. -/
def relPair : pairOf (hst.trans htu) ⟶ pairOf htu :=
  pairMap (hst.trans htu) htu (ContinuousMap.id u) (fun _ hx => hst hx)

theorem relPair_fst : TopPair.Hom.fst (relPair hst htu) = 𝟙 (pairOf htu).fst := by
  ext x
  rfl

theorem incPair_fst : TopPair.Hom.fst (incPair hst htu) = (pairOf htu).map := by
  ext x
  rfl

theorem map_trans : (pairOf (hst.trans htu)).map = (pairOf hst).map ≫ (pairOf htu).map := by
  ext x
  rfl

/-- The identity of u does not change the ambient cochain of a relative cochain. -/
theorem toAmbient_rel (j : ℕ) (ψ : relative (pairOf htu) j) :
    toAmbient (pairOf (hst.trans htu)) j (pullback (relPair hst htu) j ψ) =
      toAmbient (pairOf htu) j ψ := by
  rw [toAmbient_pullback, relPair_fst]
  exact cochain_id j _

theorem rel_injective (j : ℕ) : Function.Injective (pullback (relPair hst htu) j) := by
  intro ψ₁ ψ₂ he
  apply toAmbient_injective (pairOf htu) j
  rw [← toAmbient_rel hst htu, ← toAmbient_rel hst htu, he]

/-- A cochain of (u, s) vanishing on t is a cochain of (u, t). -/
theorem inc_exact (j : ℕ) (x : relative (pairOf (hst.trans htu)) j)
    (hx : pullback (incPair hst htu) j x = 0) :
    ∃ ψ, pullback (relPair hst htu) j ψ = x := by
  have h0 : cochainPullback (pairOf htu).map j (toAmbient (pairOf (hst.trans htu)) j x) = 0 := by
    rw [← incPair_fst hst htu, ← toAmbient_pullback, hx, map_zero]
  obtain ⟨ψ, hψ⟩ := exists_lift (pairOf htu) j _ h0
  refine ⟨ψ, ?_⟩
  apply toAmbient_injective (pairOf (hst.trans htu)) j
  rw [toAmbient_rel, hψ]

theorem rel_inc_zero (j : ℕ) (ψ : relative (pairOf htu) j) :
    pullback (incPair hst htu) j (pullback (relPair hst htu) j ψ) = 0 := by
  apply toAmbient_injective (pairOf hst) j
  rw [toAmbient_pullback, toAmbient_rel, incPair_fst, map_zero]
  exact restriction_toAmbient (pairOf htu) j ψ

/-- Every cochain of (t, s) extends to a cochain of (u, s). -/
theorem inc_surjective (j : ℕ) : Function.Surjective (pullback (incPair hst htu) j) := by
  intro y
  have hepi : Function.Surjective (sequence (pairOf htu) j).g.hom := by
    have : Epi (sequence (pairOf htu) j).g := (degree_short_exact (pairOf htu) j).epi_g
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨φ, hφ⟩ := hepi (toAmbient (pairOf hst) j y)
  have hφ' : cochainPullback (pairOf htu).map j φ = toAmbient (pairOf hst) j y := hφ
  have h0 : cochainPullback (pairOf (hst.trans htu)).map j φ = 0 := by
    rw [map_trans hst htu, ← cochain_comp, hφ']
    exact restriction_toAmbient (pairOf hst) j y
  obtain ⟨x, hx⟩ := exists_lift (pairOf (hst.trans htu)) j φ h0
  refine ⟨x, ?_⟩
  apply toAmbient_injective (pairOf hst) j
  rw [toAmbient_pullback, incPair_fst, hx, hφ']

end Triple

variable {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) {a b : ℝ} (hab : a ≤ b)

/-- The crossing pair (t_b, t_a). -/
abbrev crossPair : TopPair.{0} := pairOf (lev_mono F hab)

/-- The reversal of the crossing pair. -/
def revCross : crossPair F hab ⟶ crossPair F hab :=
  pairMap _ _ (revLev F b) (fun _ hx => reverse_mem_lev F hx)

theorem revCross_sq : revCross F hab ≫ revCross F hab = 𝟙 (crossPair F hab) := by
  have h : (revLev F b).comp (revLev F b) = ContinuousMap.id (lev F b) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (Finsler.SobolevReverse.reverseSphere_involutive
      (u : Finsler.IntervalSobolev.SphereLoop n)) :
      (⟨Finsler.SobolevReverse.reverseSphere (Finsler.SobolevReverse.reverseSphere
        (u : Finsler.IntervalSobolev.SphereLoop n)), _⟩ : lev F b) = u)
  exact (pairMap_comp (lev_mono F hab) (lev_mono F hab) (lev_mono F hab)
    (revLev F b) (revLev F b) (fun _ hx => reverse_mem_lev F hx)
    (fun _ hx => reverse_mem_lev F hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

/-- The map of pairs (t_b, M) → (t_b, t_a). -/
abbrev relLev : levPair F b ⟶ crossPair F hab :=
  relPair (consts_subset_lev F a) (lev_mono F hab)

theorem relLev_equivariant : relLev F hab ≫ revCross F hab = revPair F b ≫ relLev F hab := by
  ext : 2 <;> rfl

theorem cutPair_eq : cutPair F hab = incPair (consts_subset_lev F a) (lev_mono F hab) := rfl

/-- The involutive cochains of the crossing pair. -/
abbrev crossComplex : InvComplex :=
  ofPair (crossPair F hab) (revCross F hab) (revCross_sq F hab)

/-- The cochain map C(t_b, t_a) → C(t_b, M). -/
abbrev relHom : InvHom (crossComplex F hab) (levComplex F b) :=
  pullHom (revPair_sq F b) (revCross_sq F hab) (relLev F hab) (relLev_equivariant F hab)

/-- The actual relative cochains of (t_b, t_a), (t_b, M) and (t_a, M) form a degreewise short
exact sequence of involutive complexes. -/
theorem shortExact : BorelExact.ShortExact (relHom F hab) (cutHom F hab) where
  inj j := rel_injective (consts_subset_lev F a) (lev_mono F hab) j
  surj j := inc_surjective (consts_subset_lev F a) (lev_mono F hab) j
  zero j z := rel_inc_zero (consts_subset_lev F a) (lev_mono F hab) j z
  exact j x hx := inc_exact (consts_subset_lev F a) (lev_mono F hab) j x hx

/-- Exactness of the reflection Borel crossing sequence at B_b: a class of (t_b, M) vanishing on
t_a comes from the crossing group. -/
theorem exact_crossing (q : ℕ) (x : HR (levComplex F b) q)
    (hx : HRmap (cutHom F hab) q x = 0) :
    ∃ z : HR (crossComplex F hab) q, HRmap (relHom F hab) q z = x :=
  BorelExact.exact_mid (shortExact F hab) q x hx

theorem crossing_cut_zero (q : ℕ) (z : HR (crossComplex F hab) q) :
    HRmap (cutHom F hab) q (HRmap (relHom F hab) q z) = 0 :=
  BorelExact.comp_zero (shortExact F hab) q z

/-- The same exactness for the ordinary relative groups. -/
theorem exact_crossing_ordinary (q : ℕ) (x : H (levComplex F b) q)
    (hx : Hmap (cutHom F hab) q x = 0) :
    ∃ z : H (crossComplex F hab) q, Hmap (relHom F hab) q z = x :=
  BorelExact.exact_mid_ordinary (shortExact F hab) q x hx

/-- The connecting map B_a^q → H_R^{q+1}(t_b, t_a). -/
def crossDelta (q : ℕ) : HR (levComplex F a) q →ₗ[ZMod 2] HR (crossComplex F hab) (q + 1) :=
  BorelExact.delta (shortExact F hab) q

theorem crossDelta_cut (q : ℕ) (x : HR (levComplex F b) q) :
    crossDelta F hab q (HRmap (cutHom F hab) q x) = 0 :=
  BorelExact.delta_comp_zero (shortExact F hab) q x

/-- Exactness at B_a: a class of (t_a, M) with zero connecting image extends to (t_b, M). -/
theorem exact_crossDelta (q : ℕ) (x : HR (levComplex F a) q) (hx : crossDelta F hab q x = 0) :
    ∃ y : HR (levComplex F b) q, HRmap (cutHom F hab) q y = x :=
  BorelExact.exact_delta (shortExact F hab) q x hx

theorem rel_crossDelta (q : ℕ) (x : HR (levComplex F a) q) :
    HRmap (relHom F hab) (q + 1) (crossDelta F hab q x) = 0 :=
  BorelExact.comp_delta_zero (shortExact F hab) q x

/-- Exactness at the crossing group in positive degree. -/
theorem exact_crossing_sub (q : ℕ) (y : HR (crossComplex F hab) (q + 1))
    (hy : HRmap (relHom F hab) (q + 1) y = 0) :
    ∃ x : HR (levComplex F a) q, crossDelta F hab q x = y :=
  BorelExact.exact_sub (shortExact F hab) q y hy

theorem crossDelta_w (q : ℕ) (x : HR (levComplex F a) q) :
    crossDelta F hab (q + 1) (w _ q x) = w _ (q + 1) (crossDelta F hab q x) :=
  BorelExact.delta_w (shortExact F hab) q x

section Tail

variable (a : ℝ)

/-- The tail pair (Λ, t_a). -/
abbrev tailPair : TopPair.{0} := pairOf (subset_univ (lev F a))

/-- The reversal of the tail pair. -/
def revTail : tailPair F a ⟶ tailPair F a :=
  pairMap _ _ (revFull n) (fun _ hx => reverse_mem_lev F hx)

theorem revTail_sq : revTail F a ≫ revTail F a = 𝟙 (tailPair F a) := by
  have h : (revFull n).comp (revFull n) = ContinuousMap.id (univ : Set (Loops n)) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (Finsler.SobolevReverse.reverseSphere_involutive
      (u : Finsler.IntervalSobolev.SphereLoop n)) :
      (⟨Finsler.SobolevReverse.reverseSphere (Finsler.SobolevReverse.reverseSphere
        (u : Finsler.IntervalSobolev.SphereLoop n)), mem_univ _⟩ : (univ : Set (Loops n))) = u)
  exact (pairMap_comp (subset_univ (lev F a)) (subset_univ (lev F a)) (subset_univ (lev F a))
    (revFull n) (revFull n) (fun _ hx => reverse_mem_lev F hx)
    (fun _ hx => reverse_mem_lev F hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

/-- The map of pairs (Λ, M) → (Λ, t_a). -/
abbrev relFull : fullPair n ⟶ tailPair F a :=
  relPair (consts_subset_lev F a) (subset_univ (lev F a))

theorem relFull_equivariant : relFull F a ≫ revTail F a = revFullPair n ≫ relFull F a := by
  ext : 2 <;> rfl

theorem resPair_eq : resPair F a = incPair (consts_subset_lev F a) (subset_univ (lev F a)) := rfl

/-- The involutive cochains of the tail pair. -/
abbrev tailComplex : InvComplex := ofPair (tailPair F a) (revTail F a) (revTail_sq F a)

/-- The cochain map C(Λ, t_a) → C(Λ, M). -/
abbrev tailHom : InvHom (tailComplex F a) (fullComplex n) :=
  pullHom (revFullPair_sq n) (revTail_sq F a) (relFull F a) (relFull_equivariant F a)

/-- The actual relative cochains of (Λ, t_a), (Λ, M) and (t_a, M) form a degreewise short exact
sequence of involutive complexes. -/
theorem shortExactTail : BorelExact.ShortExact (tailHom F a) (resHom F a) where
  inj j := rel_injective (consts_subset_lev F a) (subset_univ (lev F a)) j
  surj j := inc_surjective (consts_subset_lev F a) (subset_univ (lev F a)) j
  zero j z := rel_inc_zero (consts_subset_lev F a) (subset_univ (lev F a)) j z
  exact j x hx := inc_exact (consts_subset_lev F a) (subset_univ (lev F a)) j x hx

/-- A global reflection class vanishing on t_a comes from the tail group H_R(Λ, t_a). -/
theorem exact_tail (q : ℕ) (x : HR (fullComplex n) q) (hx : HRmap (resHom F a) q x = 0) :
    ∃ z : HR (tailComplex F a) q, HRmap (tailHom F a) q z = x :=
  BorelExact.exact_mid (shortExactTail F a) q x hx

theorem tail_res_zero (q : ℕ) (z : HR (tailComplex F a) q) :
    HRmap (resHom F a) q (HRmap (tailHom F a) q z) = 0 :=
  BorelExact.comp_zero (shortExactTail F a) q z

/-- The same exactness for the ordinary relative groups. -/
theorem exact_tail_ordinary (q : ℕ) (x : H (fullComplex n) q) (hx : Hmap (resHom F a) q x = 0) :
    ∃ z : H (tailComplex F a) q, Hmap (tailHom F a) q z = x :=
  BorelExact.exact_mid_ordinary (shortExactTail F a) q x hx

/-- The connecting map B_a^q → H_R^{q+1}(Λ, t_a). -/
def tailDelta (q : ℕ) : HR (levComplex F a) q →ₗ[ZMod 2] HR (tailComplex F a) (q + 1) :=
  BorelExact.delta (shortExactTail F a) q

theorem tailDelta_res (q : ℕ) (x : HR (fullComplex n) q) :
    tailDelta F a q (HRmap (resHom F a) q x) = 0 :=
  BorelExact.delta_comp_zero (shortExactTail F a) q x

/-- A class of (t_a, M) is the restriction of a global class exactly when its connecting image
in H_R(Λ, t_a) vanishes: the cokernel of the global restriction embeds in the tail group. -/
theorem exact_tailDelta (q : ℕ) (x : HR (levComplex F a) q) (hx : tailDelta F a q x = 0) :
    ∃ y : HR (fullComplex n) q, HRmap (resHom F a) q y = x :=
  BorelExact.exact_delta (shortExactTail F a) q x hx

theorem tail_tailDelta (q : ℕ) (x : HR (levComplex F a) q) :
    HRmap (tailHom F a) (q + 1) (tailDelta F a q x) = 0 :=
  BorelExact.comp_delta_zero (shortExactTail F a) q x

/-- Exactness at the tail group in positive degree. -/
theorem exact_tail_sub (q : ℕ) (y : HR (tailComplex F a) (q + 1))
    (hy : HRmap (tailHom F a) (q + 1) y = 0) :
    ∃ x : HR (levComplex F a) q, tailDelta F a q x = y :=
  BorelExact.exact_sub (shortExactTail F a) q y hy

theorem tailDelta_w (q : ℕ) (x : HR (levComplex F a) q) :
    tailDelta F a (q + 1) (w _ q x) = w _ (q + 1) (tailDelta F a q x) :=
  BorelExact.delta_w (shortExactTail F a) q x

end Tail

/-- Evaluation at zero on the ambient space t_b of the crossing pair. -/
def crossEval : (crossPair F hab).fst ⟶ sphere n := levEval F b

theorem crossEval_invariant :
    TopPair.Hom.fst (revCross F hab) ≫ crossEval F hab = crossEval F hab := by
  ext u : 1
  exact eval_reverse u.val

theorem rel_eval : TopPair.Hom.fst (relLev F hab) ≫ crossEval F hab = levEval F b := by
  ext u
  rfl

/-- The action of an actual sphere class on the crossing group. -/
def crossClassCup (p : ℕ) (s : cohomologyZMod2 (sphere n) p) (q : ℕ) :
    HR (crossComplex F hab) q →ₗ[ZMod 2] HR (crossComplex F hab) (p + q) :=
  BorelCup.cup (crossPair F hab) (revCross F hab) (revCross_sq F hab) p
    (cochainPullback (crossEval F hab) p (classRepr (sphere n) p s))
    (cochainPullback_cocycle _ _ _ (classRepr_isCocycle (sphere n) p s))
    (cochain_invariant _ _ (crossEval_invariant F hab) p _) q

/-- The canonical e action on the crossing group. -/
def crossE (hn : 1 ≤ n) (q : ℕ) :
    HR (crossComplex F hab) q →ₗ[ZMod 2] HR (crossComplex F hab) (n + q) :=
  crossClassCup F hab n (topClass n hn) q

/-- The crossing action is the representative-independent class action. -/
theorem crossClassCup_eq_action (p : ℕ) (s : cohomologyZMod2 (sphere n) p) (q : ℕ) :
    crossClassCup F hab p s q =
      (BorelPullbackCup.classAction (crossPair F hab) (revCross F hab) (revCross_sq F hab)
        (crossEval F hab) (crossEval_invariant F hab) p q).hom s := by
  have h := BorelPullbackCup.classAction_mk (crossPair F hab) (revCross F hab)
    (revCross_sq F hab) (crossEval F hab) (crossEval_invariant F hab) p
    (classRepr (sphere n) p s) (classRepr_isCocycle (sphere n) p s) q
  change (BorelPullbackCup.classAction (crossPair F hab) (revCross F hab) (revCross_sq F hab)
    (crossEval F hab) (crossEval_invariant F hab) p q).hom (cocycleClass (sphere n) p _ _) =
    crossClassCup F hab p s q at h
  rw [cocycleClass_classRepr] at h
  exact h.symm

/-- Naturality of the sphere class action for (t_b, M) → (t_b, t_a). -/
theorem crossClassCup_rel (p : ℕ) (s : cohomologyZMod2 (sphere n) p) (q : ℕ)
    (z : HR (crossComplex F hab) q) :
    HRmap (relHom F hab) (p + q) (crossClassCup F hab p s q z) =
      levClassCup F b p s q (HRmap (relHom F hab) q z) := by
  apply BorelCup.cup_natural
  rw [cochain_comp, rel_eval]

/-- Naturality of e: the image of an e-multiple of a crossing class is e times its image. -/
theorem crossE_rel (hn : 1 ≤ n) (q : ℕ) (z : HR (crossComplex F hab) q) :
    HRmap (relHom F hab) (n + q) (crossE F hab hn q z) =
      BorelCanonicalEvaluation.levE F b hn q (HRmap (relHom F hab) q z) :=
  crossClassCup_rel F hab n (topClass n hn) q z

/-- If the evaluation of the crossing pair avoids a point, e acts as zero on the crossing
group. The hypothesis never holds for a crossing pair containing all constant loops; it is the
form used after excision to a neighbourhood of the critical set. -/
theorem crossE_zero_of_avoids (hn : 1 ≤ n) (p : Finsler.SphereGeometry.Sphere n)
    (hp : ∀ x, crossEval F hab x ≠ p) (q : ℕ) : crossE F hab hn q = 0 := by
  rw [crossE, crossClassCup_eq_action]
  exact SpherePuncturedEvaluation.classAction_topClass_zero_of_avoids (crossPair F hab)
    (revCross F hab) (revCross_sq F hab) n hn p (crossEval F hab) (crossEval_invariant F hab) hp q

section Sequence

variable (c : ℕ → ℝ) (hc : Monotone c) (hn : 1 ≤ n) (q : ℕ)

/-- The actual first-appearance system of a global reflection Borel degree along an increasing
sequence of cuts: restrictions, crossing maps and the e actions with their naturality. -/
def firstData : Finsler.FirstAppearance.Data (HR (fullComplex n) q)
    (fun i => HR (levComplex F (c i)) q) (fun i => HR (levComplex F (c i)) (n + q))
    (fun i => HR (crossComplex F (hc (Nat.le_succ i))) q)
    (fun i => HR (crossComplex F (hc (Nat.le_succ i))) (n + q)) where
  restrict i := (HRmap (cutHom F (hc (Nat.le_succ i))) q).toAddMonoidHom
  res i := (HRmap (resHom F (c i)) q).toAddMonoidHom
  crossing i := (HRmap (relHom F (hc (Nat.le_succ i))) q).toAddMonoidHom
  cup i := (BorelCanonicalEvaluation.levE F (c i) hn q).toAddMonoidHom
  localCup i := (crossE F (hc (Nat.le_succ i)) hn q).toAddMonoidHom
  crossingCup i := (HRmap (relHom F (hc (Nat.le_succ i))) (n + q)).toAddMonoidHom
  natural_res i x := by
    change HRmap (cutHom F (hc (Nat.le_succ i))) q (HRmap (resHom F (c (i + 1))) q x) =
      HRmap (resHom F (c i)) q x
    rw [← HRmap_comp]
    exact HRmap_congr (cut_res_f F (hc (Nat.le_succ i))) q x
  exact_crossing i x hx := exact_crossing F (hc (Nat.le_succ i)) q x hx
  natural_cup i z := (crossE_rel F (hc (Nat.le_succ i)) hn q z).symm

/-- At the first cut of the sequence where a global reflection class is nonzero, its e-multiple
vanishes, provided e acts as zero on the crossing groups before that cut. -/
theorem first_visible_e_zero (x : HR (fullComplex n) q) (m : ℕ)
    (hzero : HRmap (resHom F (c 0)) q x = 0) (hm : HRmap (resHom F (c m)) q x ≠ 0)
    (local_zero : ∀ i, i < m → ∀ z, crossE F (hc (Nat.le_succ i)) hn q z = 0) :
    ∃ i, i < m ∧ HRmap (resHom F (c i)) q x = 0 ∧ HRmap (resHom F (c (i + 1))) q x ≠ 0 ∧
      BorelCanonicalEvaluation.levE F (c (i + 1)) hn q (HRmap (resHom F (c (i + 1))) q x) = 0 :=
  Finsler.FirstAppearance.first_cup_zero (firstData F c hc hn q) x m hzero hm local_zero

/-- The abstract doubling-plateau contradiction applied to the actual reflection Borel groups: a
global class which is zero at the first cut stays zero, when e vanishes on the crossing groups and
the doubling rank budgets at the successor cuts are plateaux whose distinguished label counts the
class and its e-partner. -/
theorem not_visible_of_doubling_plateau {ι : Type*} (x : HR (fullComplex n) q) (m : ℕ)
    (budgets : ℕ → Finsler.PartnerRank.Data ι) (label : ℕ → ι)
    (hzero : HRmap (resHom F (c 0)) q x = 0)
    (local_zero : ∀ i, i < m → ∀ z, crossE F (hc (Nat.le_succ i)) hn q z = 0)
    (member : ∀ i, i < m → label i ∈ (budgets i).labels)
    (bottom_rank : ∀ i, i < m → (budgets i).bottom (label i) =
      Finsler.FirstAppearance.bottom (firstData F c hc hn q) x (i + 1))
    (partner_rank : ∀ i, i < m → (budgets i).partner (label i) =
      Finsler.FirstAppearance.partner (firstData F c hc hn q) x (i + 1))
    (plateau : ∀ i, i < m → (budgets i).Tdouble = (budgets i).T) :
    HRmap (resHom F (c m)) q x = 0 :=
  Finsler.FirstAppearance.not_visible_of_doubling_plateau (firstData F c hc hn q) x m budgets
    label hzero local_zero member bottom_rank partner_rank plateau

end Sequence

end

end Finsler.BorelCrossing
