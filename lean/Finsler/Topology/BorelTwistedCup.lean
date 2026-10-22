module
public import Finsler.Topology.BorelAbsolute
public import Finsler.Topology.BorelEvaluationLaws
/-! Actual iterated singular-cochain pullback preserves cup and differential, with involutive two-periodicity and the twisted norm Leibniz identity. The finite horizontal-degree-twisted total convolution is bilinear, has the required finite support and recovers ordinary cup in its top component. For a closed strictly invariant left single, it equals the actual graded total map and commutes with the total differential. The general two-input total Leibniz identity, boundary descent and full absolute Borel ring laws remain open. -/

@[expose] public section
namespace Finsler.BorelTwistedCup
open CategoryTheory SphereOddDegree
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (r : X ⟶ X)

def act (k p : ℕ) : singularCochainGroup (ZMod 2) X p →ₗ[ZMod 2] singularCochainGroup (ZMod 2) X p :=
  (((singularCochainComplexZMod2.map r.op).f p).hom)^k

theorem act_succ_left (k p : ℕ) (α : singularCochainGroup (ZMod 2) X p) :
    act r (k+1) p α=cochainPullback r p (act r k p α) := by
  simp only [act,pow_succ',Module.End.mul_apply]
  rfl

theorem act_succ_right (k p : ℕ) (α : singularCochainGroup (ZMod 2) X p) :
    act r (k+1) p α=act r k p (cochainPullback r p α) := by
  simp only [act,pow_succ,Module.End.mul_apply]
  rfl

theorem act_cup (k p q : ℕ) (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q) :
    act r k (p+q) (cochainCup p q α β)=cochainCup p q (act r k p α) (act r k q β) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [act_succ_left,ih,cochainCup_naturality,act_succ_left,act_succ_left]

def norm (p : ℕ) (α : singularCochainGroup (ZMod 2) X p) := α+cochainPullback r p α

/-- The group differential needs the twist on the right factor when the left group degree increases. -/
theorem norm_cup (k p q : ℕ) (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q) :
    norm r (p+q) (cochainCup p q α (act r k q β))=
      cochainCup p q (norm r p α) (act r (k+1) q β)+cochainCup p q α (act r k q (norm r q β)) := by
  let A := cochainCup p q α (act r k q β)
  let B := cochainCup p q (cochainPullback r p α) (act r (k+1) q β)
  let C := cochainCup p q α (act r (k+1) q β)
  have hl : norm r (p+q) (cochainCup p q α (act r k q β))=A+B := by
    rw [norm,cochainCup_naturality,←act_succ_left]
  have hr : cochainCup p q (norm r p α) (act r (k+1) q β)+cochainCup p q α (act r k q (norm r q β))=(C+B)+(A+C) := by
    rw [norm,norm,map_add,cochainCup_add_left,cochainCup_add_right,←act_succ_right]
  rw [hl,hr]
  have hc : C+C=0 := Finsler.BorelCochain.two_eq_zero_of_mod _
  calc
    _ = (C+C)+(A+B) := by rw [hc,zero_add]
    _ = (C+B)+(A+C) := by abel

theorem act_coboundary (k p : ℕ) (α : singularCochainGroup (ZMod 2) X p) :
    cochainCoboundary (ZMod 2) X p (act r k p α)=act r k (p+1) (cochainCoboundary (ZMod 2) X p α) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [act_succ_left,cochainPullback_cochainCoboundary,ih,act_succ_left]

theorem act_invariant (k p : ℕ) (α : singularCochainGroup (ZMod 2) X p) (hα : cochainPullback r p α=α) :
    act r k p α=α := by
  induction k with
  | zero => rfl
  | succ k ih => rw [act_succ_left,ih,hα]

theorem act_periodic (hr : r≫r=𝟙 X) (k p : ℕ) (α : singularCochainGroup (ZMod 2) X p) :
    act r (k+2) p α=act r k p α := by
  calc
    _ = cochainPullback r p (cochainPullback r p (act r k p α)) := by
      rw [show k+2=(k+1)+1 by omega,act_succ_left,act_succ_left]
    _ = _ := (BorelAbsolute.ofSpace X r hr).tt p (act r k p α)


open Finsler.BorelCochain SphereOddDegree.AlexanderWhitney

theorem cast_absolute (hr : r≫r=𝟙 X) {a b : ℕ} (h : a=b)
    (x : singularCochainGroup (ZMod 2) X a) :
    cochainCast h x=BorelGraded.castC (BorelAbsolute.ofSpace X r hr) h x := by
  subst b
  rfl

theorem cast_cup_right {b c : ℕ} (h : b=c) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X b) :
    cochainCast (congrArg (p+·) h) (cochainCup p b α β)=cochainCup p c α (cochainCast h β) := by
  subst c
  simp [cochainCast]

theorem cast_seq {a b : ℕ} (h : a=b) (x : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    cochainCast h (x a)=x b := by
  subst b
  simp [cochainCast]

/-- A single summand of the actual group-degree-twisted total product. -/
def term (p k a : ℕ) (x y : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    singularCochainGroup (ZMod 2) X k :=
  if h : a≤k ∧ a≤p then
    cochainCast (by omega) (cochainCup a (k-a) (x a) (act r (p-a) (k-a) (y (k-a))))
  else 0

/-- Finite convolution in vertical degree, with the necessary horizontal-degree twist. -/
def totalCup (p : ℕ) (x y : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    (j : ℕ) → singularCochainGroup (ZMod 2) X j :=
  fun k => ∑ a ∈ Finset.range (k+1), term r p k a x y

theorem term_add_left (p k a : ℕ) (x z y : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    term r p k a (x+z) y=term r p k a x y+term r p k a z y := by
  unfold term
  split_ifs <;> simp only [Pi.add_apply,cochainCup_add_left,cochainCast_add,add_zero]

theorem term_add_right (p k a : ℕ) (x y z : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    term r p k a x (y+z)=term r p k a x y+term r p k a x z := by
  unfold term
  split_ifs <;> simp only [Pi.add_apply,map_add,cochainCup_add_right,cochainCast_add,add_zero]

theorem term_zero_left (p k a : ℕ) (y : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    term r p k a 0 y=0 := by
  unfold term
  split_ifs <;> simp only [Pi.zero_apply,cochainCup_zero_left,cochainCast_zero]

theorem term_zero_right (p k a : ℕ) (x : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    term r p k a x 0=0 := by
  unfold term
  split_ifs <;> simp only [Pi.zero_apply,map_zero,cochainCup_zero_right,cochainCast_zero]

theorem totalCup_add_left (p : ℕ) (x z y : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    totalCup r p (x+z) y=totalCup r p x y+totalCup r p z y := by
  funext k
  simp only [totalCup,term_add_left,Finset.sum_add_distrib,Pi.add_apply]

theorem totalCup_add_right (p : ℕ) (x y z : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    totalCup r p x (y+z)=totalCup r p x y+totalCup r p x z := by
  funext k
  simp only [totalCup,term_add_right,Finset.sum_add_distrib,Pi.add_apply]

theorem totalCup_zero_left (p : ℕ) (y : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    totalCup r p 0 y=0 := by
  funext k
  simp only [totalCup,term_zero_left,Finset.sum_const_zero,Pi.zero_apply]

theorem totalCup_zero_right (p : ℕ) (x : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    totalCup r p x 0=0 := by
  funext k
  simp only [totalCup,term_zero_right,Finset.sum_const_zero,Pi.zero_apply]

theorem totalCup_low (hr : r≫r=𝟙 X) (p q : ℕ)
    (x y : Seq (BorelAbsolute.ofSpace X r hr)) (hy : y ∈ low (BorelAbsolute.ofSpace X r hr) (q+1)) :
    totalCup r p x y ∈ low (BorelAbsolute.ofSpace X r hr) (p+q+1) := by
  intro k hk
  apply Finset.sum_eq_zero
  intro a ha
  unfold term
  split_ifs with h
  · have hb : q+1≤k-a := by omega
    rw [hy (k-a) hb,map_zero,cochainCup_zero_right,cochainCast_zero]
  · rfl

/-- The ordinary top component forgets the twist and recovers the actual cup. -/
theorem totalCup_top (hr : r≫r=𝟙 X) (p q : ℕ)
    (x y : Seq (BorelAbsolute.ofSpace X r hr)) (hy : y ∈ low (BorelAbsolute.ofSpace X r hr) (q+1)) :
    totalCup r p x y (p+q)=cochainCup p q (x p) (y q) := by
  change (j : ℕ) → singularCochainGroup (ZMod 2) X j at x y
  unfold totalCup
  rw [Finset.sum_eq_single p]
  · unfold term
    rw [dite_eq_left (show p≤p+q ∧ p≤p by omega)]
    have hs : p+q-p=q := by omega
    simp only [Nat.sub_self,act,pow_zero,Module.End.one_apply]
    exact (cast_cup_right hs p (x p) (y (p+q-p))).trans (congrArg (cochainCup p q (x p)) (cast_seq hs y))
  · intro a ha hap
    unfold term
    split_ifs with h
    · have hb : q+1≤p+q-a := by omega
      rw [hy (p+q-a) hb,map_zero,cochainCup_zero_right,cochainCast_zero]
    · rfl
  · intro hp
    exact False.elim (hp (Finset.mem_range.mpr (by omega)))


/-- Multiplication by an invariant closed single cochain is an actual total cochain map. -/
def gradedCup (hr : r≫r=𝟙 X) (p : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0) (hi : cochainPullback r p α=α) :
    BorelGraded.Map (BorelAbsolute.ofSpace X r hr) (BorelAbsolute.ofSpace X r hr) p where
  f j := {
    toFun := cochainCup p j α
    map_add' := cochainCup_add_right p j α
    map_smul' := fun a ψ => cochainCup_smul_right p j a α ψ }
  comm_d j x := by
    change cochainCoboundary (ZMod 2) X (p+j) (cochainCup p j α x)=_
    have h := cochainCupZMod2_differential p j α x
    rw [hα,cochainCup_zero_left,cochainCast_zero,zero_add] at h
    exact h.trans (cast_absolute r hr _ _)
  comm_t j x := by
    change cochainPullback r (p+j) (cochainCup p j α x)=cochainCup p j α (cochainPullback r j x)
    rw [cochainCup_naturality,hi]

/-- The finite twisted formula recovers invariant left multiplication in all components. -/
theorem totalCup_single_left (hr : r≫r=𝟙 X) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0) (hi : cochainPullback r p α=α)
    (y : Seq (BorelAbsolute.ofSpace X r hr)) :
    totalCup r p (Pi.single p α) y=BorelGraded.total (gradedCup r hr p α hα hi) y := by
  change (j : ℕ) → singularCochainGroup (ZMod 2) X j at y
  funext k
  by_cases hp : p≤k
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hp
    rw [BorelGraded.total_at]
    unfold totalCup
    rw [Finset.sum_eq_single p]
    · unfold term
      rw [dite_eq_left (show p≤p+j ∧ p≤p by omega)]
      change cochainCast _ (cochainCup p (p+j-p) ((Pi.single p α) p) (act r (p-p) (p+j-p) (y (p+j-p))))=cochainCup p j α (y j)
      simp only [Nat.sub_self,act,pow_zero,Module.End.one_apply,Pi.single_eq_same]
      have hs : p+j-p=j := by omega
      exact (cast_cup_right hs p α (y (p+j-p))).trans (congrArg (cochainCup p j α) (cast_seq hs y))
    · intro a ha hap
      unfold term
      split_ifs with h
      · rw [single_ne (BorelAbsolute.ofSpace X r hr) hap,cochainCup_zero_left,cochainCast_zero]
      · rfl
    · intro hp
      exact False.elim (hp (Finset.mem_range.mpr (by omega)))
  · rw [BorelGraded.total_below _ _ (by omega)]
    apply Finset.sum_eq_zero
    intro a ha
    unfold term
    split_ifs with h
    · rw [single_ne (BorelAbsolute.ofSpace X r hr) (show a≠p by omega),cochainCup_zero_left,cochainCast_zero]
    · rfl

/-- The total differential law needed by the already constructed evaluation element. -/
theorem totalCup_single_D (hr : r≫r=𝟙 X) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0) (hi : cochainPullback r p α=α)
    (y : Seq (BorelAbsolute.ofSpace X r hr)) :
    D (BorelAbsolute.ofSpace X r hr) (totalCup r p (Pi.single p α) y)=
      totalCup r p (Pi.single p α) (D (BorelAbsolute.ofSpace X r hr) y) := by
  rw [totalCup_single_left r hr p α hα hi,totalCup_single_left r hr p α hα hi]
  exact BorelGraded.total_D _ y


theorem cast_smul {a b : ℕ} (h : a=b) (s : ZMod 2)
    (x : singularCochainGroup (ZMod 2) X a) : cochainCast h (s • x)=s • cochainCast h x := by
  subst b
  simp [cochainCast]

theorem term_smul_left (p k a : ℕ) (s : ZMod 2)
    (x y : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    term r p k a (s • x) y=s • term r p k a x y := by
  unfold term
  split_ifs <;> simp only [Pi.smul_apply,cochainCup_smul_left,cast_smul,smul_zero]

theorem term_smul_right (p k a : ℕ) (s : ZMod 2)
    (x y : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    term r p k a x (s • y)=s • term r p k a x y := by
  unfold term
  split_ifs <;> simp only [Pi.smul_apply,map_smul,cochainCup_smul_right,cast_smul,smul_zero]

theorem totalCup_smul_left (p : ℕ) (s : ZMod 2)
    (x y : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    totalCup r p (s • x) y=s • totalCup r p x y := by
  funext k
  simp only [totalCup,term_smul_left,←Finset.smul_sum,Pi.smul_apply]

theorem totalCup_smul_right (p : ℕ) (s : ZMod 2)
    (x y : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    totalCup r p x (s • y)=s • totalCup r p x y := by
  funext k
  simp only [totalCup,term_smul_right,←Finset.smul_sum,Pi.smul_apply]

/-- The actual finite twisted convolution is bilinear before passing to cohomology. -/
def pairing (p : ℕ) :
    ((j : ℕ) → singularCochainGroup (ZMod 2) X j) →ₗ[ZMod 2]
    ((j : ℕ) → singularCochainGroup (ZMod 2) X j) →ₗ[ZMod 2]
    ((j : ℕ) → singularCochainGroup (ZMod 2) X j) where
  toFun x := {
    toFun := totalCup r p x
    map_add' := totalCup_add_right r p x
    map_smul' := fun s y => totalCup_smul_right r p s x y }
  map_add' x z := by
    apply LinearMap.ext
    exact totalCup_add_left r p x z
  map_smul' s x := by
    apply LinearMap.ext
    exact totalCup_smul_left r p s x

end
end Finsler.BorelTwistedCup
