module
public import Finsler.Topology.BorelTwistedCup
/-! Actual elementary twisted shift maps satisfy the total Leibniz identity for every cochain, with no invariant or closed assumption on the left cochain. The finite convolution equals the sum of elementary shifts. Its differentiated finite sums are identified with convolution by the actual D of the left sequence, using the explicit left finite-support hypothesis. Consequently the general two-input total Leibniz identity holds in all degrees, including zero, for the actual absolute reflection singular-cochain complex. Quotient boundary descent, arbitrary-class Borel cup, full ring/module laws, K/O(2), localization and geometric Borel comparison remain open. -/

@[expose] public section
namespace Finsler.BorelTwistedDifferential
open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelTwistedCup
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : TopCat.{0}} (r : X ⟶ X) (hr : r≫r=𝟙 X)

def shift (p i : ℕ) (α : singularCochainGroup (ZMod 2) X p) :
    Seq (BorelAbsolute.ofSpace X r hr) →ₗ[ZMod 2] Seq (BorelAbsolute.ofSpace X r hr) where
  toFun y k := if h : p≤k then
    BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (by omega)
      (SphereOddDegree.cochainCup p (k-p) α (act r i (k-p) (y (k-p))))
    else 0
  map_add' y z := by
    funext k
    by_cases h : p≤k <;> simp [h,map_add,cochainCup_add_right]
  map_smul' a y := by
    funext k
    by_cases h : p≤k <;> simp [h,map_smul,cochainCup_smul_right]

theorem cast_cup_act {a b : ℕ} (h : a=b) (p i : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (y : Seq (BorelAbsolute.ofSpace X r hr)) :
    BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (congrArg (p+·) h)
      (SphereOddDegree.cochainCup p a α (act r i a (y a)))=
      SphereOddDegree.cochainCup p b α (act r i b (y b)) := by
  subst b
  rfl

theorem shift_at (p i : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (y : Seq (BorelAbsolute.ofSpace X r hr)) (k : ℕ) :
    shift r hr p i α y (p+k)=SphereOddDegree.cochainCup p k α (act r i k (y k)) := by
  change (if h : p≤p+k then _ else 0)=_
  rw [dite_eq_left (show p≤p+k by omega)]
  exact cast_cup_act r hr (show p+k-p=k by omega) p i α y

theorem shift_below (p i : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (y : Seq (BorelAbsolute.ofSpace X r hr)) {k : ℕ} (hk : k<p) : shift r hr p i α y k=0 := by
  change (if h : p≤k then _ else 0)=0
  rw [dite_eq_right (show ¬p≤k by omega)]

theorem shift_low (p i q : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (y : Seq (BorelAbsolute.ofSpace X r hr)) (hy : y ∈ low (BorelAbsolute.ofSpace X r hr) q) :
    shift r hr p i α y ∈ low (BorelAbsolute.ofSpace X r hr) (p+q) := by
  intro k hk
  have hp : p≤k := by omega
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [shift_at,hy j (by omega),map_zero,cochainCup_zero_right]


open SphereOddDegree.AlexanderWhitney

theorem differential_cup_act (p i k : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (β : singularCochainGroup (ZMod 2) X k) :
    (BorelAbsolute.ofSpace X r hr).d (p+k) (SphereOddDegree.cochainCup p k α (act r i k β))=
      BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (aw_degree_left_succ p k)
        (SphereOddDegree.cochainCup (p+1) k (cochainCoboundary (ZMod 2) X p α) (act r i k β))+
      BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (aw_degree_right_succ p k)
        (SphereOddDegree.cochainCup p (k+1) α (act r i (k+1) (cochainCoboundary (ZMod 2) X k β))) := by
  change cochainCoboundary (ZMod 2) X (p+k) (SphereOddDegree.cochainCup p k α (act r i k β))=_
  rw [cochainCupZMod2_differential,act_coboundary,cast_absolute r hr,cast_absolute r hr]

theorem norm_cup_act (p i k : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (β : singularCochainGroup (ZMod 2) X k) :
    tr (BorelAbsolute.ofSpace X r hr) (p+k) (SphereOddDegree.cochainCup p k α (act r i k β))=
      SphereOddDegree.cochainCup p k (norm r p α) (act r (i+1) k β)+
      SphereOddDegree.cochainCup p k α (act r i k (norm r k β)) := by
  exact norm_cup r i p k α β

/-- Single-summand total Leibniz law without invariant or cocycle assumptions on α. -/
theorem shift_D (p i : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (y : Seq (BorelAbsolute.ofSpace X r hr)) :
    D (BorelAbsolute.ofSpace X r hr) (shift r hr p i α y)=
      shift r hr p (i+1) (norm r p α) y+
      shift r hr (p+1) i (cochainCoboundary (ZMod 2) X p α) y+
      shift r hr p i α (D (BorelAbsolute.ofSpace X r hr) y) := by
  change (j : ℕ) → singularCochainGroup (ZMod 2) X j at y
  funext j
  simp only [Pi.add_apply]
  by_cases hp : p≤j
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hp
    cases k with
    | zero =>
      simp only [Nat.add_zero]
      rw [shift_below r hr (p+1) i _ y (by omega)]
      simp only [add_zero]
      cases p with
      | zero =>
        change tr (BorelAbsolute.ofSpace X r hr) (0+0) (shift r hr 0 i α y (0+0))=_
        rw [shift_at r hr _ i α y 0, shift_at r hr _ (i+1) (norm r _ α) y 0, shift_at r hr _ i α (D (BorelAbsolute.ofSpace X r hr) y) 0, D_zero]
        exact norm_cup r i 0 0 α (y 0)
      | succ p =>
        rw [D_succ,shift_below r hr (p+1) i α y (by omega),map_zero,zero_add]
        change tr (BorelAbsolute.ofSpace X r hr) ((p+1)+0) (shift r hr (p+1) i α y ((p+1)+0))=_
        rw [shift_at r hr _ i α y 0, shift_at r hr _ (i+1) (norm r _ α) y 0, shift_at r hr _ i α (D (BorelAbsolute.ofSpace X r hr) y) 0, D_zero]
        exact norm_cup r i (p+1) 0 α (y 0)
    | succ k =>
      rw [show p+(k+1)=p+k+1 by omega,D_succ,shift_at,differential_cup_act]
      have ht : ∀ i α (z : Seq (BorelAbsolute.ofSpace X r hr)), shift r hr p i α z (p+k+1)=
          BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p k 1).symm
            (SphereOddDegree.cochainCup p (k+1) α (act r i (k+1) (z (k+1)))) := by
        intro i α z
        exact (BorelGraded.cast_seq (Nat.add_assoc p k 1).symm (shift r hr p i α z)).trans
          (congrArg (BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p k 1).symm) (shift_at r hr p i α z (k+1)))
      have hd : shift r hr (p+1) i (cochainCoboundary (ZMod 2) X p α) y (p+k+1)=
          BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (aw_degree_left_succ p k)
            (SphereOddDegree.cochainCup (p+1) k (cochainCoboundary (ZMod 2) X p α) (act r i k (y k))) := by
        exact (BorelGraded.cast_seq (aw_degree_left_succ p k) (shift r hr (p+1) i _ y)).trans
          (congrArg (BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (aw_degree_left_succ p k)) (shift_at r hr (p+1) i _ y k))
      rw [ht,ht,ht,hd,BorelGraded.cast_tr,norm_cup_act,D_succ]
      simp only [map_add,cochainCup_add_right]
      have hd0 : (BorelAbsolute.ofSpace X r hr).d k (y k)=cochainCoboundary (ZMod 2) X k (y k) := rfl
      have ht0 : tr (BorelAbsolute.ofSpace X r hr) (k+1) (y (k+1))=norm r (k+1) (y (k+1)) := rfl
      rw [hd0,ht0]
      abel
  · have hlt : j<p := by omega
    rw [shift_below r hr p (i+1) _ y hlt,shift_below r hr (p+1) i _ y (by omega),shift_below r hr p i α _ hlt,add_zero,add_zero]
    cases j with
    | zero => rw [D_zero,shift_below r hr p i α y hlt,map_zero]
    | succ j => rw [D_succ,shift_below r hr p i α y (by omega),shift_below r hr p i α y hlt,map_zero,map_zero,add_zero]


theorem shift_eq_term (p a : ℕ) (ha : a≤p) (x y : Seq (BorelAbsolute.ofSpace X r hr)) (k : ℕ) :
    shift r hr a (p-a) (x a) y k=term r p k a x y := by
  change (if h : a≤k then _ else 0)=(if h : a≤k ∧ a≤p then _ else 0)
  by_cases hk : a≤k
  · rw [dite_eq_left hk,dite_eq_left ⟨hk,ha⟩]
    exact (cast_absolute r hr _ _).symm
  · rw [dite_eq_right hk,dite_eq_right (by omega)]

/-- Rewrite the convolution as a finite sum of elementary twisted shifts. -/
theorem totalCup_eq_sum_shift (p : ℕ) (x y : Seq (BorelAbsolute.ofSpace X r hr)) :
    totalCup r p x y=∑ a ∈ Finset.range (p+1), shift r hr a (p-a) (x a) y := by
  funext k
  simp only [Finset.sum_apply]
  have he : (∑ a ∈ Finset.range (p+1),shift r hr a (p-a) (x a) y k)=
      ∑ a ∈ Finset.range (p+1),term r p k a x y := by
    apply Finset.sum_congr rfl
    intro a ha
    exact shift_eq_term r hr p a (by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp ha))) x y k
  rw [he]
  change (∑ a ∈ Finset.range (k+1),term r p k a x y)=∑ a ∈ Finset.range (p+1),term r p k a x y
  by_cases hp : p≤k
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro a ha hna
    have hap : ¬a≤p := by simpa using hna
    unfold term
    rw [dite_eq_right (by omega)]
  · apply Finset.sum_subset (Finset.range_mono (by omega))
    intro a ha hna
    have hak : ¬a≤k := by simpa using hna
    unfold term
    rw [dite_eq_right (by omega)]


def convolution (p : ℕ) (x y : Seq (BorelAbsolute.ofSpace X r hr)) : Seq (BorelAbsolute.ofSpace X r hr) :=
  totalCup r p x y

/-- Differentiate the full finite convolution into its three explicit summands. -/
theorem totalCup_D_decomposition (p : ℕ) (x y : Seq (BorelAbsolute.ofSpace X r hr)) :
    D (BorelAbsolute.ofSpace X r hr) (totalCup r p x y)=
      (∑ a ∈ Finset.range (p+1),shift r hr a (p-a+1) (norm r a (x a)) y)+
      (∑ a ∈ Finset.range (p+1),shift r hr (a+1) (p-a) (cochainCoboundary (ZMod 2) X a (x a)) y)+
      convolution r hr p x (D (BorelAbsolute.ofSpace X r hr) y) := by
  unfold convolution
  rw [totalCup_eq_sum_shift,map_sum]
  simp only [shift_D,Finset.sum_add_distrib]
  rw [totalCup_eq_sum_shift]


theorem shift_zero_left (p i : ℕ) (y : Seq (BorelAbsolute.ofSpace X r hr)) : shift r hr p i 0 y=0 := by
  funext k
  change (if h : p≤k then _ else 0)=0
  split_ifs <;> simp only [cochainCup_zero_left,map_zero]

theorem shift_add_left (p i : ℕ) (α β : singularCochainGroup (ZMod 2) X p)
    (y : Seq (BorelAbsolute.ofSpace X r hr)) :
    shift r hr p i (α+β) y=shift r hr p i α y+shift r hr p i β y := by
  funext k
  simp only [Pi.add_apply]
  change (if h : p≤k then _ else 0)=(if h : p≤k then _ else 0)+(if h : p≤k then _ else 0)
  split_ifs <;> simp only [cochainCup_add_left,map_add,add_zero]

theorem norm_top_zero (p : ℕ) (x : Seq (BorelAbsolute.ofSpace X r hr))
    (hx : x ∈ low (BorelAbsolute.ofSpace X r hr) (p+1)) : norm r (p+1) (x (p+1))=0 := by
  rw [hx (p+1) le_rfl]
  change 0+cochainPullback r (p+1) 0=0
  have hz : cochainPullback r (p+1) (0 : singularCochainGroup (ZMod 2) X (p+1))=0 :=
    map_zero ((singularCochainComplexZMod2.map r.op).f (p+1)).hom
  rw [hz,add_zero]


/-- Identify the first two differentiated sums with convolution by the actual D x. -/
theorem convolution_D_left (p : ℕ) (x y : Seq (BorelAbsolute.ofSpace X r hr))
    (hx : x ∈ low (BorelAbsolute.ofSpace X r hr) (p+1)) :
    convolution r hr (p+1) (D (BorelAbsolute.ofSpace X r hr) x) y=
      (∑ a ∈ Finset.range (p+1),shift r hr a (p-a+1) (norm r a (x a)) y)+
      (∑ a ∈ Finset.range (p+1),shift r hr (a+1) (p-a) (cochainCoboundary (ZMod 2) X a (x a)) y) := by
  let H : ℕ → Seq (BorelAbsolute.ofSpace X r hr) := fun a => shift r hr a (p+1-a) (norm r a (x a)) y
  let V : ℕ → Seq (BorelAbsolute.ofSpace X r hr) := fun a => shift r hr (a+1) (p-a) (cochainCoboundary (ZMod 2) X a (x a)) y
  have h0 : shift r hr 0 (p+1-0) (D (BorelAbsolute.ofSpace X r hr) x 0) y=H 0 := rfl
  have hs : ∀ a, shift r hr (a+1) (p+1-(a+1)) (D (BorelAbsolute.ofSpace X r hr) x (a+1)) y=V a+H (a+1) := by
    intro a
    have hd : D (BorelAbsolute.ofSpace X r hr) x (a+1)=
        cochainCoboundary (ZMod 2) X a (x a)+norm r (a+1) (x (a+1)) := rfl
    rw [hd,shift_add_left]
    simp only [H,V,show p+1-(a+1)=p-a by omega]
  have ht : H (p+1)=0 := by
    dsimp only [H]
    rw [norm_top_zero r hr p x hx,shift_zero_left]
  have hh : (∑ a ∈ Finset.range (p+1),H (a+1))+H 0=∑ a ∈ Finset.range (p+1),H a := by
    rw [←Finset.sum_range_succ',Finset.sum_range_succ,ht,add_zero]
  have he : (∑ a ∈ Finset.range (p+1),H a)=
      ∑ a ∈ Finset.range (p+1),shift r hr a (p-a+1) (norm r a (x a)) y := by
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a≤p := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    simp only [H,show p+1-a=p-a+1 by omega]
  unfold convolution
  rw [totalCup_eq_sum_shift,Finset.sum_range_succ']
  simp_rw [hs]
  rw [Finset.sum_add_distrib,h0]
  calc
    _ = (∑ a ∈ Finset.range (p+1),V a)+((∑ a ∈ Finset.range (p+1),H (a+1))+H 0) := add_assoc _ _ _
    _ = (∑ a ∈ Finset.range (p+1),V a)+(∑ a ∈ Finset.range (p+1),H a) := by rw [hh]
    _ = (∑ a ∈ Finset.range (p+1),H a)+(∑ a ∈ Finset.range (p+1),V a) := add_comm _ _
    _ = _ := by rw [he]

/-- The general two-input total Leibniz law, with the necessary left finite-support hypothesis. -/
theorem convolution_D (p : ℕ) (x y : Seq (BorelAbsolute.ofSpace X r hr))
    (hx : x ∈ low (BorelAbsolute.ofSpace X r hr) (p+1)) :
    D (BorelAbsolute.ofSpace X r hr) (convolution r hr p x y)=
      convolution r hr (p+1) (D (BorelAbsolute.ofSpace X r hr) x) y+
      convolution r hr p x (D (BorelAbsolute.ofSpace X r hr) y) := by
  change D (BorelAbsolute.ofSpace X r hr) (totalCup r p x y)=_
  rw [totalCup_D_decomposition,convolution_D_left r hr p x y hx]

end
end Finsler.BorelTwistedDifferential
