module
public import Finsler.Topology.BorelTotalCup
/-! Arbitrary elementary twisted shifts compose according to the actual Alexander–Whitney cup associativity and addition of pullback powers, with no closed or invariant assumption. Supported left and middle sequences decompose into finite sums of dependent singles. Bilinearity reduces full convolution associativity to pairs of singles; the third cochain sequence needs no support hypothesis. Actual quotient surjectivity and degree transport prove graded associativity for arbitrary absolute reflection Borel classes. Together with v0.77 this supplies the bilinear native product, both units, associativity, equivariant naturality, ordinary forgetting and the old w comparison. No graded-commutativity, geometric Borel comparison or unconditional MAIN is claimed here. -/

@[expose] public section
namespace Finsler.BorelTotalAssociativity
open CategoryTheory SphereOddDegree BorelCochain BorelTwistedCup BorelTwistedDifferential
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : TopCat.{0}} (r : X ⟶ X) (hr : r≫r=𝟙 X)

theorem act_add (i j k : ℕ) (α : singularCochainGroup (ZMod 2) X k) :
    act r (i+j) k α=act r i k (act r j k α) := by
  unfold act
  rw [pow_add,Module.End.mul_apply]

/-- Composition of arbitrary twisted shifts, with no cocycle or invariance assumption. -/
theorem shift_comp (p s i j : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (β : singularCochainGroup (ZMod 2) X s) (c : Seq (BorelAbsolute.ofSpace X r hr)) :
    shift r hr (p+s) (i+j) (cochainCup p s α (act r i s β)) c=
      shift r hr p i α (shift r hr s j β c) := by
  funext l
  by_cases hl : p+s≤l
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hl
    apply BorelAbsoluteCup.castC_injective (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p s k)
    have he : BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p s k)
        (cochainCup (p+s) k (cochainCup p s α (act r i s β)) (act r (i+j) k (c k)))=
        cochainCup p (s+k) α (act r i (s+k) (cochainCup s k β (act r j k (c k)))) := by
      rw [←cast_absolute r hr,act_cup,act_add]
      exact CupAssociativity.cochain_assoc X p s k _ _ _
    calc
      _ = BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p s k)
          (cochainCup (p+s) k (cochainCup p s α (act r i s β)) (act r (i+j) k (c k))) :=
        congrArg (BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p s k)) (shift_at r hr (p+s) (i+j) _ c k)
      _ = _ := he
      _ = shift r hr p i α (shift r hr s j β c) (p+(s+k)) := by rw [shift_at,shift_at]
      _ = BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p s k)
          (shift r hr p i α (shift r hr s j β c) ((p+s)+k)) := BorelGraded.cast_seq _ _
  · rw [shift_below r hr (p+s) (i+j) _ c (by omega)]
    by_cases hp : p≤l
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hp
      rw [shift_at,shift_below r hr s j β c (by omega),map_zero,cochainCup_zero_right]
    · rw [shift_below r hr p i α _ (by omega)]

/-- A supported left single contributes exactly one elementary twisted shift. -/
theorem convolution_single_left (P a : ℕ) (ha : a≤P)
    (α : singularCochainGroup (ZMod 2) X a) (y : Seq (BorelAbsolute.ofSpace X r hr)) :
    convolution r hr P (Pi.single a α) y=shift r hr a (P-a) α y := by
  rw [convolution,totalCup_eq_sum_shift]
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b hb hba
    rw [single_ne (BorelAbsolute.ofSpace X r hr) hba,shift_zero_left]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

/-- Arbitrary elementary shifts multiply supported single cochains by the actual twisted cup. -/
theorem shift_single (a b i : ℕ) (α : singularCochainGroup (ZMod 2) X a)
    (β : singularCochainGroup (ZMod 2) X b) :
    shift r hr a i α (Pi.single b β)=Pi.single (a+b) (cochainCup a b α (act r i b β)) := by
  funext k
  by_cases he : k=a+b
  · subst k
    rw [shift_at,Pi.single_eq_same,Pi.single_eq_same]
  · by_cases ha : a≤k
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le ha
      have hj : j≠b := by omega
      rw [shift_at,single_ne (BorelAbsolute.ofSpace X r hr) hj,map_zero,cochainCup_zero_right,
        single_ne (BorelAbsolute.ofSpace X r hr) he]
    · rw [shift_below r hr a i α _ (by omega),single_ne (BorelAbsolute.ofSpace X r hr) he]

theorem convolution_single_single (P a b : ℕ) (ha : a≤P)
    (α : singularCochainGroup (ZMod 2) X a) (β : singularCochainGroup (ZMod 2) X b) :
    convolution r hr P (Pi.single a α) (Pi.single b β)=
      Pi.single (a+b) (cochainCup a b α (act r (P-a) b β)) := by
  rw [convolution_single_left r hr P a ha,shift_single]

theorem convolution_assoc_single (P Q a b : ℕ) (ha : a≤P) (hb : b≤Q)
    (α : singularCochainGroup (ZMod 2) X a) (β : singularCochainGroup (ZMod 2) X b)
    (z : Seq (BorelAbsolute.ofSpace X r hr)) :
    convolution r hr (P+Q) (convolution r hr P (Pi.single a α) (Pi.single b β)) z=
      convolution r hr P (Pi.single a α) (convolution r hr Q (Pi.single b β) z) := by
  rw [convolution_single_single r hr P a b ha,
    convolution_single_left r hr (P+Q) (a+b) (by omega),
    convolution_single_left r hr P a ha,convolution_single_left r hr Q b hb]
  rw [show P+Q-(a+b)=(P-a)+(Q-b) by omega]
  exact shift_comp r hr a b (P-a) (Q-b) α β z

/-- Finite-support sequences decompose into their actual dependent single components. -/
theorem seq_sum_singles (P : ℕ) (x : Seq (BorelAbsolute.ofSpace X r hr))
    (hx : x ∈ low (BorelAbsolute.ofSpace X r hr) (P+1)) :
    x=∑ a ∈ Finset.range (P+1), (Pi.single a (x a) : Seq (BorelAbsolute.ofSpace X r hr)) := by
  funext k
  rw [Finset.sum_apply]
  by_cases hk : k≤P
  · rw [Finset.sum_eq_single k]
    · exact (Pi.single_eq_same k (x k)).symm
    · intro a ha hak
      exact single_ne (BorelAbsolute.ofSpace X r hr) (Ne.symm hak) (x a)
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · rw [hx k (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    exact single_ne (BorelAbsolute.ofSpace X r hr) (by have ha' := Finset.mem_range.mp ha;omega) (x a)

/-- The typed sequence wrapper keeps the actual Borel module instances during finite summation. -/
def convolutionPairing (P : ℕ) : Seq (BorelAbsolute.ofSpace X r hr) →ₗ[ZMod 2]
    Seq (BorelAbsolute.ofSpace X r hr) →ₗ[ZMod 2] Seq (BorelAbsolute.ofSpace X r hr) where
  toFun x := {
    toFun := convolution r hr P x
    map_add' y z := totalCup_add_right r P x y z
    map_smul' a y := totalCup_smul_right r P a x y }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    exact totalCup_add_left r P x z y
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    exact totalCup_smul_left r P a x y

theorem convolution_sum_left (P : ℕ) (s : Finset ℕ)
    (f : ℕ → Seq (BorelAbsolute.ofSpace X r hr)) (y : Seq (BorelAbsolute.ofSpace X r hr)) :
    convolution r hr P (∑ a ∈ s,f a) y=∑ a ∈ s,convolution r hr P (f a) y := by
  have he := congrArg (fun A => A y) (map_sum (convolutionPairing r hr P) f s)
  simp only [LinearMap.sum_apply] at he
  exact he

theorem convolution_sum_right (P : ℕ) (s : Finset ℕ)
    (x : Seq (BorelAbsolute.ofSpace X r hr)) (f : ℕ → Seq (BorelAbsolute.ofSpace X r hr)) :
    convolution r hr P x (∑ a ∈ s,f a)=∑ a ∈ s,convolution r hr P x (f a) := by
  exact map_sum (convolutionPairing r hr P x) f s

/-- Full cochain associativity from finite singles and arbitrary shift composition. -/
theorem convolution_assoc (P Q : ℕ) (x y z : Seq (BorelAbsolute.ofSpace X r hr))
    (hx : x ∈ low (BorelAbsolute.ofSpace X r hr) (P+1))
    (hy : y ∈ low (BorelAbsolute.ofSpace X r hr) (Q+1)) :
    convolution r hr (P+Q) (convolution r hr P x y) z=
      convolution r hr P x (convolution r hr Q y z) := by
  rw [seq_sum_singles r hr P x hx,seq_sum_singles r hr Q y hy]
  simp only [convolution_sum_left,convolution_sum_right]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  exact convolution_assoc_single r hr P Q a b (by have h := Finset.mem_range.mp ha;omega)
    (by have h := Finset.mem_range.mp hb;omega) (x a) (y b) z

/-- Graded associativity for arbitrary absolute reflection Borel classes. -/
theorem cup_assoc (P Q S : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) P)
    (y : HR (BorelAbsolute.ofSpace X r hr) Q) (z : HR (BorelAbsolute.ofSpace X r hr) S) :
    BorelGraded.castHR (Nat.add_assoc P Q S)
      (BorelTotalCup.cup r hr (P+Q) S (BorelTotalCup.cup r hr P Q x y) z)=
      BorelTotalCup.cup r hr P (Q+S) x (BorelTotalCup.cup r hr Q S y z) := by
  obtain ⟨a,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b,rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [BorelTotalCup.cup_mk,BorelTotalCup.cup_mk,BorelTotalCup.cup_mk,BorelTotalCup.cup_mk]
  have ht := convolution_assoc r hr P Q a.val b.val c.val ((mem_bcocycles _).mp a.2).1 ((mem_bcocycles _).mp b.2).1
  have hc : convolution r hr (P+Q) (convolution r hr P a.val b.val) c.val ∈ bcocycles (BorelAbsolute.ofSpace X r hr) (P+(Q+S)) := by
    rw [ht]
    exact (BorelTotalCup.cyclePairing r hr P (Q+S) a (BorelTotalCup.cyclePairing r hr Q S b c)).2
  calc
    _ = Submodule.Quotient.mk (⟨_,hc⟩ : bcocycles (BorelAbsolute.ofSpace X r hr) (P+(Q+S))) := BorelGraded.castHR_mk _ _ _ _
    _ = _ := congrArg Submodule.Quotient.mk (Subtype.ext ht)

end
end Finsler.BorelTotalAssociativity
