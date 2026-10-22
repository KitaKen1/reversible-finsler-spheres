module
public import Finsler.Topology.BorelCanonicalEvaluation
/-! Positive-degree cohomology of the actual punctured sphere vanishes by the pinned Tau Ceti contractibility calculation and the actual Kronecker isomorphism. A map avoiding that point has zero top-class pullback and ordinary cup action. Target composition of a strictly invariant map is proved on the actual relative reflection Borel action; this gives vanishing of the Borel action itself when evaluation avoids a point. Selecting such a point for a finite family of geodesic images remains a separate geometric obligation. -/

@[expose] public section
namespace Finsler.SpherePuncturedEvaluation
open CategoryTheory SphereOddDegree Finsler.BorelEvaluation Finsler.SphereTopClass
open Finsler.BorelCochain Finsler.BorelPair
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The actual sphere with one point removed. -/
def punctured (n : ℕ) (p : Finsler.SphereGeometry.Sphere n) : TopCat.{0} := TopCat.of ({p}ᶜ : Set (Finsler.SphereGeometry.Sphere n))
def inclusion (n : ℕ) (p : Finsler.SphereGeometry.Sphere n) : punctured n p ⟶ sphere n :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

theorem homology_isZero (n : ℕ) (p : Finsler.SphereGeometry.Sphere n) (k : ℕ) (hk : 1≤k) :
    CategoryTheory.Limits.IsZero (homologyZMod2 (punctured n p) k) := by
  cases k with
  | zero => omega
  | succ j =>
    exact (TauCeti.isZero_reducedSingularHomologyFunctor_sphere_compl_singleton
      (ModuleCat.of (ZMod 2) (ZMod 2)) p (j+1)).of_iso
      ((TauCeti.reducedSingularHomologySuccIso (ModuleCat.of (ZMod 2) (ZMod 2)) j).app (punctured n p)).symm

theorem cohomology_eq_zero (n : ℕ) (p : Finsler.SphereGeometry.Sphere n) (k : ℕ) (hk : 1≤k)
    (a : cohomologyZMod2 (punctured n p) k) : a=0 := by
  let : Subsingleton (homologyZMod2 (punctured n p) k) := ModuleCat.subsingleton_of_isZero (homology_isZero n p k hk)
  apply (kroneckerEquiv (punctured n p) k).toLinearEquiv.injective
  ext z
  have hz : z=0 := Subsingleton.elim _ _
  rw [hz,map_zero,map_zero]

theorem pullback_topClass_zero (n : ℕ) (hn : 1≤n) (p : Finsler.SphereGeometry.Sphere n) :
    (cohPullback (inclusion n p) n).hom (topClass n hn)=0 := cohomology_eq_zero n p n hn _

def avoidingMap {X : TopCat.{0}} (n : ℕ) (p : Finsler.SphereGeometry.Sphere n) (f : X ⟶ sphere n)
    (hf : ∀ x, f x≠p) : X ⟶ punctured n p :=
  TopCat.ofHom ⟨fun x => ⟨f x,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hf x⟩,
    f.hom.continuous.subtype_mk _⟩

theorem avoidingMap_include {X : TopCat.{0}} (n : ℕ) (p : Finsler.SphereGeometry.Sphere n)
    (f : X ⟶ sphere n) (hf : ∀ x, f x≠p) : avoidingMap n p f hf ≫ inclusion n p=f := by
  ext x
  rfl

theorem evaluation_topClass_zero {X : TopCat.{0}} (n : ℕ) (hn : 1≤n) (p : Finsler.SphereGeometry.Sphere n)
    (f : X ⟶ sphere n) (hf : ∀ x, f x≠p) : (cohPullback f n).hom (topClass n hn)=0 := by
  rw [←avoidingMap_include n p f hf,Cup.pullback_comp,pullback_topClass_zero,map_zero]

theorem evaluation_cup_zero {X : TopCat.{0}} (n : ℕ) (hn : 1≤n) (p : Finsler.SphereGeometry.Sphere n)
    (f : X ⟶ sphere n) (hf : ∀ x, f x≠p) (q : ℕ) (b : cohomologyZMod2 X q) :
    cupZMod2 ((cohPullback f n).hom (topClass n hn)) b=0 := by
  rw [evaluation_topClass_zero n hn p f hf,Cup.zero_cup]

variable (P : TopPair.{0}) (r : P ⟶ P) (hr : r≫r=𝟙 P)
variable {X Y : TopCat.{0}} (f : P.fst ⟶ X) (hf : TopPair.Hom.fst r≫f=f) (g : X ⟶ Y)

include hf in
theorem invariant_comp : TopPair.Hom.fst r≫(f≫g)=f≫g := by
  rw [←Category.assoc,hf]

theorem cochainCup_comp (p : ℕ) (α : singularCochainGroup (ZMod 2) Y p)
    (hα : cochainCoboundary (ZMod 2) Y p α=0) (q : ℕ) :
    BorelPullbackCup.cochainCup P r hr (f≫g) (invariant_comp P r f hf g) p α hα q=
      BorelPullbackCup.cochainCup P r hr f hf p (cochainPullback g p α) (cochainPullback_cocycle g p α hα) q := by
  unfold BorelPullbackCup.cochainCup
  apply BorelPullbackCup.invariantCup_congr
  exact (BorelEvaluation.cochain_comp f g p α).symm

theorem classAction_comp (p : ℕ) (s : cohomologyZMod2 Y p) (q : ℕ) :
    (BorelPullbackCup.classAction P r hr (f≫g) (invariant_comp P r f hf g) p q).hom s=
      (BorelPullbackCup.classAction P r hr f hf p q).hom ((cohPullback g p).hom s) := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Y p s
  rw [cohPullback_cocycleClass]
  change (BorelPullbackCup.classAction P r hr (f≫g) _ p q).hom
    (CochainClass.classOf (cochainCxZMod2 Y) p α hα)=
    (BorelPullbackCup.classAction P r hr f hf p q).hom
      (CochainClass.classOf (cochainCxZMod2 X) p (cochainPullback g p α) (cochainPullback_cocycle g p α hα))
  rw [BorelPullbackCup.classAction_mk,BorelPullbackCup.classAction_mk]
  exact cochainCup_comp P r hr f hf g p α hα q

theorem classAction_zero_of_factorization (p : ℕ) (s : cohomologyZMod2 Y p)
    (hs : (cohPullback g p).hom s=0) (q : ℕ) :
    (BorelPullbackCup.classAction P r hr (f≫g) (invariant_comp P r f hf g) p q).hom s=0 := by
  rw [classAction_comp P r hr f hf g p s q,hs,map_zero]


theorem classAction_congr_map {Z : TopCat.{0}} (f₁ f₂ : P.fst ⟶ Z)
    (hf₁ : TopPair.Hom.fst r≫f₁=f₁) (hf₂ : TopPair.Hom.fst r≫f₂=f₂) (he : f₁=f₂) (p q : ℕ) :
    BorelPullbackCup.classAction P r hr f₁ hf₁ p q=BorelPullbackCup.classAction P r hr f₂ hf₂ p q := by
  subst f₂
  rfl

/-- Avoiding one point kills the actual relative reflection evaluation action, not only its ordinary image. -/
theorem classAction_topClass_zero_of_avoids (n : ℕ) (hn : 1≤n) (p : Finsler.SphereGeometry.Sphere n)
    (e : P.fst ⟶ sphere n) (he : TopPair.Hom.fst r≫e=e) (hp : ∀ x, e x≠p) (q : ℕ) :
    (BorelPullbackCup.classAction P r hr e he n q).hom (topClass n hn)=0 := by
  let ep := avoidingMap n p e hp
  have hep : TopPair.Hom.fst r≫ep=ep := by
    ext x : 1
    apply Subtype.ext
    exact congrArg (fun φ => φ x) he
  have hzero := classAction_zero_of_factorization P r hr ep hep (inclusion n p) n (topClass n hn)
    (pullback_topClass_zero n hn p) q
  have heq : ep≫inclusion n p=e := avoidingMap_include n p e hp
  rw [classAction_congr_map P r hr (ep≫inclusion n p) e (invariant_comp P r ep hep (inclusion n p)) he heq n q] at hzero
  exact hzero

end
end Finsler.SpherePuncturedEvaluation
