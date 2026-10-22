module

public import Finsler.Topology.NestedCapHomology

/-! Compose the actual closed degree-lowering operations, retaining
the explicit associativity transport on chains and homology. -/

@[expose] public section
namespace Finsler.DegreeLoweringComposition

open CategoryTheory CategoryTheory.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 500000

variable {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {a b : ℕ}
  (f : DegreeLoweringHomology.Map C D a) (g : DegreeLoweringHomology.Map D E b)

def compose : DegreeLoweringHomology.Map C E (a + b) :=
  NestedCapHomology.operation a b (fun q => f.component (b + q) ≫ g.component q) (by
    intro q
    have hf : f.component (b + (q + 1)) ≫ D.d (b + (q + 1)) (b + q) =
        C.d (a + (b + (q + 1))) (a + (b + q)) ≫ f.component (b + q) := by
      rw [← Nat.add_assoc b q 1]
      exact f.comm (b + q)
    rw [Category.assoc, g.comm, ← Category.assoc, hf, Category.assoc])

theorem component (q : ℕ) :
    (compose f g).component q = eqToHom (congrArg C.X (Nat.add_assoc a b q)) ≫
      f.component (b + q) ≫ g.component q := rfl

private theorem transport_iCycles (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (i j : ℕ) (h : i = j) :
    eqToHom (congrArg (fun k : ℕ => K.cycles k) h) ≫ K.iCycles j = K.iCycles i ≫ eqToHom (congrArg K.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem transport_homologyπ (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (i j : ℕ) (h : i = j) :
    K.homologyπ i ≫ eqToHom (congrArg (fun k : ℕ => K.homology k) h) =
      eqToHom (congrArg (fun k : ℕ => K.cycles k) h) ≫ K.homologyπ j := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem cycles (q : ℕ) :
    (compose f g).cycles q = eqToHom (congrArg (fun k : ℕ => C.cycles k) (Nat.add_assoc a b q)) ≫
      f.cycles (b + q) ≫ g.cycles q := by
  apply (cancel_mono (E.iCycles q)).mp
  rw [DegreeLoweringHomology.Map.cycles_i, component]
  let eX := eqToHom (congrArg C.X (Nat.add_assoc a b q))
  let eC := eqToHom (congrArg (fun k : ℕ => C.cycles k) (Nat.add_assoc a b q))
  have ht : eC ≫ C.iCycles (a + (b + q)) = C.iCycles ((a + b) + q) ≫ eX :=
    transport_iCycles C ((a + b) + q) (a + (b + q)) (Nat.add_assoc a b q)
  change C.iCycles ((a + b) + q) ≫ (eX ≫ f.component (b + q) ≫ g.component q) =
    (eC ≫ f.cycles (b + q) ≫ g.cycles q) ≫ E.iCycles q
  calc
    _ = (C.iCycles ((a + b) + q) ≫ eX) ≫ f.component (b + q) ≫ g.component q := by
      simp only [Category.assoc]
    _ = (eC ≫ C.iCycles (a + (b + q))) ≫ f.component (b + q) ≫ g.component q := by rw [← ht]
    _ = eC ≫ (C.iCycles (a + (b + q)) ≫ f.component (b + q)) ≫ g.component q := by
      simp only [Category.assoc]
    _ = eC ≫ (f.cycles (b + q) ≫ D.iCycles (b + q)) ≫ g.component q := by rw [← f.cycles_i]
    _ = (eC ≫ f.cycles (b + q)) ≫ (D.iCycles (b + q) ≫ g.component q) := by
      simp only [Category.assoc]
    _ = (eC ≫ f.cycles (b + q)) ≫ (g.cycles q ≫ E.iCycles q) := by rw [← g.cycles_i]
    _ = _ := by simp only [Category.assoc]

theorem homology (q : ℕ) :
    (compose f g).homology q = eqToHom (congrArg (fun k : ℕ => C.homology k) (Nat.add_assoc a b q)) ≫
      f.homology (b + q) ≫ g.homology q := by
  apply (cancel_epi (C.homologyπ ((a + b) + q))).mp
  rw [DegreeLoweringHomology.Map.homologyπ_homology, cycles]
  calc
    (eqToHom (congrArg (fun k : ℕ => C.cycles k) (Nat.add_assoc a b q)) ≫
        f.cycles (b + q) ≫ g.cycles q) ≫ E.homologyπ q =
      eqToHom (congrArg (fun k : ℕ => C.cycles k) (Nat.add_assoc a b q)) ≫
        f.cycles (b + q) ≫ (D.homologyπ (b + q) ≫ g.homology q) := by
          rw [Category.assoc, Category.assoc, g.homologyπ_homology]
    _ = (eqToHom (congrArg (fun k : ℕ => C.cycles k) (Nat.add_assoc a b q)) ≫ C.homologyπ (a + (b + q))) ≫
        f.homology (b + q) ≫ g.homology q := by
          rw [← Category.assoc (f.cycles (b + q)), ← f.homologyπ_homology]
          simp only [Category.assoc]
    _ = C.homologyπ ((a + b) + q) ≫
        eqToHom (congrArg (fun k : ℕ => C.homology k) (Nat.add_assoc a b q)) ≫
          f.homology (b + q) ≫ g.homology q := by
          rw [← transport_homologyπ C ((a + b) + q) (a + (b + q)) (Nat.add_assoc a b q)]
          simp only [Category.assoc]

end
end Finsler.DegreeLoweringComposition
