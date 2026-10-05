import Mathlib.Order.BooleanSubalgebra
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

/-! Cardinal bounds for the actual generated subalgebra of any Boolean
algebra, in arbitrary universes. Finite generation gives a finite algebra;
infinite generation increases cardinality by at most a countable factor. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon
universe u
variable {B : Type u} [BooleanAlgebra B]

theorem booleanSubalgebraClosure_subset_latticeClosure (C : Set B) :
    (BooleanSubalgebra.closure C : Set B) ⊆
      latticeClosure (insert ⊥ (insert ⊤ (C ∪ (fun a : B => aᶜ) '' C))) := by
  let D := insert (⊥ : B) (insert ⊤ (C ∪ (fun a : B => aᶜ) '' C))
  have hDc : ∀ a ∈ D, aᶜ ∈ D := by
    intro a ha
    rcases ha with rfl | rfl | ha | ⟨b, hb, rfl⟩
    · simp [D]
    · simp [D]
    · exact Or.inr (Or.inr (Or.inr ⟨a, ha, rfl⟩))
    · simpa only [compl_compl] using
        (Or.inr (Or.inr (Or.inl hb)) : b ∈ D)
  have hc : ∀ a ∈ latticeClosure D, aᶜ ∈ latticeClosure D := by
    intro a ha
    induction ha using latticeClosure_sup_inf_induction with
    | mem a ha => exact subset_latticeClosure (hDc a ha)
    | sup a ha b hb iha ihb =>
      simpa only [compl_sup] using isSublattice_latticeClosure.infClosed iha ihb
    | inf a ha b hb iha ihb =>
      simpa only [compl_inf] using isSublattice_latticeClosure.supClosed iha ihb
  let L : BooleanSubalgebra B :=
    { carrier := latticeClosure D
      supClosed' := isSublattice_latticeClosure.supClosed
      infClosed' := isSublattice_latticeClosure.infClosed
      compl_mem' := hc _
      bot_mem' := subset_latticeClosure (by simp [D]) }
  exact (BooleanSubalgebra.closure_le (L := L)).mpr
    (fun a ha => subset_latticeClosure (Or.inr (Or.inr (Or.inl ha))))

theorem finite_booleanSubalgebraClosure {C : Set B} (hC : C.Finite) :
    (BooleanSubalgebra.closure C : Set B).Finite := by
  exact ((hC.union (hC.image (fun a : B => aᶜ))).insert ⊤ |>.insert ⊥).latticeClosure.subset
    (booleanSubalgebraClosure_subset_latticeClosure C)

theorem cardinal_booleanSubalgebraClosure_lt_aleph0 {C : Set B} (hC : C.Finite) :
    #(BooleanSubalgebra.closure C) < ℵ₀ :=
  Cardinal.lt_aleph0_iff_set_finite.mpr (finite_booleanSubalgebraClosure hC)

def booleanSubalgebraDepth (C : Set B) : ℕ → Set B
  | 0 => insert ⊥ C
  | n+1 => booleanSubalgebraDepth C n ∪ (fun a : B => aᶜ) '' booleanSubalgebraDepth C n ∪
      (fun p : B × B => p.1 ⊔ p.2) '' (booleanSubalgebraDepth C n ×ˢ booleanSubalgebraDepth C n)

theorem booleanSubalgebraDepth_mono (C : Set B) : Monotone (booleanSubalgebraDepth C) := by
  apply monotone_nat_of_le_succ
  intro n a ha
  exact Or.inl (Or.inl ha)

theorem booleanSubalgebraClosure_subset_depths (C : Set B) :
    (BooleanSubalgebra.closure C : Set B) ⊆ ⋃ n, booleanSubalgebraDepth C n := by
  intro a ha
  induction ha using BooleanSubalgebra.closure_bot_sup_induction with
  | mem a ha => exact Set.mem_iUnion.mpr ⟨0, Or.inr ha⟩
  | bot => exact Set.mem_iUnion.mpr ⟨0, Or.inl rfl⟩
  | sup a ha b hb iha ihb =>
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp iha
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ihb
    exact Set.mem_iUnion.mpr ⟨max n m + 1, Or.inr ⟨(a,b),
      ⟨booleanSubalgebraDepth_mono C (le_max_left _ _) hn,
        booleanSubalgebraDepth_mono C (le_max_right _ _) hm⟩, rfl⟩⟩
  | compl a ha ih =>
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ih
    exact Set.mem_iUnion.mpr ⟨n+1, Or.inl (Or.inr ⟨a, hn, rfl⟩)⟩

theorem cardinal_booleanSubalgebraClosure_le (C : Set B)
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hC : #C ≤ κ) :
    #(BooleanSubalgebra.closure C) ≤ κ := by
  have hsum : κ + κ = κ := Cardinal.add_eq_self hκ
  have hprod : κ * κ = κ := Cardinal.mul_eq_self hκ
  have hd (n : ℕ) : #(booleanSubalgebraDepth C n) ≤ κ := by
    induction n with
    | zero =>
      change #(insert (⊥ : B) C : Set B) ≤ κ
      calc
        _ ≤ #({⊥} : Set B) + #C := by
          simpa only [Set.singleton_union] using Cardinal.mk_union_le {⊥} C
        _ ≤ κ + κ := add_le_add (by simpa using Cardinal.one_le_aleph0.trans hκ) hC
        _ = κ := hsum
    | succ n ih =>
      have hc : #((fun a : B => aᶜ) '' booleanSubalgebraDepth C n) ≤ κ :=
        Cardinal.mk_image_le.trans ih
      have hu : #((fun p : B × B => p.1 ⊔ p.2) ''
          (booleanSubalgebraDepth C n ×ˢ booleanSubalgebraDepth C n)) ≤ κ := by
        exact Cardinal.mk_image_le.trans (by
          rw [Cardinal.mk_setProd]
          exact (mul_le_mul' ih ih).trans_eq hprod)
      exact (Cardinal.mk_union_le _ _).trans ((add_le_add
        ((Cardinal.mk_union_le _ _).trans ((add_le_add ih hc).trans_eq hsum)) hu).trans_eq hsum)
  calc
    _ ≤ #(⋃ n, booleanSubalgebraDepth C n) :=
      Cardinal.mk_le_mk_of_subset (booleanSubalgebraClosure_subset_depths C)
    _ ≤ Cardinal.lift.{u} #ℕ * ⨆ n, #(booleanSubalgebraDepth C n) := by
      simpa only [Cardinal.lift_id'.{0, u}] using Cardinal.mk_iUnion_le_lift (booleanSubalgebraDepth C)
    _ ≤ κ * κ := mul_le_mul' (by simpa using hκ) (ciSup_le' hd)
    _ = κ := hprod

theorem cardinal_booleanSubalgebraClosure_le_max (C : Set B) :
    #(BooleanSubalgebra.closure C) ≤ max ℵ₀ #C :=
  cardinal_booleanSubalgebraClosure_le C _ (le_max_left _ _) (le_max_right _ _)

end ThesisCommon
