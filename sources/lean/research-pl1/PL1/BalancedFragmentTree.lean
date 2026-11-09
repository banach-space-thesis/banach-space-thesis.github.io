import PL1.AtomicBandDecomposition
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Balanced binary fragment trees

An actual exact-halving fragment map constructs finite lattice partitions.
The Boolean signs on each common refinement are the usual Rademacher signs.
-/

noncomputable section
open scoped BigOperators Topology

namespace PL1.BalancedFragmentTree

abbrev Word (n : ℕ) := Fin n → Bool

def snocEquiv (n : ℕ) : (Word n × Bool) ≃ Word (n + 1) where
  toFun p := Fin.snoc p.1 p.2
  invFun w := (Fin.init w, w (Fin.last n))
  left_inv p := by simp
  right_inv w := Fin.snoc_init_self w

theorem sum_word_succ {A : Type*} [AddCommMonoid A] (n : ℕ) (f : Word (n + 1) → A) :
    ∑ w, f w = ∑ w : Word n, (f (Fin.snoc w false) + f (Fin.snoc w true)) := by
  rw [← (snocEquiv n).sum_comp, Fintype.sum_prod_type]
  simp only [snocEquiv, Equiv.coe_fn_mk, Fintype.sum_bool, add_comm]

def sign {n : ℕ} (i : Fin n) (w : Word n) : ℝ := if w i then -1 else 1

theorem sign_eq {n : ℕ} (i : Fin n) (w : Word n) : sign i w = 1 ∨ sign i w = -1 := by
  cases h : w i <;> simp [sign, h]

@[simp] theorem abs_sign {n : ℕ} (i : Fin n) (w : Word n) : |sign i w| = 1 := by
  rcases sign_eq i w with h | h <;> simp [h]

@[simp] theorem sign_sq {n : ℕ} (i : Fin n) (w : Word n) : sign i w * sign i w = 1 := by
  rcases sign_eq i w with h | h <;> simp [h]

@[simp] theorem sign_snoc_castSucc {n : ℕ} (i : Fin n) (w : Word n) (b : Bool) :
    sign i.castSucc (Fin.snoc w b) = sign i w := by simp [sign]

@[simp] theorem sign_snoc_last_false {n : ℕ} (w : Word n) :
    sign (Fin.last n) (Fin.snoc w false) = 1 := by simp [sign]

@[simp] theorem sign_snoc_last_true {n : ℕ} (w : Word n) :
    sign (Fin.last n) (Fin.snoc w true) = -1 := by simp [sign]

def flipEquiv {n : ℕ} (i : Fin n) : Word n ≃ Word n where
  toFun w := Function.update w i (!(w i))
  invFun w := Function.update w i (!(w i))
  left_inv w := by ext j; by_cases h : j = i <;> simp [h]
  right_inv w := by ext j; by_cases h : j = i <;> simp [h]

@[simp] theorem sign_flip_self {n : ℕ} (i : Fin n) (w : Word n) :
    sign i (flipEquiv i w) = -sign i w := by
  cases h : w i <;> simp [sign, flipEquiv, h]

theorem sign_flip_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) (w : Word n) :
    sign j (flipEquiv i w) = sign j w := by simp [sign, flipEquiv, h]

/-- Orthogonality is a finite Boolean identity, independent of a measure space. -/
theorem sign_orthogonality {n : ℕ} (i j : Fin n) :
    (∑ w : Word n, sign i w * sign j w) = if i = j then (2 : ℝ) ^ n else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [Word]
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (hij h))]
    have h := (flipEquiv i).sum_comp (fun w => sign i w * sign j w)
    simp only [sign_flip_self, sign_flip_ne (fun h => hij h.symm), neg_mul,
      Finset.sum_neg_distrib] at h
    linarith

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- Exact halving by genuine disjoint fragments throughout `[0,u]`. -/
def IsBalancedSplit (φ : E →L[ℝ] ℝ) (u : E) (split : E → E) : Prop :=
  ∀ x : E, 0 ≤ x → x ≤ u →
    0 ≤ split x ∧ split x ≤ x ∧ IsVLDisjoint (split x) (x - split x) ∧
      φ (split x) = φ x / 2

/-- Actual cells; at each step the final Boolean coordinate chooses the child. -/
def cell (u : E) (split : E → E) : (n : ℕ) → Word n → E
  | 0, _ => u
  | n + 1, w =>
    let x := cell u split n (Fin.init w)
    if w (Fin.last n) then x - split x else split x

omit [Lattice E] [IsOrderedAddMonoid E] [NormedVectorLattice E] in
@[simp] theorem cell_zero (u : E) (split : E → E) (w : Word 0) : cell u split 0 w = u := rfl

omit [Lattice E] [IsOrderedAddMonoid E] [NormedVectorLattice E] in
@[simp] theorem cell_snoc_false (u : E) (split : E → E) {n : ℕ} (w : Word n) :
    cell u split (n + 1) (Fin.snoc w false) = split (cell u split n w) := by simp [cell]

omit [Lattice E] [IsOrderedAddMonoid E] [NormedVectorLattice E] in
@[simp] theorem cell_snoc_true (u : E) (split : E → E) {n : ℕ} (w : Word n) :
    cell u split (n + 1) (Fin.snoc w true) = cell u split n w - split (cell u split n w) := by
  simp [cell]

omit [Lattice E] [IsOrderedAddMonoid E] [NormedVectorLattice E] in
theorem cell_children_add (u : E) (split : E → E) {n : ℕ} (w : Word n) :
    cell u split (n + 1) (Fin.snoc w false) + cell u split (n + 1) (Fin.snoc w true) =
      cell u split n w := by simp

theorem cell_mem_Icc {φ : E →L[ℝ] ℝ} {u : E} {split : E → E}
    (hu : 0 ≤ u) (hs : IsBalancedSplit φ u split) (n : ℕ) (w : Word n) :
    0 ≤ cell u split n w ∧ cell u split n w ≤ u := by
  induction n with
  | zero => exact ⟨hu, le_rfl⟩
  | succ n ih =>
    obtain ⟨hx, hxu⟩ := ih (Fin.init w)
    obtain ⟨hp, hpx, _, _⟩ := hs _ hx hxu
    simp only [cell]
    split
    · exact ⟨sub_nonneg.mpr hpx, (sub_le_self _ hp).trans hxu⟩
    · exact ⟨hp, hpx.trans hxu⟩

theorem cell_child_le {φ : E →L[ℝ] ℝ} {u : E} {split : E → E}
    (hu : 0 ≤ u) (hs : IsBalancedSplit φ u split) {n : ℕ} (w : Word n) (b : Bool) :
    cell u split (n + 1) (Fin.snoc w b) ≤ cell u split n w := by
  have hx := cell_mem_Icc hu hs n w
  have hp := hs _ hx.1 hx.2
  cases b <;> simp only [cell_snoc_false, cell_snoc_true]
  · exact hp.2.1
  · exact sub_le_self _ hp.1

omit [Lattice E] [IsOrderedAddMonoid E] [NormedVectorLattice E] in
theorem sum_cell (u : E) (split : E → E) (n : ℕ) : ∑ w : Word n, cell u split n w = u := by
  induction n with
  | zero => simp [Word]
  | succ n ih => rw [sum_word_succ]; simpa only [cell_children_add] using ih

theorem cell_phi {φ : E →L[ℝ] ℝ} {u : E} {split : E → E}
    (hu : 0 ≤ u) (hs : IsBalancedSplit φ u split) (n : ℕ) (w : Word n) :
    φ (cell u split n w) = φ u / (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx := cell_mem_Icc hu hs n (Fin.init w)
    have hp := (hs _ hx.1 hx.2).2.2.2
    simp only [cell]
    split
    · rw [map_sub, hp, ih]
      rw [pow_succ]
      ring
    · rw [hp, ih, pow_succ]
      ring

theorem cell_pairwise_disjoint {φ : E →L[ℝ] ℝ} {u : E} {split : E → E}
    (hu : 0 ≤ u) (hs : IsBalancedSplit φ u split) (n : ℕ) :
    Pairwise (fun w z : Word n => IsVLDisjoint (cell u split n w) (cell u split n z)) := by
  induction n with
  | zero =>
    intro w z hne
    exact False.elim (hne (Subsingleton.elim w z))
  | succ n ih =>
    have hc (w z : Word n) (b c : Bool)
        (hne : (Fin.snoc w b : Word (n + 1)) ≠ Fin.snoc z c) :
        IsVLDisjoint (cell u split (n + 1) (Fin.snoc w b))
          (cell u split (n + 1) (Fin.snoc z c)) := by
      by_cases hwz : w = z
      · subst z
        have hbc : b ≠ c := fun h => hne (h ▸ rfl)
        have hx := cell_mem_Icc hu hs n w
        have hd := (hs _ hx.1 hx.2).2.2.1
        cases b <;> cases c
        · exact False.elim (hbc rfl)
        · simpa only [cell_snoc_false, cell_snoc_true] using hd
        · simpa only [cell_snoc_false, cell_snoc_true] using isVLDisjoint_comm.mp hd
        · exact False.elim (hbc rfl)
      · apply ((ih hwz).mono_left ?_).mono_right ?_
        · rw [abs_of_nonneg (cell_mem_Icc hu hs _ _).1,
            abs_of_nonneg (cell_mem_Icc hu hs _ _).1]
          exact cell_child_le hu hs w b
        · rw [abs_of_nonneg (cell_mem_Icc hu hs _ _).1,
            abs_of_nonneg (cell_mem_Icc hu hs _ _).1]
          exact cell_child_le hu hs z c
    intro w z hne
    simpa only [Fin.snoc_init_self] using
      hc (Fin.init w) (Fin.init z) (w (Fin.last n)) (z (Fin.last n))
        (by simpa only [Fin.snoc_init_self] using hne)

theorem signed_refinement_one (u : E) (split : E → E) {n : ℕ} (i : Fin n) :
    (∑ w : Word (n + 1), sign i.castSucc w • cell u split (n + 1) w) =
      ∑ w : Word n, sign i w • cell u split n w := by
  rw [sum_word_succ]
  apply Finset.sum_congr rfl
  intro w _
  simp only [sign_snoc_castSucc, ← smul_add, cell_children_add]

/-- The actual lattice Rademacher sequence generated by the fragment tree. -/
def rademacher (u : E) (split : E → E) (n : ℕ) : E :=
  ∑ w : Word (n + 1), sign (Fin.last n) w • cell u split (n + 1) w

/-- All earlier Rademachers admit a simultaneous expansion on any deeper partition. -/
theorem rademacher_refinement (u : E) (split : E → E) {n m : ℕ} (hnm : n < m) :
    rademacher u split n = ∑ w : Word m, sign ⟨n, hnm⟩ w • cell u split m w := by
  induction m with
  | zero => exact False.elim (Nat.not_lt_zero n hnm)
  | succ m ih =>
    by_cases h : n = m
    · subst m
      rfl
    · have hlt : n < m := lt_of_le_of_ne (Nat.le_of_lt_succ hnm) h
      have hidx : (⟨n, hnm⟩ : Fin (m + 1)) = (⟨n, hlt⟩ : Fin m).castSucc := rfl
      rw [hidx, signed_refinement_one]
      exact ih hlt

/-- BanLat's absolute-sum identity, reindexed over an arbitrary finite type. -/
theorem abs_sum_smul_disjoint {ι : Type*} [Fintype ι]
    (p : ι → E) (α : ι → ℝ) (hd : Pairwise (fun i j => IsVLDisjoint (p i) (p j))) :
    |∑ i, α i • p i| = ∑ i, |α i| • |p i| := by
  classical
  let e := (Fintype.equivFin ι).symm
  have h := abs_sum_of_pairwise_isVLDisjoint (x := fun i => p (e i))
    (α := fun i => α (e i)) (fun _ _ hij => hd (fun h => hij (e.injective h)))
  have h₁ := e.sum_comp (fun i => α i • p i)
  have h₂ := e.sum_comp (fun i => |α i| • |p i|)
  rw [h₁, h₂] at h
  exact h

/-- Every Rademacher has exactly the absolute value of the root fragment. -/
theorem abs_rademacher {φ : E →L[ℝ] ℝ} {u : E} {split : E → E}
    (hu : 0 ≤ u) (hs : IsBalancedSplit φ u split) (n : ℕ) :
    |rademacher u split n| = u := by
  rw [rademacher, abs_sum_smul_disjoint _ _ (cell_pairwise_disjoint hu hs _)]
  simpa only [abs_sign, abs_of_nonneg (cell_mem_Icc hu hs _ _).1, one_smul] using
    sum_cell u split (n + 1)

theorem weighted_sign_orthogonality {φ : E →L[ℝ] ℝ} {u : E} {split : E → E}
    (hu : 0 ≤ u) (hs : IsBalancedSplit φ u split) {n : ℕ} (i j : Fin n) :
    (∑ w : Word n, φ (cell u split n w) * sign i w * sign j w) =
      if i = j then φ u else 0 := by
  simp_rw [cell_phi hu hs]
  have heq : (∑ w : Word n, φ u / (2 : ℝ) ^ n * sign i w * sign j w) =
      (φ u / (2 : ℝ) ^ n) * ∑ w : Word n, sign i w * sign j w := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [heq, sign_orthogonality]
  split
  · exact div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
  · exact mul_zero _

/-- An existential exact-halving theorem supplies the actual split map used
in the tree, including its value at zero. -/
theorem exists_balancedSplit (φ : E →L[ℝ] ℝ) (u : E)
    (hhalf : ∀ x : E, 0 < x → x ≤ u →
      ∃ y : E, 0 ≤ y ∧ y ≤ x ∧ IsVLDisjoint y (x - y) ∧ φ y = φ x / 2) :
    ∃ split : E → E, IsBalancedSplit φ u split := by
  classical
  let split : E → E := fun x => if h : 0 < x ∧ x ≤ u then (hhalf x h.1 h.2).choose else 0
  refine ⟨split, ?_⟩
  intro x hx hxu
  by_cases hx0 : x = 0
  · subst x
    simp [split, IsVLDisjoint]
  · have hxpos := lt_of_le_of_ne hx (fun h => hx0 h.symm)
    have hvalid : 0 < x ∧ x ≤ u := ⟨hxpos, hxu⟩
    simpa only [split, dite_eq_left hvalid] using (hhalf x hxpos hxu).choose_spec

end PL1.BalancedFragmentTree
