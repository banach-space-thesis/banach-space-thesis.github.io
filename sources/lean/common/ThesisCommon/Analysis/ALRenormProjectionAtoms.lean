import ThesisCommon.Analysis.ALRenormBandEstimates

/-! Simultaneous Boolean refinements of finitely many commuting band
projections. The cells are explicit finite products, including empty cells. -/
noncomputable section
open scoped BigOperators ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon

section Algebra
variable {R : Type*} [Ring R]

def projectionFactor (p : R) (b : Bool) : R := if b then p else 1-p

def projectionAtom : {n : ℕ} → (Fin n → R) → (Fin n → Bool) → R
  | 0, _, _ => 1
  | _+1, p, ε => projectionFactor (p 0) (ε 0) *
      projectionAtom (fun i => p i.succ) (fun i => ε i.succ)

theorem projectionFactor_commute {p q : R} (h : Commute p q) (b : Bool) :
    Commute q (projectionFactor p b) := by
  cases b
  · change q * (1-p) = (1-p) * q
    simp only [mul_sub, sub_mul, mul_one, one_mul, h.eq]
  · exact h.symm

theorem projectionAtom_commute {n : ℕ} (p : Fin n → R) (ε : Fin n → Bool) (q : R)
    (h : ∀ i, Commute (p i) q) : Commute q (projectionAtom p ε) := by
  induction n with
  | zero => exact Commute.one_right q
  | succ n ih =>
    have hhead := (projectionFactor_commute (h 0) (ε 0)).eq
    have htail := (ih (fun i => p i.succ) (fun i => ε i.succ) (fun i => h i.succ)).eq
    change q * (projectionFactor (p 0) (ε 0) * projectionAtom _ _) =
      (projectionFactor (p 0) (ε 0) * projectionAtom _ _) * q
    rw [← mul_assoc, hhead, mul_assoc, htail, ← mul_assoc]

theorem projectionAtom_selected_left {n : ℕ} (p : Fin n → R)
    (hid : ∀ i, p i * p i = p i) (hcomm : ∀ i j, Commute (p i) (p j))
    (ε : Fin n → Bool) (i : Fin n) :
    p i * projectionAtom p ε = if ε i then projectionAtom p ε else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · cases hε : ε 0
      · simp only [projectionAtom, projectionFactor, hε, Bool.false_eq_true, if_false]
        rw [← mul_assoc, mul_sub, mul_one, hid, sub_self, zero_mul]
      · simp only [projectionAtom, projectionFactor, hε, if_true]
        rw [← mul_assoc, hid]
    · have hc := (projectionFactor_commute (hcomm 0 j.succ) (ε 0)).eq
      change p j.succ * (projectionFactor (p 0) (ε 0) * projectionAtom _ _) = _
      rw [← mul_assoc, hc, mul_assoc,
        ih (fun k => p k.succ) (fun k => hid k.succ) (fun k l => hcomm k.succ l.succ)
          (fun k => ε k.succ) j]
      cases ε j.succ <;> simp [projectionAtom]

theorem projectionAtom_selected_right {n : ℕ} (p : Fin n → R)
    (hid : ∀ i, p i * p i = p i) (hcomm : ∀ i j, Commute (p i) (p j))
    (ε : Fin n → Bool) (i : Fin n) :
    projectionAtom p ε * p i = if ε i then projectionAtom p ε else 0 := by
  rw [← (projectionAtom_commute p ε (p i) (fun j => hcomm j i)).eq]
  exact projectionAtom_selected_left p hid hcomm ε i

theorem projectionAtom_absorb {n : ℕ} (p : Fin n → R) (ε : Fin n → Bool) (z : R)
    (hz : ∀ i, projectionFactor (p i) (ε i) * z = z) : projectionAtom p ε * z = z := by
  induction n with
  | zero => simp [projectionAtom]
  | succ n ih =>
    change (projectionFactor (p 0) (ε 0) * projectionAtom _ _) * z = z
    rw [mul_assoc, ih (fun i => p i.succ) (fun i => ε i.succ) (fun i => hz i.succ), hz 0]

theorem projectionAtom_idempotent {n : ℕ} (p : Fin n → R)
    (hid : ∀ i, p i * p i = p i) (hcomm : ∀ i j, Commute (p i) (p j))
    (ε : Fin n → Bool) : projectionAtom p ε * projectionAtom p ε = projectionAtom p ε := by
  apply projectionAtom_absorb
  intro i
  have h := projectionAtom_selected_left p hid hcomm ε i
  cases hε : ε i
  · simpa only [projectionFactor, hε, Bool.false_eq_true, if_false, sub_mul, one_mul,
      show p i * projectionAtom p ε = 0 by simpa [hε] using h, sub_zero]
  · simpa only [projectionFactor, hε, if_true] using h

theorem projectionAtom_orthogonal {n : ℕ} (p : Fin n → R)
    (hid : ∀ i, p i * p i = p i) (hcomm : ∀ i j, Commute (p i) (p j))
    (ε η : Fin n → Bool) (hne : ε ≠ η) : projectionAtom p ε * projectionAtom p η = 0 := by
  have hex : ∃ i, ε i ≠ η i := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hex
  have hε := projectionAtom_selected_right p hid hcomm ε i
  have hη := projectionAtom_selected_left p hid hcomm η i
  cases he : ε i <;> cases hh : η i
  · exact (hi (he.trans hh.symm)).elim
  · have hzero : projectionAtom p ε * p i = 0 := by simpa [he] using hε
    have hone : p i * projectionAtom p η = projectionAtom p η := by simpa [hh] using hη
    rw [← hone, ← mul_assoc, hzero, zero_mul]
  · have hone : projectionAtom p ε * p i = projectionAtom p ε := by simpa [he] using hε
    have hzero : p i * projectionAtom p η = 0 := by simpa [hh] using hη
    rw [← hone, mul_assoc, hzero, mul_zero]
  · exact (hi (he.trans hh.symm)).elim

theorem projectionAtom_sum {n : ℕ} (p : Fin n → R) :
    (∑ ε : Fin n → Bool, projectionAtom p ε) = 1 := by
  classical
  induction n with
  | zero => simp [projectionAtom]
  | succ n ih =>
    have hsum : (∑ ε, projectionAtom p ε) =
        ∑ q : Bool × (Fin n → Bool), projectionAtom p (Fin.cons q.1 q.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool)) _ _ (fun _ => rfl)).symm
    rw [hsum, Fintype.sum_prod_type]
    simp only [projectionAtom, Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum, ih, mul_one,
      Fintype.sum_bool, projectionFactor, if_true, Bool.false_eq_true, if_false]
    noncomm_ring

end Algebra

section Ordered
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E]
variable [IsOrderedModule ℝ E] [HasSolidNorm E]

theorem projectionFactor_nonneg {p : E →L[ℝ] E} (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ projectionFactor p b := by
  cases b
  · exact sub_nonneg.mpr hp1
  · exact hp

theorem projectionFactor_le_one {p : E →L[ℝ] E} (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    projectionFactor p b ≤ 1 := by
  cases b
  · exact sub_le_self _ hp
  · exact hp1

theorem projectionAtom_nonneg {n : ℕ} (p : Fin n → E →L[ℝ] E)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (ε : Fin n → Bool) :
    0 ≤ projectionAtom p ε := by
  induction n with
  | zero => intro x hx; exact hx
  | succ n ih =>
    have htail := ih (fun i => p i.succ) (fun i => hp i.succ) (fun i => hp1 i.succ)
      (fun i => ε i.succ)
    intro x hx
    exact projectionFactor_nonneg (hp 0) (hp1 0) (ε 0) _ (htail x hx)

theorem projectionAtom_le_one {n : ℕ} (p : Fin n → E →L[ℝ] E)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (ε : Fin n → Bool) :
    projectionAtom p ε ≤ 1 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have htailpos := projectionAtom_nonneg (fun i => p i.succ)
      (fun i => hp i.succ) (fun i => hp1 i.succ) (fun i => ε i.succ)
    have htail := ih (fun i => p i.succ) (fun i => hp i.succ) (fun i => hp1 i.succ)
      (fun i => ε i.succ)
    intro x hx
    exact (projectionFactor_le_one (hp 0) (hp1 0) (ε 0) _ (htailpos x hx)).trans (htail x hx)

theorem projectionAtom_sum_apply {n : ℕ} (p : Fin n → E →L[ℝ] E) (x : E) :
    (∑ ε : Fin n → Bool, projectionAtom p ε x) = x := by
  have h := congrArg (fun T : E →L[ℝ] E => T x) (projectionAtom_sum p)
  simpa using h

end Ordered
end ThesisCommon
