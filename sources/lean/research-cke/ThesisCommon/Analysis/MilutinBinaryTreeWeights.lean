import ThesisCommon.Analysis.MilutinBinaryCylinderSystem

/-! Continuous positive binary-tree weights extending the cylinder indicators
of any embedded copy of Cantor space in a compact Hausdorff space. -/

noncomputable section
open Set
namespace ThesisCommon
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
variable (e : C((ℕ → Bool), Y)) (he : Function.Injective e)

def milutinBinaryCylinderImage (n : ℕ) (w : MilutinBinaryWord n) : Set Y :=
  e '' {x | milutinBinaryWordPrefix n x = w}

theorem milutinBinaryCylinderImage_isClosed (n : ℕ) (w : MilutinBinaryWord n) :
    IsClosed (milutinBinaryCylinderImage e n w) :=
  ((isClosed_eq (milutinBinaryWordPrefix n).continuous continuous_const).isCompact.image
    e.continuous).isClosed

include he in
theorem milutinBinaryCylinderImage_disjoint (n : ℕ) (w : MilutinBinaryWord n) :
    Disjoint (milutinBinaryCylinderImage e (n + 1) (Fin.snoc w false))
      (milutinBinaryCylinderImage e (n + 1) (Fin.snoc w true)) := by
  rw [Set.disjoint_left]
  rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
  have hzx' := he hzx
  subst z
  have h := congrArg (fun u : MilutinBinaryWord (n + 1) => u (Fin.last n)) (hx.symm.trans hz)
  simpa using h

include he in
theorem milutinBinarySplit_exists (n : ℕ) (w : MilutinBinaryWord n) :
    ∃ f : C(Y, ℝ),
      EqOn f 0 (milutinBinaryCylinderImage e (n + 1) (Fin.snoc w false)) ∧
      EqOn f 1 (milutinBinaryCylinderImage e (n + 1) (Fin.snoc w true)) ∧
      ∀ y, f y ∈ Set.Icc (0 : ℝ) 1 :=
  exists_continuous_zero_one_of_isClosed
    (milutinBinaryCylinderImage_isClosed e _ _) (milutinBinaryCylinderImage_isClosed e _ _)
    (milutinBinaryCylinderImage_disjoint e he n w)

def milutinBinarySplit (n : ℕ) (w : MilutinBinaryWord n) : C(Y, ℝ) :=
  (milutinBinarySplit_exists e he n w).choose

theorem milutinBinarySplit_mem_Icc (n : ℕ) (w : MilutinBinaryWord n) (y : Y) :
    milutinBinarySplit e he n w y ∈ Set.Icc (0 : ℝ) 1 :=
  (milutinBinarySplit_exists e he n w).choose_spec.2.2 y

theorem milutinBinarySplit_apply_false (n : ℕ) (w : MilutinBinaryWord n) (x : ℕ → Bool)
    (hx : milutinBinaryWordPrefix (n + 1) x = Fin.snoc w false) :
    milutinBinarySplit e he n w (e x) = 0 :=
  (milutinBinarySplit_exists e he n w).choose_spec.1 ⟨x, hx, rfl⟩

theorem milutinBinarySplit_apply_true (n : ℕ) (w : MilutinBinaryWord n) (x : ℕ → Bool)
    (hx : milutinBinaryWordPrefix (n + 1) x = Fin.snoc w true) :
    milutinBinarySplit e he n w (e x) = 1 :=
  (milutinBinarySplit_exists e he n w).choose_spec.2.1 ⟨x, hx, rfl⟩

def milutinBinaryTreeWeight : (n : ℕ) → MilutinBinaryWord n → C(Y, ℝ)
  | 0, _ => 1
  | n + 1, w => milutinBinaryTreeWeight n (Fin.init w) *
      if w (Fin.last n) then milutinBinarySplit e he n (Fin.init w)
        else 1 - milutinBinarySplit e he n (Fin.init w)

@[simp] theorem milutinBinaryTreeWeight_snoc_false (n : ℕ) (w : MilutinBinaryWord n) :
    milutinBinaryTreeWeight e he (n + 1) (Fin.snoc w false) =
      milutinBinaryTreeWeight e he n w * (1 - milutinBinarySplit e he n w) := by
  simp [milutinBinaryTreeWeight]

@[simp] theorem milutinBinaryTreeWeight_snoc_true (n : ℕ) (w : MilutinBinaryWord n) :
    milutinBinaryTreeWeight e he (n + 1) (Fin.snoc w true) =
      milutinBinaryTreeWeight e he n w * milutinBinarySplit e he n w := by
  simp [milutinBinaryTreeWeight]

theorem milutinBinaryTreeWeight_nonneg (n : ℕ) (w : MilutinBinaryWord n) (y : Y) :
    0 ≤ milutinBinaryTreeWeight e he n w y := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih =>
    change 0 ≤ milutinBinaryTreeWeight e he n (Fin.init w) y * _
    apply mul_nonneg (ih _)
    split
    · exact (milutinBinarySplit_mem_Icc e he n _ y).1
    · exact sub_nonneg.mpr (milutinBinarySplit_mem_Icc e he n _ y).2

theorem milutinBinaryTreeWeight_sum (n : ℕ) (y : Y) :
    ∑ w, milutinBinaryTreeWeight e he n w y = 1 := by
  induction n with
  | zero => simp [milutinBinaryTreeWeight]
  | succ n ih =>
    rw [milutinBinaryWord_sum_snoc]
    calc
      _ = ∑ w, milutinBinaryTreeWeight e he n w y := by
        apply Finset.sum_congr rfl
        intro w _
        simp only [milutinBinaryTreeWeight_snoc_false, milutinBinaryTreeWeight_snoc_true,
          ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply]
        ring
      _ = 1 := ih

theorem milutinBinaryTreeWeight_on_image (n : ℕ) (w : MilutinBinaryWord n) (x : ℕ → Bool) :
    milutinBinaryTreeWeight e he n w (e x) = if milutinBinaryWordPrefix n x = w then 1 else 0 := by
  classical
  induction n with
  | zero => simp [milutinBinaryTreeWeight, Subsingleton.elim (milutinBinaryWordPrefix 0 x) w]
  | succ n ih =>
    obtain ⟨⟨b, v⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).surjective w
    change milutinBinaryTreeWeight e he (n + 1) (Fin.snoc v b) (e x) =
      if milutinBinaryWordPrefix (n + 1) x = Fin.snoc v b then 1 else 0
    by_cases hv : milutinBinaryWordPrefix n x = v
    · have hnext : milutinBinaryWordPrefix (n + 1) x = Fin.snoc v (x n) := by
        rw [milutinBinaryWordPrefix_snoc, hv]
      cases hb : x n <;> cases b <;>
        simp only [hb] at hnext <;>
        simp [milutinBinaryTreeWeight_snoc_false, milutinBinaryTreeWeight_snoc_true,
          ih, hv, hnext, milutinBinarySplit_apply_false e he n v x,
          milutinBinarySplit_apply_true e he n v x, Fin.snoc_inj]
    · have hnext : milutinBinaryWordPrefix (n + 1) x ≠ Fin.snoc v b := by
        intro h
        apply hv
        simpa using congrArg Fin.init h
      cases b <;> simp [ih, hv, hnext]

end ThesisCommon
