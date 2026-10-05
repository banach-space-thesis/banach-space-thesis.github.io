import JLMS.FiniteRowBlocks

/-! # Common thinning of finitely many increasing coordinate sequences -/

noncomputable section
namespace JLMS
variable {ι : Type*} [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.decEq

theorem exists_strictMono_ordered_rows (h : ℕ → ι → ℕ)
    (hh : ∀ i, StrictMono (fun n => h n i)) :
    ∃ q : ℕ → ℕ, StrictMono q ∧
      ∀ n m, n < m → ∀ i j, h (q n) i < h (q m) j := by
  let M (n : ℕ) := (Finset.univ.image (h n)).sup id
  have hM (n : ℕ) (i : ι) : h n i ≤ M n :=
    Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let q : ℕ → ℕ := Nat.rec 0 (fun _ k => M k + 1)
  have hsucc (n : ℕ) : q n < q (n + 1) := by
    let i : ι := Classical.choice inferInstance
    exact lt_of_le_of_lt ((hh i).id_le _ |>.trans (hM _ i)) (Nat.lt_succ_self _)
  have hq : StrictMono q := strictMono_nat_of_lt_succ hsucc
  refine ⟨q, hq, ?_⟩
  intro n m hnm i j
  have hfirst : h (q n) i < q (n + 1) :=
    lt_of_le_of_lt (hM _ i) (Nat.lt_succ_self _)
  exact hfirst.trans_le ((hq.monotone (Nat.succ_le_of_lt hnm)).trans ((hh j).id_le _))

end JLMS
