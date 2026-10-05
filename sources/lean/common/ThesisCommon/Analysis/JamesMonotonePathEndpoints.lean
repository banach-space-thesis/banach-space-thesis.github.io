import ThesisCommon.Analysis.JamesMonotonePaths

/-! Monotone path compression can retain both endpoints. This permits
variation estimates inside adjacent closed coordinate intervals. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon

@[simp] theorem JamesPath.snoc_first (s : JamesPath) (n : ℕ)
    (hn : s.index (Fin.last s.length) < n) : (s.snoc n hn).index 0 = s.index 0 :=
  JamesPath.snoc_castSucc s n hn 0

theorem exists_jamesPath_of_monotone_endpoints (w : ℕ → ℕ → ℝ) (hw : ∀ n, w n n = 0)
    {n : ℕ} (f : Fin (n + 1) → ℕ) (hf : Monotone f) :
    ∃ s : JamesPath, s.index 0 = f 0 ∧ s.index (Fin.last s.length) = f (Fin.last n) ∧
      (∑ j : Fin n, w (f j.castSucc) (f j.succ)) =
        ∑ j : Fin s.length, w (s.index j.castSucc) (s.index j.succ) := by
  induction n with
  | zero => exact ⟨JamesPath.point (f 0), rfl, rfl, rfl⟩
  | succ n ih =>
    let g : Fin (n + 1) → ℕ := fun i => f i.castSucc
    obtain ⟨s, hs0, hs, he⟩ := ih g (hf.comp Fin.strictMono_castSucc.monotone)
    have hle : f (Fin.last n).castSucc ≤ f (Fin.last (n + 1)) := hf (Fin.le_last _)
    have hsum : (∑ j : Fin (n + 1), w (f j.castSucc) (f j.succ)) =
        (∑ j : Fin n, w (g j.castSucc) (g j.succ)) +
          w (g (Fin.last n)) (f (Fin.last (n + 1))) := by
      rw [Fin.sum_univ_castSucc]
      simp only [g, Fin.succ_castSucc, Fin.succ_last]
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hn : s.index (Fin.last s.length) < f (Fin.last (n + 1)) := hs ▸ hlt
      refine ⟨s.snoc (f (Fin.last (n + 1))) hn, ?_, JamesPath.snoc_last _ _ _, ?_⟩
      · rw [JamesPath.snoc_first, hs0]
        rfl
      · rw [JamesPath.snoc_energy, ← he, hs]
        exact hsum
    · refine ⟨s, hs0, hs.trans heq, ?_⟩
      rw [hsum, show g (Fin.last n) = f (Fin.last (n + 1)) from heq, hw, add_zero]
      exact he

end ThesisCommon
