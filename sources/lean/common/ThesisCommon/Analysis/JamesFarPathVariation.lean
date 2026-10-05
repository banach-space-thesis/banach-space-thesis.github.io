import ThesisCommon.Analysis.JamesPathConcatenation

/-! Finite-p variation on paths lying far to the right tends uniformly to
zero. Otherwise concatenating separated witness paths contradicts bounded
variation. This is an actual estimate on each James vector, not a basis
or shrinking assumption. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent}

theorem james_far_path_small (hp : p.val ≠ ∞) (x : JamesSequenceSpace 𝕜 p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : JamesPath, N < s.index 0 → ‖jamesPathMap 𝕜 p s x.val‖ < ε := by
  classical
  by_contra hn
  push_neg at hn
  have hpower : 0 < ε ^ p.val.toReal := Real.rpow_pos_of_pos hε _
  have hgrow (n : ℕ) : ∃ s : JamesPath,
      (n : ℝ) * ε ^ p.val.toReal ≤ ‖jamesPathMap 𝕜 p s x.val‖ ^ p.val.toReal := by
    induction n with
    | zero =>
      refine ⟨JamesPath.two 0 1 Nat.zero_lt_one, ?_⟩
      simp only [Nat.cast_zero, zero_mul]
      exact Real.rpow_nonneg (norm_nonneg _) _
    | succ n ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨t, ht, hnorm⟩ := hn (s.index (Fin.last s.length))
      refine ⟨s.append t ht, ?_⟩
      calc
        ((n + 1 : ℕ) : ℝ) * ε ^ p.val.toReal =
            (n : ℝ) * ε ^ p.val.toReal + ε ^ p.val.toReal := by push_cast; ring
        _ ≤ ‖jamesPathMap 𝕜 p s x.val‖ ^ p.val.toReal +
            ‖jamesPathMap 𝕜 p t x.val‖ ^ p.val.toReal :=
          add_le_add hs (Real.rpow_le_rpow hε.le hnorm ENNReal.toReal_nonneg)
        _ ≤ ‖jamesPathMap 𝕜 p (s.append t ht) x.val‖ ^ p.val.toReal :=
          jamesPath_append_norm_rpow_le p hp s t ht x.val
  obtain ⟨n, hn⟩ := exists_nat_gt (‖x‖ ^ p.val.toReal / ε ^ p.val.toReal)
  have hn' : ‖x‖ ^ p.val.toReal < (n : ℝ) * ε ^ p.val.toReal :=
    (div_lt_iff₀ hpower).mp hn
  obtain ⟨s, hs⟩ := hgrow n
  have hs' : ‖jamesPathMap 𝕜 p s x.val‖ ^ p.val.toReal ≤ ‖x‖ ^ p.val.toReal :=
    Real.rpow_le_rpow (norm_nonneg _) (x.path_norm_le s) ENNReal.toReal_nonneg
  exact (not_lt_of_ge (hs.trans hs')) hn'

end ThesisCommon
