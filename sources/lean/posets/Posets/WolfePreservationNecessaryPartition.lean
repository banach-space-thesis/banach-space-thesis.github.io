import ThesisCommon.Analysis.Factorization

/-! Quantitative retention through a finite operator partition. The primary
factorisation constant is an explicit hypothesis. One finite partition costs
at most a fixed power of that constant; no uniform bound for an unbounded
iteration of partitions is asserted. -/

noncomputable section
open ThesisCommon
namespace Posets
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Nontrivial E]

theorem wolfe_finite_partition_factorization {C : ℝ} (hC : 1 ≤ C)
    (hPFP : HasCPFP 𝕜 E C) (n : ℕ)
    (A : Fin n → E →L[𝕜] E)
    (hA : ∑ i, A i = ContinuousLinearMap.id 𝕜 E) :
    ∃ i, FactorsIdentityWith (A i) E (C ^ n) := by
  classical
  induction n with
  | zero =>
      obtain ⟨x, hx⟩ := exists_ne (0 : E)
      have he := congrArg (fun T : E →L[𝕜] E => T x) hA
      simp at he
      exact (hx he.symm).elim
  | succ n ih =>
      rcases hPFP (A 0) with hfirst | ⟨U, V, hUV, hnorm⟩
      · exact ⟨0, hfirst.mono (le_self_pow₀ hC (Nat.succ_ne_zero n))⟩
      · let B (i : Fin n) := (U.comp (A i.succ)).comp V
        have htail : ∑ i : Fin n, A i.succ = ContinuousLinearMap.id 𝕜 E - A 0 := by
          rw [Fin.sum_univ_succ] at hA
          exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hA)
        have hB : ∑ i, B i = ContinuousLinearMap.id 𝕜 E := by
          rw [← hUV]
          ext x
          simp only [B, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
          rw [← map_sum]
          have ht := congrArg (fun Q : E →L[𝕜] E => Q (V x)) htail
          simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sub_apply,
            ContinuousLinearMap.id_apply] using congrArg U ht
        obtain ⟨i, hi⟩ := ih B hB
        refine ⟨i.succ, (hi.of_compression U V).mono ?_⟩
        change C ^ n * (‖U‖ * ‖V‖) ≤ C ^ (n + 1)
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_left hnorm (pow_nonneg (le_trans (by norm_num) hC) n)

end Posets
