import Sigma.ComplexDesiredProperty
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Data.Countable.Defs

noncomputable section
namespace SigmaNonprimarity

theorem complex_product_has_one_norming {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {a : ℕ → E →L[ℂ] ℂ} {b : ℕ → F →L[ℂ] ℂ}
    (ha : IsComplexCNorming a 1) (hb : IsComplexCNorming b 1) :
    ∃ e : ℕ → (E × F) →L[ℂ] ℂ, IsComplexCNorming e 1 := by
  obtain ⟨s, hs⟩ := exists_surjective_nat (ℕ ⊕ ℕ)
  let e : ℕ → (E × F) →L[ℂ] ℂ := fun n =>
    match s n with
    | Sum.inl k => (a k).comp (ContinuousLinearMap.fst ℂ E F)
    | Sum.inr k => (b k).comp (ContinuousLinearMap.snd ℂ E F)
  have hnorm (n : ℕ) (x : E × F) : ‖e n x‖ ≤ ‖x‖ := by
    rcases hsn : s n with k | k
    · simp only [e, hsn]
      change ‖a k x.1‖ ≤ ‖x‖
      exact ((a k).le_opNorm x.1).trans
        ((mul_le_mul_of_nonneg_right (ha.2.2.1 k) (norm_nonneg x.1)).trans
          (by simpa using norm_fst_le x))
    · simp only [e, hsn]
      change ‖b k x.2‖ ≤ ‖x‖
      exact ((b k).le_opNorm x.2).trans
        ((mul_le_mul_of_nonneg_right (hb.2.2.1 k) (norm_nonneg x.2)).trans
          (by simpa using norm_snd_le x))
  have hunit (n) : ‖e n‖ ≤ 1 :=
    (e n).opNorm_le_bound zero_le_one (fun x => by simpa using hnorm n x)
  refine ⟨e, zero_lt_one, le_rfl, hunit, ?_⟩
  intro x
  rw [one_mul, Prod.norm_def]
  have hbound := complex_evaluations_bddAbove e hunit x
  apply max_le
  · have h := ha.2.2.2 x.1
    rw [one_mul] at h
    refine h.trans (ciSup_le fun k => ?_)
    obtain ⟨n, hn⟩ := hs (Sum.inl k)
    have hh := le_ciSup hbound n
    simpa [e, hn] using hh
  · have h := hb.2.2.2 x.2
    rw [one_mul] at h
    refine h.trans (ciSup_le fun k => ?_)
    obtain ⟨n, hn⟩ := hs (Sum.inr k)
    have hh := le_ciSup hbound n
    simpa [e, hn] using hh

end SigmaNonprimarity


