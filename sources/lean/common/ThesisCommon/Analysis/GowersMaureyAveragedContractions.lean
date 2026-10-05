import ThesisCommon.Analysis.GowersMaureyCodePerturbation
import ThesisCommon.Analysis.GowersMaureySupportIntervals

/-! Rational coding perturbations preserve the actual averaged-functional
class. The witnesses are the original successive dual-unit functionals,
contracted by the same scalar; their averaging parameter is unchanged. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem DualUnit.smul_of_norm_le_one {p : Seminorm 𝕜 (C00 𝕜)} {a : C00 𝕜}
    (ha : DualUnit p a) {c : 𝕜} (hc : ‖c‖ ≤ 1) : DualUnit p (c • a) := by
  intro x
  rw [pairing_smul_left, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (ha x)

theorem AveragedFunctional.smul_of_norm_le_one {p : Seminorm 𝕜 (C00 𝕜)}
    {n : ℕ} {a : C00 𝕜} (ha : AveragedFunctional p n a)
    {c : 𝕜} (hc : ‖c‖ ≤ 1) : AveragedFunctional p n (c • a) := by
  obtain ⟨hn,z,hz,hunit,he⟩ := ha
  refine ⟨hn,fun i => c • z i,?_,fun i => (hunit i).smul_of_norm_le_one hc,?_⟩
  · intro i j hij s hs t ht
    exact hz i j hij s (Finsupp.support_smul hs) t (Finsupp.support_smul ht)
  · rw [he, smul_comm, Finset.smul_sum]

theorem ConstructionData.exists_large_code_averaged_contraction
    (D : ConstructionData 𝕜) {xs : List (C00 𝕜)} (hxs : CodingDomain xs)
    {a : C00 𝕜} (ha : RationalUnitSequence a) (ha0 : a ≠ 0)
    (hbefore : ∀ b ∈ xs, Before b a) {p : Seminorm 𝕜 (C00 𝕜)} {n : ℕ}
    (havg : AveragedFunctional p n a) (error : Seminorm 𝕜 (C00 𝕜))
    {ε : ℝ} (hε : 0 < ε) (M : ℕ) (B : ℝ) :
    ∃ q : ℚ, 0 < q ∧ q < 1 ∧ 1-(q : ℝ) < ε ∧
      ((q : 𝕜) • a).support = a.support ∧ CodingDomain (xs ++ [(q : 𝕜) • a]) ∧
      AveragedFunctional p n ((q : 𝕜) • a) ∧ error ((q : 𝕜) • a - a) < ε ∧
      M < D.sigma (xs ++ [(q : 𝕜) • a]) ∧
      B < logarithmicWeight (D.sigma (xs ++ [(q : 𝕜) • a])) := by
  obtain ⟨q,hq,hq1,hnear,hs,hcode,herr,hM,hB⟩ :=
    D.exists_large_code_rational_contraction hxs ha ha0 hbefore error hε M B
  have hqn : ‖(q : 𝕜)‖ ≤ 1 := by
    rw [← RCLike.ofReal_ratCast, RCLike.norm_ofReal,
      abs_of_nonneg (by exact_mod_cast hq.le : (0 : ℝ) ≤ q)]
    exact_mod_cast hq1.le
  exact ⟨q,hq,hq1,hnear,hs,hcode,havg.smul_of_norm_le_one hqn,herr,hM,hB⟩

end ThesisCommon.GowersMaurey
