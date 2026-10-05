import ThesisCommon.Analysis.GowersMaureyAveragedRationalApproximation
import ThesisCommon.Analysis.GowersMaureyAveragedContractions

/-! A genuine coding step starting from any nonzero averaged functional.
Gaussian rationality is constructed first, and the coding injection then
supplies arbitrarily large codes through distinct rational contractions. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem ConstructionData.exists_large_code_averaged_near
    (D : ConstructionData 𝕜) {xs : List (C00 𝕜)} (hxs : CodingDomain xs)
    {N : ℕ} {a : C00 𝕜} (ha : AveragedFunctional (implicitNorm D) N a)
    (ha0 : a ≠ 0) (hbefore : ∀ c ∈ xs, Before c a)
    {δ : ℝ} (hδ : 0 < δ) (M : ℕ) (B : ℝ) :
    ∃ b : C00 𝕜, b ≠ 0 ∧ AveragedFunctional (implicitNorm D) N b ∧
      RationalUnitSequence b ∧ b.support ⊆ a.support ∧ CodingDomain (xs ++ [b]) ∧
      mass (b-a) < δ ∧ M < D.sigma (xs ++ [b]) ∧
      B < logarithmicWeight (D.sigma (xs ++ [b])) := by
  obtain ⟨a',ha'0,ha',hr,hs,he⟩ := ha.exists_nonzero_rational_near ha0
    (show 0 < δ/2 by positivity)
  have hbefore' : ∀ c ∈ xs, Before c a' := by
    intro c hc s hcs t ht
    exact hbefore c hc s hcs t (hs ht)
  obtain ⟨q,hq,hq1,_,hqs,hcode,havg,herr,hM,hB⟩ :=
    D.exists_large_code_averaged_contraction hxs hr ha'0 hbefore' ha' mass
      (show 0 < δ/2 by positivity) M B
  refine ⟨(q : 𝕜) • a',smul_ne_zero (by exact_mod_cast hq.ne') ha'0,
    havg,hr.rat_smul hq.le hq1.le,?_,hcode,?_,hM,hB⟩
  · rw [hqs]
    exact hs
  · have heq : (q : 𝕜) • a' - a = ((q : 𝕜) • a' - a') + (a'-a) := by abel
    rw [heq]
    exact (map_add_le_add mass _ _).trans_lt (by linarith)

end ThesisCommon.GowersMaurey
