import ThesisCommon.Analysis.UncountableSchauderBasis

/-! Coordinate solidity for arbitrary-index unconditional expansions.
Dominated coefficients are constructed using the Cauchy criterion for the
net of finite sums. No countability restriction or supplied completion map
is used.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
namespace NormalizedSchauderFamily
variable {𝕜 Γ E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (b : NormalizedSchauderFamily 𝕜 Γ E)

/-- Coordinatewise absolute domination implies domination of the actual vector norms. -/
theorem norm_le_of_coord_le (hb : b.IsOneUnconditional) {x y : E}
    (h : ∀ i, ‖b.coord i x‖ ≤ ‖b.coord i y‖) : ‖x‖ ≤ ‖y‖ := by
  apply le_of_tendsto_of_tendsto' (b.expansion_tendsto x).norm
    (b.expansion_tendsto y).norm
  intro F
  simpa only [one_mul] using hb.2 F (fun i => b.coord i x)
    (fun i => b.coord i y) (fun i _ => h i)

/-- Finite coordinate suppression is contractive on the entire space. -/
theorem finite_projection_norm_le (hb : b.IsOneUnconditional) (F : Finset Γ) (x : E) :
    ‖∑ i ∈ F, b.coord i x • b.vector i‖ ≤ ‖x‖ := by
  classical
  apply b.norm_le_of_coord_le hb
  intro i
  rw [b.coord_finite_sum]
  by_cases hi : i ∈ F
  · simp only [if_pos hi, le_refl]
  · simp only [if_neg hi, norm_zero]; exact norm_nonneg _

/-- Domination transfers the unconditional finite-tail Cauchy criterion. -/
theorem summable_of_coord_domination [CompleteSpace E] (hb : b.IsOneUnconditional)
    (x : E) (a : Γ → 𝕜) (ha : ∀ i, ‖a i‖ ≤ ‖b.coord i x‖) :
    Summable (fun i => a i • b.vector i) := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  obtain ⟨F, hF⟩ := summable_iff_vanishing_norm.mp (b.expansion x).summable ε hε
  refine ⟨F, ?_⟩
  intro G hGF
  have hdom : ‖∑ i ∈ G, a i • b.vector i‖ ≤
      ‖∑ i ∈ G, b.coord i x • b.vector i‖ := by
    simpa only [one_mul] using hb.2 G a (fun i => b.coord i x) (fun i _ => ha i)
  exact hdom.trans_lt (hF G hGF)

/-- Every family of coefficients dominated by a vector is realized by a
genuine unconditional sum, with no increase of norm. -/
theorem exists_of_coord_domination [CompleteSpace E] (hb : b.IsOneUnconditional)
    (x : E) (a : Γ → 𝕜) (ha : ∀ i, ‖a i‖ ≤ ‖b.coord i x‖) :
    ∃ y : E, (∀ i, b.coord i y = a i) ∧ ‖y‖ ≤ ‖x‖ := by
  have hs := b.summable_of_coord_domination hb x a ha
  let y : E := ∑' i, a i • b.vector i
  have hy (i : Γ) : b.coord i y = a i := b.coord_of_hasSum a hs.hasSum i
  refine ⟨y, hy, b.norm_le_of_coord_le hb ?_⟩
  intro i
  rw [hy]
  exact ha i

theorem finite_sum_norm_le_of_coord_domination (hb : b.IsOneUnconditional)
    (x : E) (a : Γ → 𝕜) (ha : ∀ i, ‖a i‖ ≤ ‖b.coord i x‖) (F : Finset Γ) :
    ‖∑ i ∈ F, a i • b.vector i‖ ≤ ‖x‖ := by
  have hdom : ‖∑ i ∈ F, a i • b.vector i‖ ≤
      ‖∑ i ∈ F, b.coord i x • b.vector i‖ := by
    simpa only [one_mul] using hb.2 F a (fun i => b.coord i x) (fun i _ => ha i)
  exact hdom.trans (b.finite_projection_norm_le hb F x)

end NormalizedSchauderFamily
end ThesisCommon
