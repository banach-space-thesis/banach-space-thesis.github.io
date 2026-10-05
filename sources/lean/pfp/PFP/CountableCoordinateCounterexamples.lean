import PFP.GeneralSumBlockStatements
import ThesisCommon.Analysis.CZeroSchauderFamily
import ThesisCommon.Analysis.CountableSchauderRankOne

/-! Actual countable-index counterexamples to the preserved standalone
printed formulas 4.27 and 4.30. The outer family is the normalized real
c₀ family on ℕ, and the coefficient space is ℝ. A bounded rank-one map
has every coordinate entry nonzero. The section-context versions, which
explicitly impose uncountability, are unaffected. -/
noncomputable section
open scoped ZeroAtInfty
namespace PFP
open ThesisCommon

theorem lemma_4_27_asPrinted_false_countable_cZero :
    ¬ Lemma_4_27_asPrinted ℝ ℕ ℝ C₀(ℕ, ℝ)
      (scalarCZeroSchauderFamily (𝕜 := ℝ) (Γ := ℕ)) := by
  intro h
  let b := scalarCZeroSchauderFamily (𝕜 := ℝ) (Γ := ℕ)
  let hs := scalarCZeroSchauderFamily_symmetric (𝕜 := ℝ) (Γ := ℕ)
  let T := UncountableSchauderSum.geometricRankOne b hs.1
  obtain ⟨Λ,hΛ,hdiag⟩ := h hs T (Or.inr (fun γ =>
    ⟨Set.to_countable _,Set.to_countable _⟩))
  apply UncountableSchauderSum.no_full_cardinal_diagonal_for_geometricRankOne b hs.1
  exact ⟨Λ,hΛ,hdiag⟩

theorem lemma_4_30_asPrinted_false_countable_cZero :
    ¬ Lemma_4_30_asPrinted ℝ ℕ ℝ C₀(ℕ, ℝ)
      (scalarCZeroSchauderFamily (𝕜 := ℝ) (Γ := ℕ)) := by
  intro h
  let b := scalarCZeroSchauderFamily (𝕜 := ℝ) (Γ := ℕ)
  let hs := scalarCZeroSchauderFamily_symmetric (𝕜 := ℝ) (Γ := ℕ)
  let T := UncountableSchauderSum.geometricRankOne b hs.1
  obtain ⟨Λ,hΛ,hdiag⟩ := h hs
    (scalarCZeroSchauderFamily_not_equivalentEllOne (𝕜 := ℝ) (Γ := ℕ)) inferInstance T
  apply UncountableSchauderSum.no_full_cardinal_diagonal_for_geometricRankOne b hs.1
  exact ⟨Λ,hΛ,hdiag⟩

end PFP
