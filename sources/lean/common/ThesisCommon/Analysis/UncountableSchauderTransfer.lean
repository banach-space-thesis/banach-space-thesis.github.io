import ThesisCommon.Analysis.UncountableSchauderFactorAssembly
import ThesisCommon.Analysis.UncountableSchauderHajnalSelection

/-! Primary factorisation transfers to arbitrary-index symmetric sums.
Separable coefficients require only uncountably many coordinates; a
countable total dual set requires cardinality strictly above aleph-one.
Only the nonuniform PFP conclusion requires uncountable cofinality. -/
noncomputable section
open TopologicalSpace
namespace ThesisCommon.UncountableSchauderSum
variable {𝕜 Γ E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {b : NormalizedSchauderFamily 𝕜 Γ E}

theorem hasCPFP_of_separable [SeparableSpace X] (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    {C : ℝ} (hC : 0 ≤ C) (hX : HasCPFP 𝕜 X C) :
    HasCPFP 𝕜 (UncountableSchauderSum b hs.1 X) C :=
  hasCPFP_of_diagonal_selection hs hΓ.le
    (diagonal_coordinates_of_separable hs hnot hΓ) hC hX

theorem hasUPFP_of_separable [SeparableSpace X] (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (hX : HasUPFP 𝕜 X) : HasUPFP 𝕜 (UncountableSchauderSum b hs.1 X) := by
  obtain ⟨C, hC, hX⟩ := hX
  exact ⟨C, hC, hasCPFP_of_separable hs hnot hΓ (zero_le_one.trans hC) hX⟩

theorem hasPFP_of_separable [SeparableSpace X] (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof) (hX : HasPFP 𝕜 X) :
    HasPFP 𝕜 (UncountableSchauderSum b hs.1 X) :=
  hasPFP_of_diagonal_selection hs hΓ.le hcof
    (diagonal_coordinates_of_separable hs hnot hΓ) hX

theorem hasCPFP_of_countable_total_dual (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) (htotal : HasCountableTotalDual 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) {C : ℝ} (hC : 0 ≤ C)
    (hX : HasCPFP 𝕜 X C) : HasCPFP 𝕜 (UncountableSchauderSum b hs.1 X) C :=
  hasCPFP_of_diagonal_selection hs (Cardinal.aleph0_lt_aleph_one.trans hΓ).le
    (diagonal_coordinates_of_countable_total_dual hs hnot htotal hΓ) hC hX

theorem hasUPFP_of_countable_total_dual (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) (htotal : HasCountableTotalDual 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) (hX : HasUPFP 𝕜 X) :
    HasUPFP 𝕜 (UncountableSchauderSum b hs.1 X) := by
  obtain ⟨C, hC, hX⟩ := hX
  exact ⟨C, hC, hasCPFP_of_countable_total_dual hs hnot htotal hΓ
    (zero_le_one.trans hC) hX⟩

theorem hasPFP_of_countable_total_dual (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) (htotal : HasCountableTotalDual 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof) (hX : HasPFP 𝕜 X) :
    HasPFP 𝕜 (UncountableSchauderSum b hs.1 X) :=
  hasPFP_of_diagonal_selection hs (Cardinal.aleph0_lt_aleph_one.trans hΓ).le hcof
    (diagonal_coordinates_of_countable_total_dual hs hnot htotal hΓ) hX

end ThesisCommon.UncountableSchauderSum
