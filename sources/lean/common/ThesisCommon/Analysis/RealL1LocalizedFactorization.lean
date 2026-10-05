import ThesisCommon.Analysis.L1SignedDiagonalCompression
import ThesisCommon.Analysis.LpDiagonalCompressionFactorization

/-! Every real L1 operator or its complement factors the identity on an actual
positive-measure part. This is proved from reverse-kernel diagonal localization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [StandardBorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem exists_realL1Diagonal_large_set
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (hμ : μ ≠ 0) :
    ∃ S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ,
      (S = T ∨ S = ContinuousLinearMap.id ℝ _ - T) ∧
      ∃ A : Set X, MeasurableSet A ∧ 0 < μ A ∧
        ∀ x ∈ A, (1 / 2 : ℝ) ≤ ‖realL1Diagonal S x‖ := by
  let A : Set X := {x | (1 / 2 : ℝ) ≤ realL1Diagonal T x}
  let B : Set X := {x | (1 / 2 : ℝ) ≤ realL1Diagonal (ContinuousLinearMap.id ℝ _ - T) x}
  have hA : MeasurableSet A := measurableSet_le measurable_const (realL1Diagonal_measurable T)
  have hB : MeasurableSet B := measurableSet_le measurable_const (realL1Diagonal_measurable _)
  have hbnd (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (x : X)
      (hx : (1 / 2 : ℝ) ≤ realL1Diagonal S x) :
      (1 / 2 : ℝ) ≤ ‖realL1Diagonal S x‖ := hx.trans (le_abs_self _)
  by_cases ha : 0 < μ A
  · exact ⟨T, Or.inl rfl, A, hA, ha, fun x hx => hbnd T x hx⟩
  have haz : μ A = 0 := le_antisymm (le_of_not_gt ha) (zero_le _)
  have hb : 0 < μ B := by
    by_contra hn
    have hbz : μ B = 0 := le_antisymm (le_of_not_gt hn) (zero_le _)
    have haf : ∀ᵐ x ∂μ, x ∉ A := measure_eq_zero_iff_ae_notMem.mp haz
    have hbf : ∀ᵐ x ∂μ, x ∉ B := measure_eq_zero_iff_ae_notMem.mp hbz
    have hf : ∀ᵐ x ∂μ, False := by
      filter_upwards [haf, hbf, realL1Diagonal_add_complement T] with x hx hy he
      have hx' : realL1Diagonal T x < 1 / 2 := lt_of_not_ge hx
      have hy' : realL1Diagonal (ContinuousLinearMap.id ℝ _ - T) x < 1 / 2 := lt_of_not_ge hy
      linarith
    exact hμ (Measure.measure_univ_eq_zero.mp (by simpa only [ae_iff, not_false_eq_true,
      Set.setOf_true] using hf))
  exact ⟨ContinuousLinearMap.id ℝ _ - T, Or.inr rfl, B, hB, hb, fun x hx => hbnd _ x hx⟩

theorem exists_realL1_part_factorization
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (hμ : μ ≠ 0) :
    ∃ D : Set X, MeasurableSet D ∧ 0 < μ D ∧
      (FactorsIdentityWith T (Lp ℝ 1 (μ.restrict D)) 4 ∨
        FactorsIdentityWith (ContinuousLinearMap.id ℝ _ - T) (Lp ℝ 1 (μ.restrict D)) 4) := by
  obtain ⟨S, hS, A, hA, ha, hb⟩ := exists_realL1Diagonal_large_set T hμ
  obtain ⟨D, hDA, hD, hd, he⟩ := exists_kernel_offDiagonal_small_set
    (realL1ReverseKernel S).variationKernel μ hA ha (show (0 : ℝ) < 1 / 8 by norm_num)
  have hnorm := norm_realL1Diagonal_compression_le S D hD (1 / 8) (by norm_num)
    (fun x hx => (he x hx).le)
  have hfactor := factorsIdentityWith_of_lp_diagonal_compression S (realL1SignedDiagonalMultiplier S)
    (realL1Diagonal S) (realL1Diagonal_measurable S) (realL1SignedDiagonalMultiplier_coe S)
    D hD (fun x hx => hb x (hDA hx)) (by linarith)
  refine ⟨D, hD, hd, ?_⟩
  rcases hS with rfl | rfl
  · exact Or.inl hfactor
  · exact Or.inr hfactor

end ThesisCommon

