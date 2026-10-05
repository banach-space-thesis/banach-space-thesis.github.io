import ThesisCommon.Analysis.ComplexL1KernelDiagonal
import ThesisCommon.Analysis.ComplexL1CutColumns
import ThesisCommon.Analysis.L1SignedDiagonalCompression

/-! Actual two-sided local compression of every bounded complex L1 operator
to its measurable diagonal multiplier. Both real columns are controlled by one
finite variation kernel; the estimate concerns the full operator norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [StandardBorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]

def complexL1DiagonalMultiplier (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ :=
  lpBoundedMultiplier (complexL1Diagonal T)
    (complexL1Diagonal_measurable T).aestronglyMeasurable (2 * ‖T‖)
    (Eventually.of_forall (complexL1Diagonal_norm_le T))

theorem complexL1DiagonalMultiplier_coe (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ)
    (f : Lp ℂ 1 μ) :
    complexL1DiagonalMultiplier T f =ᵐ[μ] fun x => complexL1Diagonal T x * f x :=
  lpBoundedMultiplier_coe _ _ _ _ f

@[simp] theorem complexL1RealColumn_diagonalMultiplier
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    complexL1RealColumn (complexL1DiagonalMultiplier T) =
      realL1SignedDiagonalMultiplier (complexL1RealColumn T) := by
  ext f : 1
  apply Lp.ext
  filter_upwards [complexL1RealColumn_multiplier_coe (complexL1Diagonal T)
      (complexL1Diagonal_measurable T).aestronglyMeasurable (2 * ‖T‖)
      (Eventually.of_forall (complexL1Diagonal_norm_le T)) f,
    realL1SignedDiagonalMultiplier_coe (complexL1RealColumn T) f] with x hr hd
  change (complexL1RealColumn (lpBoundedMultiplier (complexL1Diagonal T) _ _ _) f) x = _
  rw [hr, hd, complexL1Diagonal_re]

@[simp] theorem complexL1ImagColumn_diagonalMultiplier
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    complexL1ImagColumn (complexL1DiagonalMultiplier T) =
      realL1SignedDiagonalMultiplier (complexL1ImagColumn T) := by
  ext f : 1
  apply Lp.ext
  filter_upwards [complexL1ImagColumn_multiplier_coe (complexL1Diagonal T)
      (complexL1Diagonal_measurable T).aestronglyMeasurable (2 * ‖T‖)
      (Eventually.of_forall (complexL1Diagonal_norm_le T)) f,
    realL1SignedDiagonalMultiplier_coe (complexL1ImagColumn T) f] with x hr hd
  change (complexL1ImagColumn (lpBoundedMultiplier (complexL1Diagonal T) _ _ _) f) x = _
  rw [hr, hd, complexL1Diagonal_im]

theorem norm_complexL1Diagonal_compression_le
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (D : Set X) (hD : MeasurableSet D)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ x ∈ D, (complexL1VariationKernel T x).real (D \ {x}) ≤ ε) :
    ‖(lpCutL D hD).comp ((T - complexL1DiagonalMultiplier T).comp (lpCutL D hD))‖ ≤
      8 * ε := by
  have hr : ∀ x ∈ D,
      ((realL1ReverseKernel (complexL1RealColumn T)).variationKernel x).real
        (D \ {x}) ≤ ε := by
    intro x hx
    have h := hb x hx
    rw [complexL1VariationKernel_real] at h
    exact (le_add_of_nonneg_right measureReal_nonneg).trans h
  have hi : ∀ x ∈ D,
      ((realL1ReverseKernel (complexL1ImagColumn T)).variationKernel x).real
        (D \ {x}) ≤ ε := by
    intro x hx
    have h := hb x hx
    rw [complexL1VariationKernel_real] at h
    exact (le_add_of_nonneg_left measureReal_nonneg).trans h
  have hR := norm_realL1Diagonal_compression_le (complexL1RealColumn T) D hD ε hε hr
  have hI := norm_realL1Diagonal_compression_le (complexL1ImagColumn T) D hD ε hε hi
  calc
    _ ≤ 2 * ‖complexL1RealColumn ((lpCutL D hD).comp
          ((T - complexL1DiagonalMultiplier T).comp (lpCutL D hD)))‖ +
        2 * ‖complexL1ImagColumn ((lpCutL D hD).comp
          ((T - complexL1DiagonalMultiplier T).comp (lpCutL D hD)))‖ :=
      norm_complexL1Operator_le_columns _
    _ = 2 * ‖(lpCutL D hD).comp ((complexL1RealColumn T -
          realL1SignedDiagonalMultiplier (complexL1RealColumn T)).comp (lpCutL D hD))‖ +
        2 * ‖(lpCutL D hD).comp ((complexL1ImagColumn T -
          realL1SignedDiagonalMultiplier (complexL1ImagColumn T)).comp (lpCutL D hD))‖ := by
      rw [complexL1RealColumn_cut, complexL1ImagColumn_cut,
        complexL1RealColumn_sub, complexL1ImagColumn_sub,
        complexL1RealColumn_diagonalMultiplier, complexL1ImagColumn_diagonalMultiplier]
    _ ≤ 2 * (2 * ε) + 2 * (2 * ε) := add_le_add
      (mul_le_mul_of_nonneg_left hR (by norm_num))
      (mul_le_mul_of_nonneg_left hI (by norm_num))
    _ = _ := by ring

theorem exists_complexL1_small_diagonal_compression
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (hμ : μ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ,
      (S = T ∨ S = ContinuousLinearMap.id ℂ _ - T) ∧
      ∃ (D : Set X) (hD : MeasurableSet D), 0 < μ D ∧
        (∀ x ∈ D, (1 / 2 : ℝ) ≤ ‖complexL1Diagonal S x‖) ∧
        ‖(lpCutL D hD).comp ((S - complexL1DiagonalMultiplier S).comp (lpCutL D hD))‖ ≤ ε := by
  obtain ⟨S, hS, D, hD, hd, hdiag, hsmall⟩ :=
    exists_complexL1Diagonal_localization T hμ (show 0 < ε / 8 by positivity)
  refine ⟨S, hS, D, hD, hd, hdiag, ?_⟩
  exact (norm_complexL1Diagonal_compression_le S D hD (ε / 8) (by positivity)
    (fun x hx => (hsmall x hx).le)).trans_eq (by ring)

end ThesisCommon
