import ThesisCommon.Analysis.DecomposableL1Operators
import ThesisCommon.Analysis.L1OperatorLattice

/-! Positivity can be checked on every piece of an actual L1 direct sum. -/
noncomputable section
open MeasureTheory Filter
open scoped Function ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem lebesgueL1Restrict_nonneg (s : Set X) (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    0 ≤ lebesgueLpRestrict (𝕜 := ℝ) s f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [lebesgueLpRestrict_coe (𝕜 := ℝ) s f,
    ae_restrict_of_ae ((Lp.coeFn_nonneg f).mpr hf)] with x he hx
  rwa [he]

theorem decomposableL1Operator_nonneg (s : I → Set X)
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    (A : ∀ i, Lp ℝ 1 (μ.restrict (s i)) →L[ℝ] Lp ℝ 1 ν)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (hpos : ∀ i, 0 ≤ A i) :
    0 ≤ decomposableL1Operator s hμ A C hC hA := by
  intro f hf
  change 0 ≤ ∑' i, A i (lebesgueLpRestrict (𝕜 := ℝ) (s i) f)
  exact tsum_nonneg fun i => hpos i _ (lebesgueL1Restrict_nonneg (s i) f hf)

theorem lOneOperator_nonneg_of_decomposable_pieces (s : I → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hpos : ∀ i, 0 ≤ T.comp
      (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i)).toContinuousLinearMap) : 0 ≤ T := by
  let A := fun i => T.comp (lebesgueLpExtend (𝕜 := ℝ) (s i) (hs i)).toContinuousLinearMap
  have hA : ∀ i, ‖A i‖ ≤ ‖T‖ := fun i =>
    (T.opNorm_comp_le _).trans ((mul_le_mul_of_nonneg_left
      (lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1) (s i) (hs i)).norm_toContinuousLinearMap_le
      (norm_nonneg T)).trans_eq (mul_one _))
  rw [decomposableL1Operator_unique s hs hd hμ A ‖T‖ (norm_nonneg T) hA T (fun _ => rfl)]
  exact decomposableL1Operator_nonneg s hμ A ‖T‖ (norm_nonneg T) hA hpos

end ThesisCommon
