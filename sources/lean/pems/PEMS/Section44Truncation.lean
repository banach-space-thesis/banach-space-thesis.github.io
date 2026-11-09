import PEMS.Section44Decomposition
import PEMS.L1WeakNoncompactness
import PEMS.L1WeakNoncompactnessModulus
import ThesisCommon.Analysis.IntegralKernelApproximation
import ThesisCommon.Analysis.KernelCutBound

/-! The two estimates for a single truncation threshold on all pieces of the
signed §4.4 decomposition. All truncations use the specified kernels. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped ENNReal Function Classical ThesisCommon.PositiveOperatorOrder

namespace PEMS.Section44Decomposition

set_option maxHeartbeats 1500000

variable {I X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {T : LOne ℝ μ →L[ℝ] LOne ℝ ν} (D : Section44Decomposition I T)
variable (Θ : Set Y) (hΘ : MeasurableSet Θ) [IsFiniteMeasure (ν.restrict Θ)]

local instance finitePiece (i : I) : IsFiniteMeasure (μ.restrict (D.partition.piece i)) :=
  D.partition.finitePiece i

local instance sigmaFiniteSupport (i : I) : SigmaFinite (ν.restrict (D.support i)) :=
  D.sigmaFinite_support i

def positiveSingularPiece (i : I) := (D.outputExtend i).comp |D.singularPart i|
def positiveIntegralPiece (i : I) := (D.outputExtend i).comp |D.integralPart i|

theorem positive_piece_eq (i : I) :
    |T|.comp (D.partition.includePiece i) =
      D.positiveSingularPiece i + D.positiveIntegralPiece i := by
  rw [D.abs_piece i, ContinuousLinearMap.comp_add]
  rfl

private theorem positive_piece_nonneg (i : I) :
    0 ≤ |T|.comp (D.partition.includePiece i) :=
  fun f hf => (abs_nonneg T) _ (lebesgueL1Extend_nonneg _ (D.partition.measurable i) f hf)

theorem positiveSingularPiece_nonneg (i : I) : 0 ≤ D.positiveSingularPiece i :=
  lebesgueL1Extend_comp_nonneg _ _ (abs_nonneg _)

theorem positiveIntegralPiece_nonneg (i : I) : 0 ≤ D.positiveIntegralPiece i :=
  lebesgueL1Extend_comp_nonneg _ _ (abs_nonneg _)

theorem positiveSingularPiece_singular (i : I) : IsSingularOperator (D.positiveSingularPiece i) := by
  apply section44_extend_singular _ _ _ (abs_nonneg _)
  intro K hK
  simpa only [abs_abs] using D.singular i K hK

theorem positiveIntegralPiece_kernel (i : I) :
    IsIntegralKernel (fun z => |D.kernel i z|) (D.positiveIntegralPiece i) := by
  have heq : (univ ×ˢ D.support i).indicator (fun z => |D.kernel i z|) =
      fun z => |D.kernel i z| := by
    funext z
    by_cases h : z.2 ∈ D.support i
    · simp [h]
    · obtain ⟨x, y⟩ := z
      simp [h, D.kernel_zero_off i x y h]
  simpa only [heq] using section44_kernel_extend (D.support i)
    (D.measurable_support i) (D.represents i).abs

def localizedKernel (i : I) :
    IsIntegralKernel (fun z => |D.kernel i z|)
      ((lebesgueLpRestrict (𝕜 := ℝ) Θ).comp (D.positiveIntegralPiece i)) :=
  section44_kernel_restrict (D.positiveIntegralPiece_kernel i) Θ

include hΘ in
theorem localizedIntegralPart_eq (i : I) :
    localizedIntegralPart Θ (|T|.comp (D.partition.includePiece i)) =
      (lebesgueLpRestrict (𝕜 := ℝ) Θ).comp (D.positiveIntegralPiece i) := by
  rw [localizedIntegralPart, D.positive_piece_eq i, ContinuousLinearMap.comp_add, map_add,
    (integralBandProjection_eq_zero_iff _).mpr (section44_restrict_singular
      (D.positiveSingularPiece_singular i) (D.positiveSingularPiece_nonneg i) Θ hΘ),
    integralBandProjection_eq_self ⟨_, D.localizedKernel Θ i⟩, zero_add]

def residualPiece (i : I) (n : ℕ) :=
  (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
    (boundedKernelApproximation (D.localizedKernel Θ i) n)

def tailPiece (i : I) (n : ℕ) :=
  |T|.comp (D.partition.includePiece i) - D.residualPiece Θ hΘ i n

theorem tailPiece_eq (i : I) (n : ℕ) :
    D.tailPiece Θ hΘ i n = D.positiveSingularPiece i +
      (lpCutL Θᶜ hΘ.compl).comp (D.positiveIntegralPiece i) +
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
        ((D.localizedKernel Θ i).truncatedOperator n) := by
  rw [tailPiece, D.positive_piece_eq i, residualPiece]
  change _ - (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
    ((lebesgueLpRestrict (𝕜 := ℝ) Θ).comp (D.positiveIntegralPiece i) -
      (D.localizedKernel Θ i).truncatedOperator n) = _
  let E := (lebesgueLpExtend (𝕜 := ℝ) (μ := ν) (p := 1) (E := ℝ) Θ hΘ).toContinuousLinearMap
  let K := D.positiveIntegralPiece i
  let P := (lebesgueLpRestrict (𝕜 := ℝ) (μ := ν) (p := 1) (E := ℝ) Θ)
  let H := (D.localizedKernel Θ i).truncatedOperator n
  have heq : K - E.comp (P.comp K) = (lpCutL Θᶜ hΘ.compl).comp K := by
    have hh := congrArg (fun L => L - E.comp (P.comp K)) (lOne_localized_decomposition K Θ hΘ)
    change (lpCutL Θᶜ hΘ.compl).comp K + E.comp (P.comp K) - E.comp (P.comp K) =
      K - E.comp (P.comp K) at hh
    simpa only [add_sub_cancel_right] using hh.symm
  change D.positiveSingularPiece i + K - E.comp (P.comp K - H) =
    D.positiveSingularPiece i + (lpCutL Θᶜ hΘ.compl).comp K + E.comp H
  rw [ContinuousLinearMap.comp_sub]
  calc
    _ = D.positiveSingularPiece i + (K - E.comp (P.comp K)) + E.comp H := by abel
    _ = _ := by rw [heq]

theorem tailPiece_nonneg (i : I) (n : ℕ) : 0 ≤ D.tailPiece Θ hΘ i n := by
  rw [D.tailPiece_eq Θ hΘ i n]
  have h : ∀ z, 0 ≤ truncatedKernel (n : ℝ) (fun z => |D.kernel i z|) z :=
    fun z => indicator_nonneg (fun _ _ => abs_nonneg _) z
  have hk := (D.localizedKernel Θ i).truncatedOperator_represents n
  exact add_nonneg (add_nonneg (D.positiveSingularPiece_nonneg i)
    (positive_outputCut_nonneg (D.positiveIntegralPiece_nonneg i) Θᶜ hΘ.compl))
    (lebesgueL1Extend_comp_nonneg Θ hΘ (hk.positive_of_nonneg_ae (Eventually.of_forall h)))

theorem residualPiece_nonneg (i : I) (n : ℕ) : 0 ≤ D.residualPiece Θ hΘ i n := by
  apply lebesgueL1Extend_comp_nonneg
  apply (isIntegralKernel_boundedKernelApproximation (D.localizedKernel Θ i) n).positive_of_nonneg_ae
  exact Eventually.of_forall fun z => by
    by_cases h : z ∈ {w | (n : ℝ) ≤ ‖|D.kernel i w|‖}
    · simp only [truncatedKernel, indicator_of_mem h, sub_self, le_refl]
    · simpa only [truncatedKernel, indicator_of_notMem h, Pi.zero_apply, sub_zero] using
        abs_nonneg (D.kernel i z)

theorem norm_tailPiece_le (i : I) (n : ℕ) : ‖D.tailPiece Θ hΘ i n‖ ≤ ‖T‖ := by
  have hle : D.tailPiece Θ hΘ i n ≤ |T|.comp (D.partition.includePiece i) :=
    sub_le_self _ (D.residualPiece_nonneg Θ hΘ i n)
  apply le_trans _ (D.partition.norm_comp_piece_le |T| i |>.trans_eq (norm_abs_lOneOperator T))
  apply norm_le_norm_of_abs_le_abs
  simpa only [abs_of_nonneg (D.tailPiece_nonneg Θ hΘ i n),
    abs_of_nonneg (D.positive_piece_nonneg i)] using hle

def tailOperator (n : ℕ) : LOne ℝ μ →L[ℝ] LOne ℝ ν :=
  decomposableL1Operator D.partition.piece D.partition.sum_restrict
    (fun i => D.tailPiece Θ hΘ i n) ‖T‖ (norm_nonneg T) (fun i => D.norm_tailPiece_le Θ hΘ i n)

theorem tailOperator_comp (n : ℕ) (i : I) :
    (D.tailOperator Θ hΘ n).comp (D.partition.includePiece i) = D.tailPiece Θ hΘ i n := by
  ext f : 1
  exact decomposableL1Operator_extend D.partition.piece D.partition.measurable
    D.partition.disjoint D.partition.sum_restrict (fun j => D.tailPiece Θ hΘ j n) ‖T‖
    (norm_nonneg T) (fun j => D.norm_tailPiece_le Θ hΘ j n) i f

theorem norm_tailOperator_le (n : ℕ) : ‖D.tailOperator Θ hΘ n‖ ≤ ‖T‖ :=
  (D.partition.norm_le_iff_pieces _ (norm_nonneg T)).mpr fun i => by
    rw [D.tailOperator_comp Θ hΘ n i]
    exact D.norm_tailPiece_le Θ hΘ i n

theorem residualPiece_apply_bound (i : I) (n : ℕ)
    (f : LOne ℝ (μ.restrict (D.partition.piece i))) :
    ∀ᵐ y ∂ν, ‖D.residualPiece Θ hΘ i n f y‖ ≤ (n : ℝ) * ‖f‖ := by
  let A := boundedKernelApproximation (D.localizedKernel Θ i) n
  have hk := isIntegralKernel_boundedKernelApproximation (D.localizedKernel Θ i) n
  have ha := hk.apply_norm_le_of_bound (C := (n : ℝ)) (by
    simpa only [max_eq_left (Nat.cast_nonneg n)] using
      (Eventually.of_forall (f := ae ((μ.restrict (D.partition.piece i)).prod (ν.restrict Θ)))
        (norm_sub_truncatedKernel_le (n : ℝ) (fun z => |D.kernel i z|)))) f
  filter_upwards [lebesgueLpExtend_coe (𝕜 := ℝ) Θ hΘ (A f), (ae_restrict_iff' hΘ).mp ha]
    with y hy ha
  change ‖lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (A f) y‖ ≤ _
  rw [hy]
  by_cases hm : y ∈ Θ
  · simpa only [indicator_of_mem hm] using ha hm
  · simp only [indicator_of_notMem hm, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg n) (norm_nonneg f)

theorem norm_cut_residualPiece_le (i : I) (n : ℕ) {B : Set Y}
    (hB : MeasurableSet B) (hfin : ν B < ⊤) :
    ‖(lpCutL (Θᶜ ∪ B) (hΘ.compl.union hB)).comp (D.residualPiece Θ hΘ i n)‖ ≤
      (n : ℝ) * (ν B).toReal := by
  have heq : (lpCutL (Θᶜ ∪ B) (hΘ.compl.union hB)).comp (D.residualPiece Θ hΘ i n) =
      (lpCutL B hB).comp (D.residualPiece Θ hΘ i n) := by
    ext f : 1
    let A := boundedKernelApproximation (D.localizedKernel Θ i) n
    apply Lp.ext
    filter_upwards [lpCut_coe (Θᶜ ∪ B) (hΘ.compl.union hB) (D.residualPiece Θ hΘ i n f),
      lpCut_coe B hB (D.residualPiece Θ hΘ i n f), lebesgueLpExtend_coe (𝕜 := ℝ) Θ hΘ (A f)]
      with y h₁ h₂ h₃
    change lpCut (Θᶜ ∪ B) (hΘ.compl.union hB) (D.residualPiece Θ hΘ i n f) y =
      lpCut B hB (D.residualPiece Θ hΘ i n f) y
    rw [h₁, h₂]
    change (Θᶜ ∪ B).indicator (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (A f)) y =
      B.indicator (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (A f)) y
    by_cases hy : y ∈ Θ <;> by_cases hb : y ∈ B <;> simp [hy, hb, h₃]
  rw [heq]
  exact norm_lOneCut_comp_le_of_range_bound _ (Nat.cast_nonneg n)
    (D.residualPiece_apply_bound Θ hΘ i n) B hB hfin

theorem cut_norm_le_tail (n : ℕ) {B : Set Y} (hB : MeasurableSet B)
    (hfin : ν B < ⊤) :
    cutOperatorNorm |T| (Θᶜ ∪ B) ≤ ‖D.tailOperator Θ hΘ n‖ + (n : ℝ) * (ν B).toReal := by
  rw [cutOperatorNorm_eq _ _ (hΘ.compl.union hB)]
  apply (D.partition.norm_le_iff_pieces _
    (add_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg n) ENNReal.toReal_nonneg))).mpr
  intro i
  let C : LOne ℝ ν →L[ℝ] LOne ℝ ν := lpCutL (Θᶜ ∪ B) (hΘ.compl.union hB)
  have hs : |T|.comp (D.partition.includePiece i) =
      D.tailPiece Θ hΘ i n + D.residualPiece Θ hΘ i n := (sub_add_cancel _ _).symm
  change ‖(C.comp |T|).comp (D.partition.includePiece i)‖ ≤ _
  rw [ContinuousLinearMap.comp_assoc, hs, ContinuousLinearMap.comp_add]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (D.norm_cut_residualPiece_le Θ hΘ i n hB hfin)
  rw [← D.tailOperator_comp Θ hΘ n i]
  exact ((C.opNorm_comp_le _).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (norm_lpCutL_le (Θᶜ ∪ B) (hΘ.compl.union hB)) (norm_nonneg _))).trans
        (D.partition.norm_comp_piece_le _ i)

theorem alpha_le_tail (n : ℕ) : alphaTheta T Θ ≤ ‖D.tailOperator Θ hΘ n‖ := by
  rw [← alphaTheta_abs T Θ hΘ]
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / ((n : ℝ) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  apply (alphaTheta_le_smallSetSup |T| Θ hΘ hδ).trans
  unfold smallSetSup
  apply csSup_le
  · exact ⟨_, ∅, MeasurableSet.empty, empty_subset _,
      by simpa using ENNReal.ofReal_pos.mpr hδ, rfl⟩
  rintro _ ⟨B, hB, _, hlt, rfl⟩
  have hfin := hlt.trans ENNReal.ofReal_lt_top
  have hb : (ν B).toReal < δ := by
    simpa only [ENNReal.toReal_ofReal hδ.le] using
      (ENNReal.toReal_lt_toReal hfin.ne ENNReal.ofReal_ne_top).mpr hlt
  have hprod : (n : ℝ) * δ ≤ ε := by
    have hd : δ * ((n : ℝ) + 1) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith [hδ.le]
  exact (D.cut_norm_le_tail Θ hΘ n hB hfin).trans
    (add_le_add_left ((mul_le_mul_of_nonneg_left hb.le (Nat.cast_nonneg n)).trans hprod) _)

theorem exists_tail_le_smallSetSup (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, ‖D.tailOperator Θ hΘ n‖ ≤ smallSetSup |T| Θ δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * ‖T‖ / δ) 0)
  have hnpos : 0 < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hsize : 2 * ‖T‖ / (n : ℝ) < δ := by
    apply (div_lt_iff₀ hnpos).mpr
    nlinarith [(div_lt_iff₀ hδ).mp ((le_max_left _ _).trans_lt hn)]
  refine ⟨n, (D.partition.norm_le_iff_pieces _ (smallSetSup_bounds |T| Θ hΘ δ hδ).1).mpr ?_⟩
  intro i
  have hki := D.localizedIntegralPart_eq Θ hΘ i
  have hnorm : ‖localizedIntegralPart Θ (|T|.comp (D.partition.includePiece i))‖ ≤ ‖T‖ :=
    (norm_localizedIntegralPart_le Θ _).trans
      ((D.partition.norm_comp_piece_le |T| i).trans_eq (norm_abs_lOneOperator T))
  have haux (K : LOne ℝ (μ.restrict (D.partition.piece i)) →L[ℝ] LOne ℝ (ν.restrict Θ))
      (hK : localizedIntegralPart Θ (|T|.comp (D.partition.includePiece i)) = K)
      (hk : IsIntegralKernel (fun z => |D.kernel i z|) K) :
      ‖localizedIntegralRemainder Θ hΘ (|T|.comp (D.partition.includePiece i)) +
        (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp (hk.truncatedOperator n)‖ ≤
          smallSetSup |T| Θ δ := by
    subst K
    exact localized_truncation_le_smallSetSup_of_input_contraction |T|
      (D.partition.includePiece i) (D.partition.norm_includePiece_le i)
      (D.positive_piece_nonneg i) Θ hΘ hk (fun _ => abs_nonneg _)
      (norm_nonneg T) hnorm hδ hnpos hsize
  have h := haux _ hki (D.localizedKernel Θ i)
  rw [localizedIntegralRemainder, hki] at h
  rw [D.tailOperator_comp Θ hΘ n i, tailPiece, residualPiece]
  unfold boundedKernelApproximation
  rw [ContinuousLinearMap.comp_sub]
  convert h using 2
  abel

theorem alpha_eq_inf_tail :
    alphaTheta T Θ = sInf (range (fun n : ℕ => ‖D.tailOperator Θ hΘ n‖)) := by
  apply le_antisymm
  · apply le_csInf (range_nonempty _)
    rintro _ ⟨n, rfl⟩
    exact D.alpha_le_tail Θ hΘ n
  · rw [← alphaTheta_abs T Θ hΘ]
    unfold alphaTheta
    apply le_csInf
    · exact ⟨_, 1, zero_lt_one, rfl⟩
    rintro _ ⟨δ, hδ, rfl⟩
    obtain ⟨n, hn⟩ := D.exists_tail_le_smallSetSup Θ hΘ δ hδ
    exact (csInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact norm_nonneg _⟩ (mem_range_self n)).trans hn

end PEMS.Section44Decomposition
