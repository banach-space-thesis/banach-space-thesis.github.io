import PEMS.Section44Truncation
import PEMS.Section44Adjoint

/-! Proposition 4.17 for each decomposition and kernel constructed in §4.4. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped ENNReal Function Classical ThesisCommon.PositiveOperatorOrder

namespace PEMS

set_option maxHeartbeats 1500000

variable {I X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {T : LOne ℝ μ →L[ℝ] LOne ℝ ν} (D : Section44Decomposition I T)
variable (Θ : Set Y) (hΘ : MeasurableSet Θ) [IsFiniteMeasure (ν.restrict Θ)]

local instance finitePiece (i : I) : IsFiniteMeasure (μ.restrict (D.partition.piece i)) :=
  D.partition.finitePiece i

local instance sigmaFiniteSupport (i : I) : SigmaFinite (ν.restrict (D.support i)) :=
  D.sigmaFinite_support i

private theorem section44_cut_extend (A B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (f : LOne ℝ (ν.restrict A)) :
    lpCut B hB (lebesgueLpExtend (𝕜 := ℝ) A hA f) =
      lebesgueLpExtend (𝕜 := ℝ) A hA (lpCut B hB f) := by
  apply Lp.ext
  filter_upwards [lpCut_coe B hB (lebesgueLpExtend (𝕜 := ℝ) A hA f),
    lebesgueLpExtend_coe (𝕜 := ℝ) A hA f,
    lebesgueLpExtend_coe (𝕜 := ℝ) A hA (lpCut B hB f),
    (ae_restrict_iff' hA).mp (lpCut_coe B hB f)] with y h₁ h₂ h₃ h₄
  rw [h₁, h₃]
  by_cases hy : y ∈ A <;> by_cases hb : y ∈ B <;> simp [hy, hb, h₂, h₄]

private theorem section44_setIntegral_of_support (A B : Set Y) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (f : Y → ℝ) (hf : ∀ y ∉ A, f y = 0) :
    (∫ y in B, f y ∂ν.restrict A) = ∫ y in B, f y ∂ν := by
  rw [Measure.restrict_restrict hB, inter_comm, ← Measure.restrict_restrict hA, ← integral_indicator hA]
  congr 1
  funext y
  by_cases hy : y ∈ A <;> simp [hy, hf]

namespace Section44Decomposition

def singularAdjointMass : X → ℝ :=
  D.partition.adjointDensity |D.S| (abs_nonneg D.S)

theorem singularAdjointMass_pairing :
    linftyL1Pairing μ (D.partition.adjointOne |D.S| (abs_nonneg D.S)) =
      banachAdjoint |D.S| (linftyL1Pairing ν (linftyOne ν)) :=
  D.partition.adjointOne_pairing |D.S| (abs_nonneg D.S)

theorem singularAdjointMass_isLUB :
    let one := linftyL1Pairing ν (linftyOne ν)
    IsLUB (banachAdjoint D.S '' Icc (-one) one)
      (linftyL1Pairing μ (D.partition.adjointOne |D.S| (abs_nonneg D.S))) := by
  rw [D.singularAdjointMass_pairing]
  exact section44_adjoint_modulus_at_one D.S

theorem singularAdjointMass_piece (i : I) :
    D.singularAdjointMass =ᵐ[μ.restrict (D.partition.piece i)]
      positiveAdjointOneDensity (D.positiveSingularPiece i) (D.positiveSingularPiece_nonneg i) := by
  have h : |D.S|.comp (D.partition.includePiece i) = D.positiveSingularPiece i := by
    calc
      _ = |D.S.comp (D.partition.includePiece i)| :=
        (section44_abs_comp_extend (D.partition.piece i) (D.partition.measurable i) D.S).symm
      _ = |(D.outputExtend i).comp (D.singularPart i)| :=
        congrArg abs (D.assemble_comp D.singularPart D.norm_singular_le i)
      _ = _ := section44_abs_extend_comp (D.support i) (D.measurable_support i) _
  exact (D.partition.adjointDensity_piece |D.S| (abs_nonneg D.S) i).trans
    (Eventually.of_forall (congrFun (positiveAdjointOneDensity_congr _ _ h)))

theorem tailOperator_nonneg (n : ℕ) : 0 ≤ D.tailOperator Θ hΘ n := by
  intro f hf
  change 0 ≤ D.tailOperator Θ hΘ n f
  rw [tailOperator, decomposableL1Operator_apply]
  exact tsum_nonneg fun i => D.tailPiece_nonneg Θ hΘ i n _
    (lebesgueL1Restrict_nonneg (D.partition.piece i) f hf)

private def outsideMass (i : I) (x : X) : ℝ :=
  ∫ y in Θᶜ, |D.kernel i (x, y)| ∂ν.restrict (D.support i)

private def insideMass (i : I) (n : ℕ) (x : X) : ℝ :=
  ∫ y, truncatedKernel (n : ℝ) (fun z => |D.kernel i z|) (x, y) ∂ν.restrict Θ

private theorem outsideDensity (i : I) :
    positiveAdjointOneDensity ((lpCutL Θᶜ hΘ.compl).comp (D.positiveIntegralPiece i))
      (positive_outputCut_nonneg (D.positiveIntegralPiece_nonneg i) Θᶜ hΘ.compl)
        =ᵐ[μ.restrict (D.partition.piece i)] D.outsideMass Θ i := by
  let K := (lpCutL Θᶜ hΘ.compl).comp |D.integralPart i|
  have heq : (lpCutL Θᶜ hΘ.compl).comp (D.positiveIntegralPiece i) =
      (D.outputExtend i).comp K := by
    ext f : 1
    exact section44_cut_extend _ _ (D.measurable_support i) hΘ.compl (|D.integralPart i| f)
  have hK : 0 ≤ K := positive_outputCut_nonneg (abs_nonneg _) Θᶜ hΘ.compl
  rw [positiveAdjointOneDensity_congr _ (lebesgueL1Extend_comp_nonneg _ _ hK) heq]
  exact (positiveAdjointOneDensity_extend _ _ K hK).trans
    ((D.represents i).abs.positiveAdjointOneDensity_outputCut (abs_nonneg _) Θᶜ hΘ.compl)

private theorem tailDensity_piece (n : ℕ) (i : I) :
    D.partition.adjointDensity (D.tailOperator Θ hΘ n) (D.tailOperator_nonneg Θ hΘ n)
      =ᵐ[μ.restrict (D.partition.piece i)]
        (fun x => D.singularAdjointMass x + D.outsideMass Θ i x + D.insideMass Θ i n x) := by
  let U := D.tailOperator Θ hΘ n
  let P := D.positiveSingularPiece i
  let Q := (lpCutL Θᶜ hΘ.compl).comp (D.positiveIntegralPiece i)
  let R := (D.localizedKernel Θ i).truncatedOperator n
  have hP : 0 ≤ P := D.positiveSingularPiece_nonneg i
  have hQ : 0 ≤ Q := positive_outputCut_nonneg (D.positiveIntegralPiece_nonneg i) Θᶜ hΘ.compl
  have hk := (D.localizedKernel Θ i).truncatedOperator_represents n
  have hR : 0 ≤ R := hk.positive_of_nonneg_ae
    (Eventually.of_forall (indicator_nonneg (fun _ _ => abs_nonneg _)))
  have heq : U.comp (D.partition.includePiece i) =
      P + Q + (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp R :=
    (D.tailOperator_comp Θ hΘ n i).trans (D.tailPiece_eq Θ hΘ i n)
  have h := (D.partition.adjointDensity_piece U (D.tailOperator_nonneg Θ hΘ n) i).trans
    (Eventually.of_forall (congrFun (positiveAdjointOneDensity_congr _
      (add_nonneg (add_nonneg hP hQ) (lebesgueL1Extend_comp_nonneg Θ hΘ hR)) heq)))
  have hr := (positiveAdjointOne_coe R hR).symm.trans (hk.positiveAdjointOne_eq_column_ae hR)
  filter_upwards [h, positiveAdjointOneDensity_add_extend Θ hΘ (add_nonneg hP hQ) hR,
    positiveAdjointOneDensity_add hP hQ, D.singularAdjointMass_piece i, D.outsideDensity Θ hΘ i, hr]
    with x h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₂, h₃, ← h₄, h₅, h₆]
  rfl

include hΘ in
private theorem outsideMass_glued {x : X} {i : I} (hx : x ∈ D.partition.piece i) :
    D.outsideMass Θ i x = ∫ y in Θᶜ, |D.gluedKernel x y| ∂ν := by
  rw [outsideMass, section44_setIntegral_of_support (D.support i) Θᶜ
    (D.measurable_support i) hΘ.compl _ (fun y hy => by rw [D.kernel_zero_off i x y hy, abs_zero])]
  exact integral_congr_ae (Eventually.of_forall fun y => congrArg abs (D.gluedKernel_eq hx y).symm)

private theorem insideMass_glued {x : X} {i : I} (hx : x ∈ D.partition.piece i) (n : ℕ) :
    D.insideMass Θ i n x =
      ∫ y in Θ, |truncatedKernel (n : ℝ) (fun z => D.gluedKernel z.1 z.2) (x, y)| ∂ν := by
  apply integral_congr_ae
  filter_upwards with y
  change truncatedKernel (n : ℝ) (fun z => |D.kernel i z|) (x, y) =
    |truncatedKernel (n : ℝ) (fun z => D.gluedKernel z.1 z.2) (x, y)|
  rw [truncatedKernel_abs]
  simp only [truncatedKernel, indicator_apply, mem_setOf_eq, D.gluedKernel_eq hx y]

theorem norm_tailOperator_eq_essSup (n : ℕ) :
    ‖D.tailOperator Θ hΘ n‖ = essSup (fun x => D.singularAdjointMass x +
      (∫ y in Θᶜ, |D.gluedKernel x y| ∂ν) +
      (∫ y in Θ, |truncatedKernel (n : ℝ) (fun z => D.gluedKernel z.1 z.2) (x, y)| ∂ν)) μ := by
  let R := D.tailOperator Θ hΘ n
  let f (i : I) (x : X) := D.singularAdjointMass x + D.outsideMass Θ i x + D.insideMass Θ i n x
  have hmeas (i : I) : Measurable (f i) := by
    have h₁ := D.partition.measurable_adjointDensity |D.S| (abs_nonneg D.S)
    have h₂ : Measurable (D.outsideMass Θ i) :=
      ((D.represents i).abs.measurable.stronglyMeasurable.integral_prod_right'
        (ν := (ν.restrict (D.support i)).restrict Θᶜ)).measurable
    have h₃ : Measurable (D.insideMass Θ i n) := by
      have hm := measurable_truncatedKernel (D.localizedKernel Θ i).measurable (n : ℝ)
      exact (hm.stronglyMeasurable.integral_prod_right' (ν := ν.restrict Θ)).measurable
    exact (h₁.add h₂).add h₃
  have heq : (fun x => D.singularAdjointMass x +
      (∫ y in Θᶜ, |D.gluedKernel x y| ∂ν) +
      (∫ y in Θ, |truncatedKernel (n : ℝ) (fun z => D.gluedKernel z.1 z.2) (x, y)| ∂ν)) =
        D.partition.paste f := by
    funext x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (D.partition.covers ▸ mem_univ x)
    rw [D.partition.paste_eq f hi]
    dsimp [f]
    rw [D.outsideMass_glued Θ hΘ hi, D.insideMass_glued Θ hi n]
  refine (D.partition.norm_eq_essSup_adjointDensity R (D.tailOperator_nonneg Θ hΘ n)).trans ?_
  rw [heq]
  apply essSup_congr_ae
  let g := D.partition.adjointDensity R (D.tailOperator_nonneg Θ hΘ n)
  let p := D.partition.paste f
  have hg := D.partition.measurable_adjointDensity R (D.tailOperator_nonneg Θ hΘ n)
  have hp := D.partition.measurable_paste f hmeas
  have hm : MeasurableSet {x | g x = p x} := by
    have he : {x | g x = p x} = {x | g x ≤ p x} ∩ {x | p x ≤ g x} := by
      ext x
      exact le_antisymm_iff
    rw [he]
    exact (measurableSet_le hg hp).inter (measurableSet_le hp hg)
  apply (D.partition.ae_on_pieces hm).mpr
  exact fun i => (D.tailDensity_piece Θ hΘ n i).trans (D.partition.paste_ae f i).symm

end Section44Decomposition

omit [IsFiniteMeasure (ν.restrict Θ)] in
/-- Proposition 4.17, with every choice of the §4.4 construction. The
essential supremum is the norm of the nonnegative column-mass representative. -/
theorem proposition_4_17 (_hν : StrictlyLocalizable ν)
    (hTheta : MeasurableSet Θ) (hfinite : ν Θ < ⊤) :
    alphaTheta T Θ = sInf (range (fun n : ℕ =>
      essSup (fun x => D.singularAdjointMass x +
        (∫ y in Θᶜ, |D.gluedKernel x y| ∂ν) +
        (∫ y in Θ, |truncatedKernel (n : ℝ) (fun z => D.gluedKernel z.1 z.2) (x, y)| ∂ν)) μ)) := by
  letI := isFiniteMeasure_restrict.mpr hfinite.ne
  rw [D.alpha_eq_inf_tail Θ hTheta]
  simp only [D.norm_tailOperator_eq_essSup Θ hTheta]

end PEMS
