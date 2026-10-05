import Sigma.ComplexDesiredProperty
import Sigma.PointCoding
import ThesisCommon.Analysis.NormingSequence

/-! Interleaving real and imaginary parts of a complex norming sequence gives
a norming sequence for the same normed space with scalars restricted to ℝ. -/
noncomputable section
namespace SigmaNonprimarity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- A single real sequence containing both scalar components of every functional. -/
def complexToRealNormingSequence (e : ℕ → E →L[ℂ] ℂ) (k : ℕ) : E →L[ℝ] ℝ :=
  if (pointCode.symm k).2 then
    Complex.imCLM.comp ((e (pointCode.symm k).1).restrictScalars ℝ)
  else
    Complex.reCLM.comp ((e (pointCode.symm k).1).restrictScalars ℝ)

@[simp] theorem complexToRealNormingSequence_real (e : ℕ → E →L[ℂ] ℂ) (n : ℕ) (x : E) :
    complexToRealNormingSequence e (pointCode (n,false)) x = (e n x).re := by
  simp [complexToRealNormingSequence]

@[simp] theorem complexToRealNormingSequence_imag (e : ℕ → E →L[ℂ] ℂ) (n : ℕ) (x : E) :
    complexToRealNormingSequence e (pointCode (n,true)) x = (e n x).im := by
  simp [complexToRealNormingSequence]

theorem complexToRealNormingSequence_norm_le (e : ℕ → E →L[ℂ] ℂ) (k : ℕ) :
    ‖complexToRealNormingSequence e k‖ ≤ ‖e (pointCode.symm k).1‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rcases h : pointCode.symm k with ⟨n,bit⟩
  cases bit
  · change ‖(complexToRealNormingSequence e k) x‖ ≤ ‖e n‖ * ‖x‖
    simpa only [complexToRealNormingSequence,h,Bool.false_eq_true,ite_false,
      ContinuousLinearMap.comp_apply,
      Complex.reCLM_apply,Real.norm_eq_abs] using
        (Complex.abs_re_le_norm (e n x)).trans ((e n).le_opNorm x)
  · change ‖(complexToRealNormingSequence e k) x‖ ≤ ‖e n‖ * ‖x‖
    simpa only [complexToRealNormingSequence,h,ite_true,
      ContinuousLinearMap.comp_apply,
      Complex.imCLM_apply,Real.norm_eq_abs] using
        (Complex.abs_im_le_norm (e n x)).trans ((e n).le_opNorm x)

/-- The real norming constant is at least half the complex norming constant. -/
theorem complexToRealNormingSequence_isCNorming {e : ℕ → E →L[ℂ] ℂ} {c : ℝ}
    (he : IsComplexCNorming e c) :
    ThesisCommon.IsCNorming (complexToRealNormingSequence e) (c/2) := by
  have hunit (k : ℕ) : ‖complexToRealNormingSequence e k‖ ≤ 1 :=
    (complexToRealNormingSequence_norm_le e k).trans (he.2.2.1 _)
  refine ⟨half_pos he.1,by linarith [he.2.1],hunit,?_⟩
  intro x
  have hbdd := ThesisCommon.evaluations_bddAbove (complexToRealNormingSequence e) hunit x
  have hre (n : ℕ) :
      |(e n x).re| ≤ ⨆ k, |complexToRealNormingSequence e k x| := by
    simpa only [complexToRealNormingSequence_real] using
      (le_ciSup hbdd (pointCode (n,false)))
  have him (n : ℕ) :
      |(e n x).im| ≤ ⨆ k, |complexToRealNormingSequence e k x| := by
    simpa only [complexToRealNormingSequence_imag] using
      (le_ciSup hbdd (pointCode (n,true)))
  have hnorm (n : ℕ) :
      ‖e n x‖ ≤ 2 * (⨆ k, |complexToRealNormingSequence e k x|) :=
    (Complex.norm_le_abs_re_add_abs_im (e n x)).trans (by linarith [hre n,him n])
  have hsup : (⨆ n, ‖e n x‖) ≤ 2 * (⨆ k, |complexToRealNormingSequence e k x|) :=
    ciSup_le hnorm
  linarith [he.2.2.2 x]

theorem complexToRealNormingSequence_isNorming {e : ℕ → E →L[ℂ] ℂ}
    (he : IsComplexNorming e) :
    ThesisCommon.IsNorming (complexToRealNormingSequence e) := by
  obtain ⟨c,hc⟩ := he
  exact ⟨c/2,complexToRealNormingSequence_isCNorming hc⟩

theorem exists_real_norming_of_complex_norming
    (h : ∃ e : ℕ → E →L[ℂ] ℂ, IsComplexNorming e) :
    ∃ r : ℕ → E →L[ℝ] ℝ, ThesisCommon.IsNorming r := by
  obtain ⟨e,he⟩ := h
  exact ⟨complexToRealNormingSequence e,complexToRealNormingSequence_isNorming he⟩

end SigmaNonprimarity

