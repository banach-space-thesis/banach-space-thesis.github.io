import ThesisCommon.Analysis.CZeroFunctionalRows
import ThesisCommon.Analysis.CZeroPairedInsertion
import ThesisCommon.Analysis.CZeroStrongRows
import ThesisCommon.Analysis.QuantitativeNeumannInverse
import Mathlib.Topology.Sequences

/-! Paired point evaluations give a quantitative retraction onto a c₀
subcopy when the original columns nearly attain the contraction bound.
Sequential compactness is used only for the selected points of K. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [SeqCompactSpace K]

omit [SeqCompactSpace K] in
private theorem eval_norm_le (t : K) :
    ‖(ContinuousMap.evalCLM 𝕜 t : C(K, 𝕜) →L[𝕜] 𝕜)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using f.norm_coe_le_norm t

theorem exists_cZero_retraction_of_near_norming_evaluations
    (V : CZeroSum 𝕜 →L[𝕜] C(K, 𝕜)) (hV : ‖V‖ ≤ 1)
    (t : ℕ → K) (d : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδsmall : 2*δ < 1)
    (hd : ∀ n, 0 ≤ d n) (hd1 : ∀ n, d n ≤ 1)
    (hne : ∀ n, 1-δ ≤ d n)
    (hdiag : ∀ n, V (cZeroSingle n 1) (t n) = (d n : 𝕜)) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜,
      ∃ Q : C(K, 𝕜) →L[𝕜] CZeroSum 𝕜,
        Q.comp (V.comp A) = ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜) ∧
        ‖A‖ ≤ 1 ∧ ‖Q‖ ≤ (1-2*δ)⁻¹ := by
  obtain ⟨t₀, s, hs, ht⟩ := SeqCompactSpace.tendsto_subseq t
  let ψ (n : ℕ) : C(K, 𝕜) →L[𝕜] 𝕜 :=
    ((1/2 : ℝ) : 𝕜) • (ContinuousMap.evalCLM 𝕜 (t (s (2*n))) -
      ContinuousMap.evalCLM 𝕜 (t (s (2*n+1))))
  have hψ (n : ℕ) : ‖ψ n‖ ≤ 1 := by
    dsimp [ψ]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hh := norm_sub_le
      (ContinuousMap.evalCLM 𝕜 (t (s (2*n))) : C(K, 𝕜) →L[𝕜] 𝕜)
      (ContinuousMap.evalCLM 𝕜 (t (s (2*n+1))))
    have he := eval_norm_le (𝕜 := 𝕜) (t (s (2*n)))
    have ho := eval_norm_le (𝕜 := 𝕜) (t (s (2*n+1)))
    linarith
  have hzero : ∀ f, Tendsto (fun n => ψ n f) atTop (𝓝 0) := by
    intro f
    have hf := (f.continuous.tendsto t₀).comp ht
    have he : StrictMono (fun n : ℕ => 2*n) := by intro i j hij; dsimp; omega
    have ho : StrictMono (fun n : ℕ => 2*n+1) := by intro i j hij; dsimp; omega
    simpa only [ψ, Function.comp_def, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousMap.evalCLM_apply, smul_eq_mul,
      sub_self, mul_zero] using
      (tendsto_const_nhds (x := ((1/2 : ℝ) : 𝕜))).mul
        ((hf.comp he.tendsto_atTop).sub (hf.comp ho.tendsto_atTop))
  let Q := cZeroStrongRows ψ 1 zero_le_one hψ hzero
  let A := cZeroPairedInsertion (𝕜 := 𝕜) s hs
  have hA : ‖A‖ ≤ 1 := norm_cZeroPairedInsertion_le s hs
  have hQ : ‖Q‖ ≤ 1 := norm_cZeroStrongRows_le ..
  have hrow (n : ℕ) :
      ‖(ContinuousMap.evalCLM 𝕜 (t n)).comp V - cZeroCoordinate n‖ ≤ 2*δ := by
    apply cZero_functional_near_coordinate _ n
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul (eval_norm_le (t n)) hV (norm_nonneg V) zero_le_one).trans_eq (one_mul 1)))
      (hd n) (hd1 n) (hdiag n) (hne n)
  have herr (x : CZeroSum 𝕜) (n : ℕ) :
      ‖V (A x) (t n) - A x n‖ ≤ 2*δ*‖x‖ := by
    have hh := ((ContinuousMap.evalCLM 𝕜 (t n)).comp V -
      cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n).le_opNorm (A x)
    exact hh.trans ((mul_le_mul_of_nonneg_right (hrow n) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left
        ((A.le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right hA (norm_nonneg x)))
        (by positivity)))
  have hclose : ‖Q.comp (V.comp A) - ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜)‖ ≤ 2*δ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    apply (BoundedContinuousFunction.norm_le (by positivity : 0 ≤ 2*δ*‖x‖)).2
    intro n
    have he := herr x (s (2*n))
    have ho := herr x (s (2*n+1))
    simp only [A, cZeroPairedInsertion_even, cZeroPairedInsertion_odd] at he ho
    change ‖((1/2 : ℝ) : 𝕜) * (V (A x) (t (s (2*n))) -
      V (A x) (t (s (2*n+1)))) - x n‖ ≤ _
    have heq : ((1/2 : ℝ) : 𝕜) * (V (A x) (t (s (2*n))) -
        V (A x) (t (s (2*n+1)))) - x n =
        ((1/2 : ℝ) : 𝕜) * ((V (A x) (t (s (2*n))) - x n) -
          (V (A x) (t (s (2*n+1))) - -x n)) := by
      rw [show ((1/2 : ℝ) : 𝕜) = (1/2 : 𝕜) by
        simp [RCLike.ofReal_ofNat]]
      ring
    rw [heq, norm_mul, RCLike.norm_ofReal, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hh := norm_sub_le (V (A x) (t (s (2*n))) - x n)
      (V (A x) (t (s (2*n+1))) - -x n)
    dsimp only [A] at hh ⊢
    linarith
  letI : Nontrivial (CZeroSum 𝕜) := ⟨⟨cZeroSingle 0 1, 0, by
    intro heq
    have hh := congrArg (fun x : CZeroSum 𝕜 => x 0) heq
    simp at hh⟩⟩
  obtain ⟨Q', hQ', hnQ'⟩ := exists_corrected_factorization_of_close V Q A
    (by positivity : 0 ≤ 2*δ) hδsmall hQ hclose
  exact ⟨A, Q', hQ', hA, hnQ'⟩

theorem exists_cZero_retraction_of_near_unit_columns [Nonempty K]
    (V : CZeroSum 𝕜 →L[𝕜] C(K, 𝕜)) (hV : ‖V‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδsmall : 2*δ < 1)
    (hcol : ∀ n, 1-δ ≤ ‖V (cZeroSingle n 1)‖) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜,
      ∃ Q : C(K, 𝕜) →L[𝕜] CZeroSum 𝕜,
        Q.comp (V.comp A) = ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜) ∧
        ‖A‖ ≤ 1 ∧ ‖Q‖ ≤ (1-2*δ)⁻¹ := by
  classical
  have ht : ∀ n, ∃ t : K, ‖V (cZeroSingle n 1) t‖ = ‖V (cZeroSingle n 1)‖ := by
    intro n
    let f := V (cZeroSingle n 1)
    obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty f.continuous.norm.continuousOn
    refine ⟨t, le_antisymm (f.norm_coe_le_norm t) ?_⟩
    exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 (fun x => ht (Set.mem_univ x))
  choose t ht using ht
  choose a ha hphase using fun n => RCLike.exists_norm_eq_mul_self (V (cZeroSingle n 1) (t n))
  let F (n : ℕ) : 𝕜 →L[𝕜] 𝕜 := a n • ContinuousLinearMap.id 𝕜 𝕜
  have hF (n : ℕ) : ‖F n‖ ≤ 1 := by simp [F, norm_smul, ha]
  let D := cZeroDiagonal F 1 zero_le_one hF
  have hD : ‖D‖ ≤ 1 := norm_cZeroDiagonal_le ..
  have hsingle (n : ℕ) : D (cZeroSingle n 1) = a n • cZeroSingle n 1 := by
    ext i
    change F i (cZeroSingle n 1 i) = a n * cZeroSingle n 1 i
    by_cases hi : i=n
    · subst i; simp [F]
    · simp [cZeroSingle_apply, hi]
  have hVD : ‖V.comp D‖ ≤ 1 := (V.opNorm_comp_le D).trans
    ((mul_le_mul hV hD (norm_nonneg D) zero_le_one).trans_eq (one_mul 1))
  have hdiag (n : ℕ) : (V.comp D) (cZeroSingle n 1) (t n) =
      (‖V (cZeroSingle n 1)‖ : 𝕜) := by
    rw [ContinuousLinearMap.comp_apply, hsingle, map_smul]
    change a n * V (cZeroSingle n 1) (t n) = _
    rw [← hphase n, ht n]
  have hd1 (n : ℕ) : ‖V (cZeroSingle n 1)‖ ≤ 1 :=
    (V.le_opNorm _).trans ((mul_le_mul hV (norm_cZeroSingle_le n (1 : 𝕜))
      (norm_nonneg _) zero_le_one).trans (by simp))
  obtain ⟨A, Q, heq, hA, hQ⟩ := exists_cZero_retraction_of_near_norming_evaluations
    (V.comp D) hVD t (fun n => ‖V (cZeroSingle n 1)‖) hδ hδsmall
    (fun _ => norm_nonneg _) hd1 hcol hdiag
  refine ⟨D.comp A, Q, ?_, ?_, hQ⟩
  · simpa only [ContinuousLinearMap.comp_assoc] using heq
  · exact (D.opNorm_comp_le A).trans
      ((mul_le_mul hD hA (norm_nonneg A) zero_le_one).trans_eq (one_mul 1))

end ThesisCommon
