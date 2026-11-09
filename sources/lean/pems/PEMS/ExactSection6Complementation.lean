import ThesisCommon.Analysis.CZeroAlmostIsometricBlocks
import ThesisCommon.Analysis.SequentialCKNearRetraction

/-! Theorem 6.5 for an arbitrary weak-star sequentially compact norming
subset of the dual ball. Only pointwise convergence of a selected sequence
of functionals is needed; the full dual ball need not be sequentially compact. -/

noncomputable section
open Filter Topology ThesisCommon
namespace PEMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private theorem retraction_of_near_norming_duals
    (V : CZeroSum 𝕜 →L[𝕜] E) (hV : ‖V‖ ≤ 1)
    (φ : ℕ → StrongDual 𝕜 E) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (φ₀ : StrongDual 𝕜 E) (s : ℕ → ℕ) (hs : StrictMono s)
    (ht : ∀ x, Tendsto (fun n => φ (s n) x) atTop (𝓝 (φ₀ x)))
    (d : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδsmall : 2 * δ < 1)
    (hd : ∀ n, 0 ≤ d n) (hd1 : ∀ n, d n ≤ 1)
    (hne : ∀ n, 1 - δ ≤ d n)
    (hdiag : ∀ n, φ n (V (cZeroSingle n 1)) = (d n : 𝕜)) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜, ∃ R : E →L[𝕜] CZeroSum 𝕜,
      R.comp (V.comp A) = ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜) ∧
        ‖A‖ ≤ 1 ∧ ‖R‖ ≤ (1 - 2 * δ)⁻¹ := by
  let ψ (n : ℕ) : StrongDual 𝕜 E :=
    ((1 / 2 : ℝ) : 𝕜) • (φ (s (2*n)) - φ (s (2*n+1)))
  have hψ (n : ℕ) : ‖ψ n‖ ≤ 1 := by
    dsimp [ψ]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    have hh := norm_sub_le (φ (s (2*n))) (φ (s (2*n+1)))
    linarith [hφ (s (2*n)), hφ (s (2*n+1))]
  have hzero (x : E) : Tendsto (fun n => ψ n x) atTop (𝓝 0) := by
    have he : StrictMono (fun n : ℕ => 2*n) := by intro i j hij; dsimp; omega
    have ho : StrictMono (fun n : ℕ => 2*n+1) := by intro i j hij; dsimp; omega
    simpa only [ψ, Function.comp_def, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul, sub_self, mul_zero] using
      (tendsto_const_nhds (x := ((1/2 : ℝ) : 𝕜))).mul
        (((ht x).comp he.tendsto_atTop).sub ((ht x).comp ho.tendsto_atTop))
  let Q := cZeroStrongRows ψ 1 zero_le_one hψ hzero
  let A := cZeroPairedInsertion (𝕜 := 𝕜) s hs
  have hA : ‖A‖ ≤ 1 := norm_cZeroPairedInsertion_le s hs
  have hQ : ‖Q‖ ≤ 1 := norm_cZeroStrongRows_le ..
  have hrow (n : ℕ) : ‖(φ n).comp V - cZeroCoordinate n‖ ≤ 2*δ := by
    apply cZero_functional_near_coordinate _ n
      (((φ n).opNorm_comp_le V).trans
        ((mul_le_mul (hφ n) hV (norm_nonneg V) zero_le_one).trans_eq (one_mul 1)))
      (hd n) (hd1 n) (hdiag n) (hne n)
  have herr (x : CZeroSum 𝕜) (n : ℕ) :
      ‖φ n (V (A x)) - A x n‖ ≤ 2*δ*‖x‖ := by
    have hh := ((φ n).comp V - cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n).le_opNorm (A x)
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
    change ‖((1/2 : ℝ) : 𝕜) * (φ (s (2*n)) (V (A x)) - φ (s (2*n+1)) (V (A x))) - x n‖ ≤ _
    have heq : ((1/2 : ℝ) : 𝕜) * (φ (s (2*n)) (V (A x)) - φ (s (2*n+1)) (V (A x))) - x n =
        ((1/2 : ℝ) : 𝕜) * ((φ (s (2*n)) (V (A x)) - x n) -
          (φ (s (2*n+1)) (V (A x)) - -x n)) := by
      rw [show ((1/2 : ℝ) : 𝕜) = (1/2 : 𝕜) by simp [RCLike.ofReal_ofNat]]
      ring
    rw [heq, norm_mul, RCLike.norm_ofReal, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hh := norm_sub_le (φ (s (2*n)) (V (A x)) - x n)
      (φ (s (2*n+1)) (V (A x)) - -x n)
    dsimp only [A] at hh ⊢
    linarith
  letI : Nontrivial (CZeroSum 𝕜) := ⟨⟨cZeroSingle 0 1, 0, by
    intro heq
    have hh := congrArg (fun x : CZeroSum 𝕜 => x 0) heq
    simp at hh⟩⟩
  obtain ⟨R, hR, hnR⟩ := exists_corrected_factorization_of_close V Q A
    (by positivity : 0 ≤ 2*δ) hδsmall hQ hclose
  exact ⟨A, R, hR, hA, hnR⟩

private theorem retraction_of_near_unit_columns
    (V : CZeroSum 𝕜 →L[𝕜] E) (hV : ‖V‖ ≤ 1)
    (φ : ℕ → StrongDual 𝕜 E) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (φ₀ : StrongDual 𝕜 E) (s : ℕ → ℕ) (hs : StrictMono s)
    (ht : ∀ x, Tendsto (fun n => φ (s n) x) atTop (𝓝 (φ₀ x)))
    {δ : ℝ} (hδ : 0 ≤ δ) (hδsmall : 2*δ < 1)
    (hcol : ∀ n, 1-δ ≤ ‖φ n (V (cZeroSingle n 1))‖) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜, ∃ R : E →L[𝕜] CZeroSum 𝕜,
      R.comp (V.comp A) = ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜) ∧
        ‖A‖ ≤ 1 ∧ ‖R‖ ≤ (1-2*δ)⁻¹ := by
  choose a ha hphase using fun n => RCLike.exists_norm_eq_mul_self (φ n (V (cZeroSingle n 1)))
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
  let d (n : ℕ) := ‖φ n (V (cZeroSingle n 1))‖
  have hdiag (n : ℕ) : φ n ((V.comp D) (cZeroSingle n 1)) = (d n : 𝕜) := by
    rw [ContinuousLinearMap.comp_apply, hsingle, map_smul, map_smul]
    change a n * φ n (V (cZeroSingle n 1)) = _
    exact (hphase n).symm
  have hd1 (n : ℕ) : d n ≤ 1 :=
    ((φ n).le_opNorm _).trans
      ((mul_le_mul (hφ n) ((V.le_opNorm _).trans
        ((mul_le_mul hV (norm_cZeroSingle_le n (1 : 𝕜))
          (norm_nonneg _) zero_le_one).trans (by simp))) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  obtain ⟨A, R, heq, hA, hR⟩ := retraction_of_near_norming_duals
    (V.comp D) hVD φ hφ φ₀ s hs ht d hδ hδsmall (fun _ => norm_nonneg _) hd1 hcol hdiag
  refine ⟨D.comp A, R, ?_, ?_, hR⟩
  · simpa only [ContinuousLinearMap.comp_assoc] using heq
  · exact (D.opNorm_comp_le A).trans
      ((mul_le_mul hD hA (norm_nonneg A) zero_le_one).trans_eq (one_mul 1))

/-- The pointwise subsequence condition expresses weak-star sequential
compactness of the actual norming subset `M` of the dual unit ball. -/
theorem theorem_6_5_printed [CompleteSpace E]
    (M : Set (StrongDual 𝕜 E))
    (hball : ∀ φ ∈ M, ‖φ‖ ≤ 1)
    (hnorming : ∀ x : E, ‖x‖ = sSup ((fun φ : StrongDual 𝕜 E => ‖φ x‖) '' M))
    (hseq : ∀ φ : ℕ → StrongDual 𝕜 E, (∀ n, φ n ∈ M) →
      ∃ φ₀ ∈ M, ∃ s : ℕ → ℕ, StrictMono s ∧
        ∀ x : E, Tendsto (fun n => φ (s n) x) atTop (𝓝 (φ₀ x)))
    (Y : Submodule 𝕜 E) (e : CZeroSum 𝕜 ≃L[𝕜] Y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Z : Submodule 𝕜 E, Z ≤ Y ∧
      (∃ eZ : CZeroSum 𝕜 ≃L[𝕜] Z,
        ‖eZ.toContinuousLinearMap‖ * ‖eZ.symm.toContinuousLinearMap‖ ≤ 1 + ε) ∧
      ∃ P : E →L[𝕜] Z, (∀ z : Z, P (z : E) = z) ∧ ‖P‖ ≤ 1 + ε := by
  let V : CZeroSum 𝕜 →L[𝕜] E := Y.subtypeL.comp e.toContinuousLinearMap
  let k := ‖e.symm.toContinuousLinearMap‖ + 1
  have hk : 0 < k := by dsimp [k]; positivity
  have hlower (x : CZeroSum 𝕜) : k⁻¹ * ‖x‖ ≤ ‖V x‖ := by
    have h := e.symm.toContinuousLinearMap.le_opNorm (e x)
    change ‖e.symm (e x)‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ at h
    rw [e.symm_apply_apply] at h
    have h' : ‖x‖ ≤ k * ‖V x‖ := h.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right zero_le_one) (norm_nonneg _))
    calc
      _ ≤ k⁻¹ * (k * ‖V x‖) := mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hk.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
  let δ := ε / (2 * (1 + ε))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : 2 * δ < 1 := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    linarith
  have hinv : (1 - 2*δ)⁻¹ = 1+ε := by
    dsimp [δ]
    have he : 1+ε ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  obtain ⟨B, b, hkb, _, hVB, hcols⟩ := exists_cZero_almost_maximal_tail_blocks
    V (inv_pos.mpr hk) hlower hδ (by linarith)
  have hb : 0 < b := (inv_pos.mpr hk).trans_le hkb
  letI : NormSMulClass 𝕜 (CZeroSum 𝕜 →L[𝕜] E) :=
    @NormedSpace.toNormSMulClass 𝕜 (CZeroSum 𝕜 →L[𝕜] E) _ _ _
  let U : CZeroSum 𝕜 →L[𝕜] E := ((b⁻¹ : ℝ) : 𝕜) • (V.comp B)
  have hU : ‖U‖ ≤ 1 := by
    dsimp [U]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hb)]
    exact (mul_le_mul_of_nonneg_left hVB (inv_nonneg.mpr hb.le)).trans_eq
      (inv_mul_cancel₀ hb.ne')
  have hcol (n : ℕ) : 1 - δ < ‖U (cZeroSingle n 1)‖ := by
    change 1 - δ < ‖((b⁻¹ : ℝ) : 𝕜) • V (B (cZeroSingle n 1))‖
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hb)]
    have hh := mul_lt_mul_of_pos_left (hcols n) (inv_pos.mpr hb)
    have heq : b⁻¹ * ((1-δ)*b) = 1-δ := by field_simp
    rwa [heq] at hh
  have hφ (n : ℕ) : ∃ φ ∈ M, 1 - δ < ‖φ (U (cZeroSingle n 1))‖ := by
    by_contra! hnone
    have hs := Real.sSup_le (s := (fun φ : StrongDual 𝕜 E => ‖φ (U (cZeroSingle n 1))‖) '' M)
      (a := 1 - δ) (by rintro _ ⟨φ, hφM, rfl⟩; exact hnone φ hφM) (by linarith)
    rw [← hnorming] at hs
    exact (hcol n).not_ge hs
  choose φ hφM hφcol using hφ
  obtain ⟨φ₀, _, s, hs, ht⟩ := hseq φ hφM
  obtain ⟨A, R, hRA, hA, hR⟩ := retraction_of_near_unit_columns U hU φ
    (fun n => hball (φ n) (hφM n)) φ₀ s hs ht hδ.le hsmall (fun n => (hφcol n).le)
  let J := U.comp A
  have hJ : ‖J‖ ≤ 1 := (U.opNorm_comp_le A).trans
    ((mul_le_mul hU hA (norm_nonneg A) zero_le_one).trans_eq (one_mul 1))
  let Z : Submodule 𝕜 E := LinearMap.range J.toLinearMap
  have hZY : Z ≤ Y := by
    rintro _ ⟨x, rfl⟩
    change ((b⁻¹ : ℝ) : 𝕜) • ((e (B (A x)) : Y) : E) ∈ Y
    exact Y.smul_mem _ (e _).property
  let JZ := J.codRestrict Z (fun x => ⟨x, rfl⟩)
  let RZ := R.comp Z.subtypeL
  have hRJ (x : CZeroSum 𝕜) : R (J x) = x := DFunLike.congr_fun hRA x
  have hright (z : Z) : JZ (RZ z) = z := by
    obtain ⟨x, hx⟩ := z.property
    apply Subtype.ext
    change J (R (z : E)) = (z : E)
    change J x = (z : E) at hx
    rw [← hx, hRJ]
  let eZ : CZeroSum 𝕜 ≃L[𝕜] Z :=
    { toLinearEquiv := LinearEquiv.ofLinear JZ.toLinearMap RZ.toLinearMap
        (by apply LinearMap.ext; intro z; exact hright z)
        (by apply LinearMap.ext; intro x; exact hRJ x)
      continuous_toFun := JZ.continuous
      continuous_invFun := RZ.continuous }
  have hJZ : ‖JZ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖J x‖ ≤ 1 * ‖x‖
    exact (J.le_opNorm x).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg x))
  have hRZ : ‖RZ‖ ≤ 1+ε := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    change ‖R (z : E)‖ ≤ (1+ε) * ‖(z : E)‖
    exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_right (hinv ▸ hR) (norm_nonneg _))
  refine ⟨Z, hZY, ⟨eZ, ?_⟩, JZ.comp R, hright, ?_⟩
  · change ‖JZ‖ * ‖RZ‖ ≤ 1 + ε
    exact (mul_le_mul hJZ hRZ (norm_nonneg RZ) zero_le_one).trans_eq (one_mul _)
  · exact (JZ.opNorm_comp_le R).trans
      ((mul_le_mul hJZ (hinv ▸ hR) (norm_nonneg R) zero_le_one).trans_eq (one_mul _))

end PEMS
