import ThesisCommon.Analysis.IntervalLpFunctionPartition
import ThesisCommon.Analysis.IntervalLpFunctionAffine

/-! Actual Lebesgue `Lp[0,1]` is linearly isometric to its countable `lp` sum.
The construction is the measurable dyadic partition followed by normalized
affine pullbacks on every block. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon

section CoordinateEquivalence
variable {𝕜 ι : Type*} [RCLike 𝕜]
  {E F : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

def lebesgueLpCoordinateValue (hp : 0 < p.toReal) (e : ∀ i, E i ≃ₗᵢ[𝕜] F i)
    (x : lp E p) : lp F p :=
  ⟨fun i => e i (x i), (memℓp_gen_iff hp).mpr (by
    simpa only [LinearIsometryEquiv.norm_map] using (lp.memℓp x).summable hp)⟩

def lebesgueLpCoordinateEquiv (hp : 0 < p.toReal) (e : ∀ i, E i ≃ₗᵢ[𝕜] F i) :
    lp E p ≃ₗᵢ[𝕜] lp F p where
  toFun := lebesgueLpCoordinateValue hp e
  invFun := lebesgueLpCoordinateValue hp (fun i => (e i).symm)
  left_inv x := by
    apply lp.ext
    funext i
    exact (e i).symm_apply_apply (x i)
  right_inv x := by
    apply lp.ext
    funext i
    exact (e i).apply_symm_apply (x i)
  map_add' x y := by
    apply lp.ext
    funext i
    exact map_add (e i) (x i) (y i)
  map_smul' c x := by
    apply lp.ext
    funext i
    exact map_smul (e i) c (x i)
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    apply tsum_congr
    intro i
    change ‖e i (x i)‖ ^ p.toReal = ‖x i‖ ^ p.toReal
    rw [LinearIsometryEquiv.norm_map]
end CoordinateEquivalence

theorem intervalLpDyadicBlock_measure (n : ℕ) :
    (volume.restrict (Icc (0 : ℝ) 1)).restrict (intervalLpDyadicBlock n) =
      volume.restrict (Ioc (intervalLpDyadicRadius (n + 1))
        (2 * intervalLpDyadicRadius (n + 1))) := by
  rw [Measure.restrict_restrict_of_subset (intervalLpDyadicBlock_subset n)]
  congr 1
  unfold intervalLpDyadicBlock intervalLpDyadicRadius
  congr 1
  rw [pow_succ]
  ring

def intervalLpFunctionBlockEquiv (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) :
    Lp 𝕜 p.val ((volume.restrict (Icc (0 : ℝ) 1)).restrict (intervalLpDyadicBlock n))
      ≃ₗᵢ[𝕜] IntervalLp 𝕜 p :=
  (lebesgueLpMeasureCongr (𝕜 := 𝕜) (intervalLpDyadicBlock_measure n)).trans
    (intervalLpFunctionAffine 𝕜 p hp (intervalLpDyadicRadius (n + 1))
      (intervalLpDyadicRadius_pos (n + 1)))

/-- The self-similarity used by UPFP Corollary 1.3, with its full finite exponent
range and real or complex scalars.  Both sides are the manuscript's actual spaces. -/
def intervalLpFunctionSelfSimilarity (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) : IntervalLp 𝕜 p ≃ₗᵢ[𝕜] SequenceSum p (IntervalLp 𝕜 p) :=
  (intervalLpFunctionPartition 𝕜 p hp).trans
    (lebesgueLpCoordinateEquiv
      (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one p.property)) hp)
      (intervalLpFunctionBlockEquiv 𝕜 p hp))

theorem intervalLpFunction_isFiniteLpSelfSimilar (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (hp : p.val ≠ ∞) :
    IsFiniteLpSelfSimilar 𝕜 (IntervalLp 𝕜 p) :=
  ⟨p, hp, ⟨(intervalLpFunctionSelfSimilarity 𝕜 p hp).toContinuousLinearEquiv⟩⟩

theorem intervalLpFunction_isSequenceSelfSimilar (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (hp : p.val ≠ ∞) :
    IsSequenceSelfSimilar 𝕜 (IntervalLp 𝕜 p) :=
  Or.inl ⟨p, ⟨(intervalLpFunctionSelfSimilarity 𝕜 p hp).toContinuousLinearEquiv⟩⟩

end ThesisCommon
