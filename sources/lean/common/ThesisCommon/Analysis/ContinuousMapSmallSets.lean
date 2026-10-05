import ThesisCommon.Analysis.ScalarBlockEstimate
import ThesisCommon.Analysis.EllOneThreshold

/-! The closed finite cover in LPCK Lemma 3.11. A point belongs to a
small set when the whole restricted operator, evaluated there, is small
on the unit ball. No matrix representation is assumed. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def continuousMapSmallSet (T : X →L[𝕜] C(K, 𝕜)) (ε : ℝ) : Set K :=
  {t | ∀ x : X, ‖x‖ ≤ 1 → ‖T x t‖ ≤ ε}

omit [CompactSpace K] in
theorem isClosed_continuousMapSmallSet (T : X →L[𝕜] C(K, 𝕜)) (ε : ℝ) :
    IsClosed (continuousMapSmallSet T ε) := by
  unfold continuousMapSmallSet
  simp only [Set.setOf_forall]
  exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
    isClosed_le (T x).continuous.norm continuous_const))

theorem norm_continuousMap_evalCLM_le (t : K) : ‖ContinuousMap.evalCLM (M := 𝕜) 𝕜 t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using f.norm_coe_le_norm t

theorem continuousMap_small_sets_cover {N : ℕ} (J : Fin N → X →L[𝕜] Y)
    {B ε : ℝ}
    (hJ : ∀ x : Fin N → X, (∀ i, ‖x i‖ ≤ 1) → ‖∑ i, J i (x i)‖ ≤ B)
    (T : Y →L[𝕜] C(K, 𝕜)) (hlarge : ‖T‖ * B < (N : ℝ) * ε) :
    ∀ t : K, ∃ i : Fin N, t ∈ continuousMapSmallSet (T.comp (J i)) ε := by
  intro t
  let R := (ContinuousMap.evalCLM 𝕜 t).comp T
  have hR : ‖R‖ ≤ ‖T‖ := by
    calc
      ‖R‖ ≤ ‖ContinuousMap.evalCLM 𝕜 t‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_continuousMap_evalCLM_le t) (norm_nonneg T)
      _ = ‖T‖ := one_mul _
  obtain ⟨i, hi⟩ := exists_small_scalar_block J (norm_nonneg T) hJ R hR hlarge
  refine ⟨i, ?_⟩
  intro x hx
  exact ((R.comp (J i)).le_opNorm x).trans ((mul_le_mul_of_nonneg_left hx
    (norm_nonneg (R.comp (J i)))).trans (by simpa only [mul_one] using hi))

theorem lp_continuousMap_small_sets_cover {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p.toReal) (T : lp (fun _ : ℕ => X) p →L[𝕜] C(K, 𝕜))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ t : K, ∃ i : Fin N,
      t ∈ continuousMapSmallSet (T.comp (lpExtend p (disjointCoordinateEmbedding i))) ε := by
  obtain ⟨N, hN⟩ := exists_ellOne_power_threshold (M := ‖T‖) hp (show 0 < 2*ε by positivity)
  have hlarge : ‖T‖ * (N : ℝ) ^ (1 / p.toReal) < (N : ℝ) * ε := by
    have h := ellOne_power_threshold hp (norm_nonneg T) hN
    convert h using 1; ring
  refine ⟨N, continuousMap_small_sets_cover (𝕜 := 𝕜)
    (X := lp (fun _ : ℕ => X) p) (Y := lp (fun _ : ℕ => X) p)
    (fun i : Fin N => lpExtend (𝕜 := 𝕜) (X := X) p (disjointCoordinateEmbedding i)) ?_ T hlarge⟩
  intro x hx
  simpa only [signedValue, if_true] using lp_disjoint_blocks_sign_bound (𝕜 := 𝕜)
    p (zero_lt_one.trans hp) x hx (fun _ => true)

theorem infinity_continuousMap_small_sets_cover
    (T : EllInfinitySum X →L[𝕜] C(K, 𝕜)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ t : K, ∃ i : Fin N,
      t ∈ continuousMapSmallSet (T.comp (lpExtend ∞ (disjointCoordinateEmbedding i))) ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖T‖ / ε)
  have hlarge : ‖T‖ * 1 < (N : ℝ) * ε := by
    simpa only [mul_one] using (div_lt_iff₀ hε).mp hN
  refine ⟨N, continuousMap_small_sets_cover (𝕜 := 𝕜)
    (X := EllInfinitySum X) (Y := EllInfinitySum X)
    (fun i : Fin N => lpExtend (𝕜 := 𝕜) (X := X) ∞ (disjointCoordinateEmbedding i)) ?_ T hlarge⟩
  intro x hx
  simpa using infinity_disjoint_blocks_sign_bound (𝕜 := 𝕜) x hx (fun _ => true)

end ThesisCommon
