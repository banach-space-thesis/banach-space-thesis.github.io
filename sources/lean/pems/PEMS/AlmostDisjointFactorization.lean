import PEMS.NearDisjointFactorization
import ThesisCommon.Analysis.AlmostDisjointNormalization

/-! The quantitative factorization lower bound from actual almost-disjoint
image sequences. The normalized output sequence and a summably close
subsequence are constructed, and the checked disjoint-vector retractions
and Neumann correction construct the factorizing operators. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped Topology
namespace PEMS
variable {𝕜 X Y : Type*} [RCLike 𝕜] [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem mul_one_sub_le_factorizationSup_of_almost_disjoint
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (u : ℕ → LOne 𝕜 μ) (g : ℕ → LOne 𝕜 ν)
    (hdu : Pairwise fun i j => ∀ᵐ x ∂μ, u i x = 0 ∨ u j x = 0)
    (hdg : Pairwise fun i j => ∀ᵐ y ∂ν, g i y = 0 ∨ g j y = 0)
    (hu : ∀ n, ‖u n‖ = 1)
    (herr : Tendsto (fun n => ‖T (u n) - g n‖) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) (hnorm : Tendsto (fun n => ‖T (u n)‖) atTop (𝓝 c))
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1) :
    c * (1 - ε) ≤ factorizationSup (EllOne 𝕜) T := by
  let z : 𝕜 := ((c⁻¹ : ℝ) : 𝕜)
  let T' : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν := z • T
  let g' : ℕ → LOne 𝕜 ν := fun n => ((‖g n‖⁻¹ : ℝ) : 𝕜) • g n
  have hg_lim := tendsto_norm_model_of_norm_error herr hnorm
  have hgne : ∀ᶠ n in atTop, g n ≠ 0 := by
    filter_upwards [hg_lim.eventually (lt_mem_nhds hc)] with n hn
    exact norm_pos_iff.mp hn
  have he_lim : Tendsto (fun n => ‖T' (u n) - g' n‖) atTop (𝓝 0) :=
    tendsto_normalized_model_error hc herr hnorm
  obtain ⟨φ, hφ, hφne, hsum, hsmall⟩ :=
    exists_summable_subsequence_lt (fun n => norm_nonneg (T' (u n) - g' n))
      he_lim hgne hε0
  have hdu' : Pairwise fun i j => ∀ᵐ x ∂μ, u (φ i) x = 0 ∨ u (φ j) x = 0 :=
    fun _ _ hij => hdu (hφ.injective.ne hij)
  have hdg' : Pairwise fun i j => ∀ᵐ y ∂ν, g' (φ i) y = 0 ∨ g' (φ j) y = 0 := by
    intro i j hij
    filter_upwards [hdg (hφ.injective.ne hij),
      Lp.coeFn_smul (((‖g (φ i)‖⁻¹ : ℝ) : 𝕜)) (g (φ i)),
      Lp.coeFn_smul (((‖g (φ j)‖⁻¹ : ℝ) : 𝕜)) (g (φ j))] with y hy hi hj
    change g' (φ i) y = 0 ∨ g' (φ j) y = 0
    change g' (φ i) y = _ at hi
    change g' (φ j) y = _ at hj
    rcases hy with hy | hy
    · exact Or.inl (by simpa only [Pi.smul_apply, hy, smul_zero] using hi)
    · exact Or.inr (by simpa only [Pi.smul_apply, hy, smul_zero] using hj)
  have hgnorm (n : ℕ) : ‖g' (φ n)‖ = 1 := by
    simpa only [g', RCLike.ofReal_inv] using norm_smul_inv_norm (𝕜 := 𝕜) (hφne n)
  obtain ⟨V, U, _, hfact, hU, hV⟩ :=
    exists_lOne_factorization_of_near_disjoint T' (fun n => u (φ n))
      (fun n => g' (φ n)) hdu' hdg' (fun n => hu _) hgnorm hsum hε hsmall
  have hUne : U ≠ 0 := by
    intro hzero
    have h := DFunLike.congr_fun hfact (lp.single 1 0 (1 : 𝕜))
    rw [hzero] at h
    have hc' := congrArg (fun x : lp (fun _ : ℕ => 𝕜) 1 => x 0) h
    simpa using hc'
  have hfact' : (z • U).comp (T.comp V.toContinuousLinearMap) =
      ContinuousLinearMap.id 𝕜 (EllOne 𝕜) := by
    calc
      _ = U.comp (T'.comp V.toContinuousLinearMap) := by
        apply ContinuousLinearMap.ext
        intro f
        simp [T']
      _ = _ := hfact
  have hinv : 1 - ε ≤ ‖U‖⁻¹ := by
    simpa only [inv_inv] using inv_anti₀ (norm_pos_iff.mpr hUne) hU
  have hconst : c * (1 - ε) ≤ ‖z • U‖⁻¹ * ‖V.toContinuousLinearMap‖⁻¹ := by
    rw [hV, inv_one, mul_one, norm_smul]
    have hz : ‖z‖ = c⁻¹ := by
      simp only [z, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hc)]
    rw [hz, mul_inv_rev, inv_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right hinv hc.le
  apply hconst.trans
  apply le_csSup
  · refine ⟨weakEssentialNorm T, ?_⟩
    rintro r (rfl | ⟨A, B, hAB, rfl⟩)
    · exact weakEssentialNorm_nonneg T
    · exact scalarEllOne_factorization_constant_le_weakEssentialNorm T A B hAB
  · exact Set.mem_insert_of_mem _ ⟨z • U, V.toContinuousLinearMap, hfact', rfl⟩

/-- A normalized disjoint input sequence with almost-disjoint images of
limiting norm `c > 0` gives the sharp lower factorization bound. -/
theorem le_factorizationSup_of_almost_disjoint
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (u : ℕ → LOne 𝕜 μ) (g : ℕ → LOne 𝕜 ν)
    (hdu : Pairwise fun i j => ∀ᵐ x ∂μ, u i x = 0 ∨ u j x = 0)
    (hdg : Pairwise fun i j => ∀ᵐ y ∂ν, g i y = 0 ∨ g j y = 0)
    (hu : ∀ n, ‖u n‖ = 1)
    (herr : Tendsto (fun n => ‖T (u n) - g n‖) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) (hnorm : Tendsto (fun n => ‖T (u n)‖) atTop (𝓝 c)) :
    c ≤ factorizationSup (EllOne 𝕜) T := by
  have he : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    convert tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1) using 1
    ext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have ht : Tendsto (fun n : ℕ => c * (1 - 1 / ((n : ℝ) + 2))) atTop (𝓝 c) := by
    convert (tendsto_const_nhds.sub he).const_mul c using 1 <;> simp
  apply le_of_tendsto ht (Eventually.of_forall fun n => ?_)
  apply mul_one_sub_le_factorizationSup_of_almost_disjoint T u g hdu hdg hu herr hc hnorm
  · positivity
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    rw [div_lt_one (by positivity)]
    linarith

/-- The sequence conclusion of source Lemma 5.4 suffices for the full sharp
factorization equality; every factorization is constructed from the vectors. -/
theorem weakEssentialNorm_eq_factorizationSup_of_almost_disjoint
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (u : ℕ → LOne 𝕜 μ) (g : ℕ → LOne 𝕜 ν)
    (hdu : Pairwise fun i j => ∀ᵐ x ∂μ, u i x = 0 ∨ u j x = 0)
    (hdg : Pairwise fun i j => ∀ᵐ y ∂ν, g i y = 0 ∨ g j y = 0)
    (hu : ∀ n, ‖u n‖ = 1)
    (herr : Tendsto (fun n => ‖T (u n) - g n‖) atTop (𝓝 0))
    (hnorm : Tendsto (fun n => ‖T (u n)‖) atTop (𝓝 (weakEssentialNorm T))) :
    weakEssentialNorm T = factorizationSup (EllOne 𝕜) T := by
  apply le_antisymm _ (factorizationSup_ellOne_le_weakEssentialNorm T)
  rcases eq_or_lt_of_le (weakEssentialNorm_nonneg T) with hz | hp
  · rw [← hz]
    apply le_csSup
    · refine ⟨weakEssentialNorm T, ?_⟩
      rintro r (rfl | ⟨A, B, hAB, rfl⟩)
      · exact weakEssentialNorm_nonneg T
      · exact scalarEllOne_factorization_constant_le_weakEssentialNorm T A B hAB
    · exact Set.mem_insert 0 _
  · exact le_factorizationSup_of_almost_disjoint T u g hdu hdg hu herr hp hnorm

end PEMS
