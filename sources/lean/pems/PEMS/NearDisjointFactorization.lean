import PEMS.EllOneFactorizationUpperBound
import ThesisCommon.Analysis.L1NearDisjointFactorization

/-! The quantitative factorization consequence of a supplied normalized
disjoint sequence and its summably close disjoint image model. The maps
are constructed; no complemented copy or perturbation theorem is assumed. -/
noncomputable section
open MeasureTheory Set ThesisCommon
namespace PEMS
variable {𝕜 X Y : Type*} [RCLike 𝕜] [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem one_sub_le_factorizationSup_of_near_disjoint
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (u : ℕ → LOne 𝕜 μ) (g : ℕ → LOne 𝕜 ν)
    (hdu : Pairwise fun i j => ∀ᵐ x ∂μ, u i x = 0 ∨ u j x = 0)
    (hdg : Pairwise fun i j => ∀ᵐ y ∂ν, g i y = 0 ∨ g j y = 0)
    (hu : ∀ n, ‖u n‖ = 1) (hg : ∀ n, ‖g n‖ = 1)
    (hsum : Summable (fun n => ‖T (u n) - g n‖))
    {ε : ℝ} (hε : ε < 1) (herr : (∑' n, ‖T (u n) - g n‖) < ε) :
    1 - ε ≤ factorizationSup (EllOne 𝕜) T := by
  obtain ⟨V, U, _, hfact, hU, hV⟩ :=
    exists_lOne_factorization_of_near_disjoint T u g hdu hdg hu hg hsum hε herr
  have hUne : U ≠ 0 := by
    intro hzero
    have h := DFunLike.congr_fun hfact (lp.single 1 0 (1 : 𝕜))
    rw [hzero] at h
    have hc := congrArg (fun x : lp (fun _ : ℕ => 𝕜) 1 => x 0) h
    simpa using hc
  have hconst : 1 - ε ≤ ‖U‖⁻¹ * ‖V.toContinuousLinearMap‖⁻¹ := by
    rw [hV, inv_one, mul_one]
    simpa only [inv_inv] using inv_anti₀ (norm_pos_iff.mpr hUne) hU
  apply hconst.trans
  apply le_csSup
  · refine ⟨weakEssentialNorm T, ?_⟩
    rintro r (rfl | ⟨A, B, hAB, rfl⟩)
    · exact weakEssentialNorm_nonneg T
    · exact scalarEllOne_factorization_constant_le_weakEssentialNorm T A B hAB
  · exact Set.mem_insert_of_mem _ ⟨U, V.toContinuousLinearMap, hfact, rfl⟩

end PEMS
