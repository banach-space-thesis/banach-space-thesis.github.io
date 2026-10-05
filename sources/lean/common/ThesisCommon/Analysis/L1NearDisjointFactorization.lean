import ThesisCommon.Analysis.L1DisjointSupports
import ThesisCommon.Analysis.EllOneColumns
import ThesisCommon.Analysis.QuantitativeNeumannInverse

/-! Quantitative correction of almost-disjoint L1 factorizations. The
embedding and retraction are built from the supplied normalized disjoint
vectors, and a genuine Neumann inverse corrects the summable column error. -/
noncomputable section
open MeasureTheory Set
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

section ColumnEstimate
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem norm_ellOne_factorization_error_le
    (T : E →L[𝕜] F) (U : F →L[𝕜] lp (fun _ : ℕ => 𝕜) 1)
    (V : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] E) (u : ℕ → E) (g : ℕ → F)
    (hV : ∀ n, V (lp.single 1 n 1) = u n)
    (hUg : ∀ n, U (g n) = lp.single 1 n 1) (hU : ‖U‖ ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) (herr : ∀ n, ‖T (u n) - g n‖ ≤ C) :
    ‖U.comp (T.comp V) - ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 1)‖ ≤ C := by
  apply ellOne_norm_le_of_columns _ hC
  intro n
  change ‖U (T (V (lp.single 1 n 1))) - lp.single 1 n 1‖ ≤ C
  rw [hV, ← hUg, ← map_sub]
  exact (U.le_opNorm _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hU).trans (herr n))

theorem norm_ellOne_factorization_error_lt_of_summable
    (T : E →L[𝕜] F) (U : F →L[𝕜] lp (fun _ : ℕ => 𝕜) 1)
    (V : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] E) (u : ℕ → E) (g : ℕ → F)
    (hV : ∀ n, V (lp.single 1 n 1) = u n)
    (hUg : ∀ n, U (g n) = lp.single 1 n 1) (hU : ‖U‖ ≤ 1)
    (hsum : Summable (fun n => ‖T (u n) - g n‖))
    {ε : ℝ} (herr : (∑' n, ‖T (u n) - g n‖) < ε) :
    ‖U.comp (T.comp V) - ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 1)‖ < ε :=
  (norm_ellOne_factorization_error_le T U V u g hV hUg hU
    (tsum_nonneg (fun _ => norm_nonneg _))
    (fun n => hsum.le_tsum n (fun _ _ => norm_nonneg _))).trans_lt herr

end ColumnEstimate

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_lOne_factorization_of_near_disjoint
    (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν)
    (u : ℕ → Lp 𝕜 1 μ) (g : ℕ → Lp 𝕜 1 ν)
    (hdu : Pairwise fun i j => ∀ᵐ x ∂μ, u i x = 0 ∨ u j x = 0)
    (hdg : Pairwise fun i j => ∀ᵐ y ∂ν, g i y = 0 ∨ g j y = 0)
    (hu : ∀ n, ‖u n‖ = 1) (hg : ∀ n, ‖g n‖ = 1)
    (hsum : Summable (fun n => ‖T (u n) - g n‖))
    {ε : ℝ} (hε : ε < 1) (herr : (∑' n, ‖T (u n) - g n‖) < ε) :
    ∃ V : lp (fun _ : ℕ => 𝕜) 1 →ₗᵢ[𝕜] Lp 𝕜 1 μ,
      ∃ U : Lp 𝕜 1 ν →L[𝕜] lp (fun _ : ℕ => 𝕜) 1,
        (∀ n, V (lp.single 1 n 1) = u n) ∧
        U.comp (T.comp V.toContinuousLinearMap) = ContinuousLinearMap.id 𝕜 _ ∧
        ‖U‖ ≤ (1 - ε)⁻¹ ∧ ‖V.toContinuousLinearMap‖ = 1 := by
  letI : Nontrivial (lp (fun _ : ℕ => 𝕜) 1) := ⟨⟨lp.single 1 0 1, 0, by
    intro h
    have hc := congrArg (fun x : lp (fun _ : ℕ => 𝕜) 1 => x 0) h
    simpa using hc⟩⟩
  obtain ⟨V, _, hV, _, _, hnormV⟩ := exists_lOne_ae_disjoint_isometric_retraction u hdu hu
  obtain ⟨G, R, hG, hRG, hR, _⟩ := exists_lOne_ae_disjoint_isometric_retraction g hdg hg
  have hRg (n : ℕ) : R (g n) = lp.single 1 n 1 := by
    have h := DFunLike.congr_fun hRG (lp.single 1 n (1 : 𝕜))
    change R (G (lp.single 1 n 1)) = lp.single 1 n 1 at h
    rwa [hG] at h
  have hclose := norm_ellOne_factorization_error_lt_of_summable T R V.toContinuousLinearMap
    u g hV hRg hR hsum herr
  have hε0 : 0 ≤ ε := (tsum_nonneg (fun n => norm_nonneg (T (u n) - g n))).trans herr.le
  obtain ⟨U, hUTV, hUnorm⟩ := exists_corrected_factorization_of_close T R V.toContinuousLinearMap
    hε0 hε hR hclose.le
  exact ⟨V, U, hV, hUTV, hUnorm, hnormV⟩

end ThesisCommon
