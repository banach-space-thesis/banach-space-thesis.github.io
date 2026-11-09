import PL1.TruncatedResolventFactorization
import PL1.TraceVanishing

/-!
# From genuine noise smoothing to the actual projection trace obstruction

Only compatible Lp-to-L2 noise extensions are explicit premises here. All
resolvent cutoffs, matrix entries, column summability and approximation limits
are discharged for the actual construction. The missing Enflo-Starbird
subspace theorem is not asserted or assumed by the factorization obstruction.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PL1.Noise
open Walsh ResolventEstimates

variable (𝕜 : Type*) [RCLike 𝕜] (rates : ℕ → ℝ≥0)

theorem resolvent_hasVanishingDyadicTrace_of_noise_smoothing
    (t : PositiveTime) (ε : ℕ → ℝ≥0)
    (hε : Tendsto (fun m => (ε m : ℝ)) atTop (𝓝 0))
    (p : ℕ → ℝ≥0∞) [∀ m, Fact (1 ≤ p m)] (hp2 : ∀ m, p m < 2)
    (H : ∀ m, Lp 𝕜 (p m) haar →L[𝕜] Lp 𝕜 2 haar)
    (hH : ∀ m (g : Lp 𝕜 1 haar) (f : Lp 𝕜 (p m) haar),
      g =ᵐ[haar] f → noiseL1 𝕜 rates (ε m) g = l2ToL1 (H m f)) :
    HasVanishingDyadicTrace (resolventL1 𝕜 rates t) := by
  intro A B
  apply SmoothingTrace.trace_tendsto_zero_of_smoothing_approximation haar haar
    A (resolventL1 𝕜 rates t) (fun m => truncatedResolventL1 𝕜 rates t (ε m)) B
    _ p hp2 (fun m => truncatedResolventLpToL2 (rates := rates) t (ε m) (H m)) l2ToL1
    (fun m => truncatedResolventLpToL2_overlap t (ε m) (H m) (hH m))
  simpa only [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp
    (truncatedResolventL1_tendsto 𝕜 rates atTop t ε hε)

/-- The matrix entries computed from the actual projection are the original
weighted analysis/reconstruction blocks. -/
theorem projection_entry (i j : ℕ) :
    MatrixTrace.entry (projection 𝕜 rates) i j =
      ((dyadicSystem 𝕜 rates).analysis i).comp ((dyadicSystem 𝕜 rates).baseColumn j) := by
  apply ContinuousLinearMap.ext
  intro f
  change (projection 𝕜 rates) (lp.single 1 j f) i = _
  exact (dyadicSystem 𝕜 rates).projection_single_coord i j f

theorem projection_summable_column_norms (j : ℕ) :
    Summable (fun i => ‖MatrixTrace.entry (projection 𝕜 rates) i j‖) := by
  simp only [projection_entry]
  exact weighted_block_norm_summable (dyadicSystem 𝕜 rates).operator
    (dyadicSystem 𝕜 rates).contractive (dyadicSystem 𝕜 rates).resolvent j

theorem projection_entry_hasVanishingDyadicTrace
    (hR : ∀ t : PositiveTime, HasVanishingDyadicTrace (resolventL1 𝕜 rates t))
    (i j : ℕ) : HasVanishingDyadicTrace (MatrixTrace.entry (projection 𝕜 rates) i j) := by
  rw [projection_entry]
  apply HasVanishingDyadicTrace.comp_left
  cases j with
  | zero => exact hR (dyadicTime 0)
  | succ j => exact (hR (dyadicTime j)).smul _

theorem projection_hasVanishingDyadicTrace_of_resolvents
    (hR : ∀ t : PositiveTime, HasVanishingDyadicTrace (resolventL1 𝕜 rates t)) :
    HasVanishingDyadicTrace (projection 𝕜 rates) := by
  intro A B
  apply MatrixTrace.trace_tendsto_zero_of_summable_columns haar A (projection 𝕜 rates) B
    (projection_summable_column_norms 𝕜 rates)
  intro i j
  exact projection_entry_hasVanishingDyadicTrace 𝕜 rates hR i j
    (A.comp (MatrixTrace.insertion i)) ((MatrixTrace.coordinate j).comp B)

theorem projection_hasVanishingDyadicTrace_of_noise_smoothing
    (ε : ℕ → ℝ≥0) (hε : Tendsto (fun m => (ε m : ℝ)) atTop (𝓝 0))
    (p : ℕ → ℝ≥0∞) [∀ m, Fact (1 ≤ p m)] (hp2 : ∀ m, p m < 2)
    (H : ∀ m, Lp 𝕜 (p m) haar →L[𝕜] Lp 𝕜 2 haar)
    (hH : ∀ m (g : Lp 𝕜 1 haar) (f : Lp 𝕜 (p m) haar),
      g =ᵐ[haar] f → noiseL1 𝕜 rates (ε m) g = l2ToL1 (H m f)) :
    HasVanishingDyadicTrace (projection 𝕜 rates) :=
  projection_hasVanishingDyadicTrace_of_resolvents 𝕜 rates
    (fun t => resolvent_hasVanishingDyadicTrace_of_noise_smoothing 𝕜 rates t ε hε p hp2 H hH)

end PL1.Noise
