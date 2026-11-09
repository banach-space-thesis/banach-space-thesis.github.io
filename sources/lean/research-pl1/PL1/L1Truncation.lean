import PL1.L1UniformIntegrability
import PL1.CompactRestriction

/-!
# Uniform bounded truncation and the L1 compact-restriction criterion

Actual bounded functions approximate every weakly convergent scalar L1
sequence uniformly. Consequently, compactness of an operator's restriction
to L-infinity implies its Dunford-Pettis property on L1.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal

namespace PL1.L1Truncation

variable {𝕜 Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω]
variable (μ : Measure Ω)

/-- Remove the part of an L1 function at or above a prescribed norm threshold. -/
def truncatedFun (f : Lp 𝕜 1 μ) (C : ℝ≥0) : Ω → 𝕜 :=
  {a | ‖f a‖₊ < C}.indicator f

theorem measurableSet_below (f : Lp 𝕜 1 μ) (C : ℝ≥0) :
    MeasurableSet {a | ‖f a‖₊ < C} :=
  measurableSet_lt (Lp.stronglyMeasurable f).nnnorm.measurable measurable_const

theorem norm_truncatedFun_le (f : Lp 𝕜 1 μ) (C : ℝ≥0) (a : Ω) :
    ‖truncatedFun μ f C a‖ ≤ C := by
  classical
  by_cases ha : ‖f a‖₊ < C
  · simp only [truncatedFun, mem_ofPred_eq, ha, indicator_of_mem]
    exact_mod_cast ha.le
  · rw [truncatedFun, indicator_of_notMem (show a ∉ {a | ‖f a‖₊ < C} from ha), norm_zero]
    exact C.property

theorem memLp_truncatedFun (f : Lp 𝕜 1 μ) (C : ℝ≥0) :
    MemLp (truncatedFun μ f C) ∞ μ :=
  memLp_top_of_bound ((Lp.aestronglyMeasurable f).indicator (measurableSet_below μ f C)) C
    (Eventually.of_forall (norm_truncatedFun_le μ f C))

/-- The bounded truncation as an actual L-infinity equivalence class. -/
def truncate (f : Lp 𝕜 1 μ) (C : ℝ≥0) : Lp 𝕜 ∞ μ :=
  (memLp_truncatedFun μ f C).toLp (truncatedFun μ f C)

theorem coeFn_truncate (f : Lp 𝕜 1 μ) (C : ℝ≥0) :
    truncate μ f C =ᵐ[μ] truncatedFun μ f C :=
  (memLp_truncatedFun μ f C).coeFn_toLp

variable [IsProbabilityMeasure μ]

theorem norm_truncate_le (f : Lp 𝕜 1 μ) (C : ℝ≥0) : ‖truncate μ f C‖ ≤ C := by
  have hb : ∀ᵐ a ∂μ, ‖truncate μ f C a‖ ≤ C := by
    filter_upwards [coeFn_truncate μ f C] with a ha
    rw [ha]
    exact norm_truncatedFun_le μ f C a
  simpa using Lp.norm_le_of_ae_bound C.property hb

/-- The truncation error is precisely the removed large-value tail. -/
theorem coeFn_sub_inclusion_truncate (f : Lp 𝕜 1 μ) (C : ℝ≥0) :
    (f - ProbabilityLp.inclusion μ 1 ∞ le_top (truncate μ f C) : Lp 𝕜 1 μ) =ᵐ[μ]
      {a | C ≤ ‖f a‖₊}.indicator f := by
  classical
  filter_upwards [Lp.coeFn_sub f (ProbabilityLp.inclusion μ 1 ∞ le_top (truncate μ f C)),
    ProbabilityLp.coeFn_inclusion μ 1 ∞ le_top (truncate μ f C), coeFn_truncate μ f C]
      with a hsub hinc htrunc
  change (f - ProbabilityLp.inclusion μ 1 ∞ le_top (truncate μ f C)) a =
    f a - ProbabilityLp.inclusion μ 1 ∞ le_top (truncate μ f C) a at hsub
  rw [hsub, hinc, htrunc]
  by_cases ha : ‖f a‖₊ < C
  · simp [truncatedFun, ha, not_le_of_gt ha]
  · simp [truncatedFun, ha, le_of_not_gt ha]

/-- Uniform integrability supplies uniform approximation by a bounded ball
of the actual L-infinity space. -/
theorem uniformIntegrable_hasUniformBoundedApproximations {x : ℕ → Lp 𝕜 1 μ}
    (hx : UniformIntegrable (fun n => (x n : Ω → 𝕜)) 1 μ) :
    HasUniformBoundedApproximations (ProbabilityLp.inclusion μ 1 ∞ le_top) x := by
  intro ε hε
  obtain ⟨C, hC⟩ := hx.spec (by simp : (1 : ℝ≥0∞) ≠ 0) (by simp : (1 : ℝ≥0∞) ≠ ∞)
    (ENNReal.ofReal_pos.mpr (half_pos hε))
  refine ⟨C, fun n => ⟨truncate μ (x n) C, norm_truncate_le μ (x n) C, ?_⟩⟩
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_sub_inclusion_truncate μ (x n) C)]
  calc
    (eLpNorm ({a | C ≤ ‖x n a‖₊}.indicator (x n)) 1 μ).toReal ≤
        (ENNReal.ofReal (ε / 2)).toReal := ENNReal.toReal_mono (by simp) (hC n)
    _ = ε / 2 := ENNReal.toReal_ofReal (half_pos hε).le
    _ < ε := half_lt_self hε

/-- The uniform approximation hypothesis follows from full-dual weak
convergence, without any additional assumptions on the sequence. -/
theorem weaklyConverges_hasUniformBoundedApproximations {x : ℕ → Lp 𝕜 1 μ}
    {a : Lp 𝕜 1 μ} (hx : WeaklyConverges 𝕜 (Lp 𝕜 1 μ) x a) :
    HasUniformBoundedApproximations (ProbabilityLp.inclusion μ 1 ∞ le_top) x :=
  uniformIntegrable_hasUniformBoundedApproximations μ
    (L1UniformIntegrability.weaklyConverges_uniformIntegrable hx)

/-- The paper's compact-restriction criterion for scalar L1 on a probability
space, with the weak-sequence uniform-integrability step fully discharged. -/
theorem isDunfordPettis_of_compact_Linfty_restriction
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : Lp 𝕜 1 μ →L[𝕜] F)
    (hcompact : IsCompactOperator (T.comp (ProbabilityLp.inclusion μ 1 ∞ le_top))) :
    IsDunfordPettis T :=
  isDunfordPettis_of_compact_restriction T _ hcompact
    (fun _ _ hx => weaklyConverges_hasUniformBoundedApproximations μ hx)

end PL1.L1Truncation
