import SurveyStatements.P5HaarDensityGrid
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Density of actual dyadic step functions in vector-valued Lp on the unit
interval, obtained from continuous-function density and finite-grid sampling. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def haarDensityIndicator (I : DyadicIndex) (c : E) : Lp E p unitIntervalMeasure :=
  indicatorConstLp p (s := haarDensityCell I) measurableSet_Ico (measure_ne_top _ _) c

def haarDensityStepSpace : Submodule 𝕜 (Lp E p unitIntervalMeasure) :=
  Submodule.span 𝕜 (Set.range (fun Ic : DyadicIndex × E =>
    haarDensityIndicator (p := p) Ic.1 Ic.2))

theorem haarDensity_lp_sum_ae {ι : Type*} (s : Finset ι)
    (f : ι → Lp E p unitIntervalMeasure) :
    ((∑ i ∈ s, f i : Lp E p unitIntervalMeasure) : ℝ → E) =ᵐ[unitIntervalMeasure]
      fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero E p unitIntervalMeasure
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (Lp.coeFn_add (f a) (∑ i ∈ s, f i)).trans
        ((EventuallyEq.refl _ _).add ih)

def haarDensitySample (n : ℕ) (f : ℝ → E) : Lp E p unitIntervalMeasure :=
  ∑ i : Fin (2 ^ n), haarDensityIndicator ⟨n, i⟩ (f (dyadicStart ⟨n, i⟩))

theorem haarDensitySample_mem (n : ℕ) (f : ℝ → E) :
    haarDensitySample (p := p) n f ∈ haarDensityStepSpace (𝕜 := 𝕜) := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.subset_span ⟨(⟨n, i⟩, f (dyadicStart ⟨n, i⟩)), rfl⟩

theorem haarDensitySample_ae (n : ℕ) (f : ℝ → E) :
    ∀ᵐ x ∂unitIntervalMeasure,
      ∀ i : Fin (2 ^ n), x ∈ haarDensityCell ⟨n, i⟩ →
        haarDensitySample (p := p) n f x = f (dyadicStart ⟨n, i⟩) := by
  classical
  have hinds : ∀ᵐ x ∂unitIntervalMeasure, ∀ i : Fin (2 ^ n),
      haarDensityIndicator (p := p) ⟨n, i⟩ (f (dyadicStart ⟨n, i⟩)) x =
        (haarDensityCell ⟨n, i⟩).indicator (fun _ => f (dyadicStart ⟨n, i⟩)) x :=
    ae_all_iff.mpr fun i => indicatorConstLp_coeFn
  filter_upwards [haarDensity_lp_sum_ae Finset.univ
    (fun i : Fin (2 ^ n) => haarDensityIndicator (p := p) ⟨n, i⟩
      (f (dyadicStart ⟨n, i⟩))), hinds] with x hsum hi
  intro i hxi
  change (∑ j : Fin (2 ^ n), haarDensityIndicator (p := p) ⟨n, j⟩
    (f (dyadicStart ⟨n, j⟩))) x = _
  rw [hsum]
  rw [Finset.sum_eq_single i]
  · rw [hi i, Set.indicator_of_mem hxi]
  · intro j _ hji
    rw [hi j, Set.indicator_of_notMem]
    intro hxj
    exact hji (haarDensityCell_unique n j i hxj hxi)
  · simp

theorem haarDensity_boundedContinuous_mem_closure (f : BoundedContinuousFunction ℝ E) :
    BoundedContinuousFunction.toLp p unitIntervalMeasure 𝕜 f ∈
      (haarDensityStepSpace (𝕜 := 𝕜) (E := E) (p := p)).topologicalClosure := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hε₂ : 0 < ε / 2 := half_pos hε
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous
    (show ContinuousOn f (Icc (0 : ℝ) 1) from f.continuous.continuousOn)
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) hε₂
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨haarDensitySample (p := p) n f, haarDensitySample_mem (𝕜 := 𝕜) n f, ?_⟩
  have hbound : ∀ᵐ x ∂unitIntervalMeasure,
      ‖(BoundedContinuousFunction.toLp p unitIntervalMeasure 𝕜 f -
        haarDensitySample (p := p) n f) x‖ ≤ ε / 2 := by
    filter_upwards [ae_mem_unitInterval_Ico, haarDensitySample_ae (p := p) n f,
      BoundedContinuousFunction.coeFn_toLp p unitIntervalMeasure 𝕜 f,
      Lp.coeFn_sub (BoundedContinuousFunction.toLp p unitIntervalMeasure 𝕜 f)
        (haarDensitySample (p := p) n f)] with x hx hs hf hsub
    obtain ⟨i, hi⟩ := exists_haarDensityCell n hx
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hf, hs i hi, ← dist_eq_norm]
    exact (hcont x (haarDensityCell_subset ⟨n, i⟩ hi)
      (dyadicStart ⟨n, i⟩)
      ⟨(dyadicEndpoints ⟨n, i⟩).1,
        ((dyadicEndpoints ⟨n, i⟩).2.1.trans
          (dyadicEndpoints ⟨n, i⟩).2.2.1).trans (dyadicEndpoints ⟨n, i⟩).2.2.2⟩
      ((haarDensityCell_dist ⟨n, i⟩ hi).trans hn)).le
  have hnrm : ‖BoundedContinuousFunction.toLp p unitIntervalMeasure 𝕜 f -
      haarDensitySample (p := p) n f‖ ≤ ε / 2 := by
    simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hε₂.le hbound
  rw [dist_eq_norm]
  exact hnrm.trans_lt (half_lt_self hε)

theorem haarDensityStepSpace_closure_eq_top (hp : p ≠ ∞) :
    (haarDensityStepSpace (𝕜 := 𝕜) (E := E) (p := p)).topologicalClosure = ⊤ := by
  letI : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : unitIntervalMeasure.WeaklyRegular := by
    unfold unitIntervalMeasure
    infer_instance
  apply top_unique
  intro f _
  exact (BoundedContinuousFunction.toLp_denseRange E unitIntervalMeasure 𝕜 hp).induction_on f
    (Submodule.isClosed_topologicalClosure _) haarDensity_boundedContinuous_mem_closure

end SurveyStatements.P5
