import CKEUPFP.Definitions
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# Bounded strong operator balls

This fresh type carries the strong operator topology, rather than the operator
norm topology of `ContinuousLinearMap`. A countable dense family of vectors
provides its uniformity. Uniform bounds make evaluation at every vector
uniformly continuous. The operator ball is complete and Polish.
-/

noncomputable section

open Set Function Filter Topology TopologicalSpace
open scoped Uniformity NNReal

namespace CKEUPFP

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Operators of norm at most `M`, with a topology defined below by strong
convergence. The bound is part of the data, and no norm topology is inherited. -/
structure StrongOperatorBall (M : ℝ≥0) where
  operator : E →L[𝕜] E
  norm_le : ‖operator‖ ≤ M

namespace StrongOperatorBall

variable {𝕜 E} {M : ℝ≥0}

@[ext] theorem ext {R S : StrongOperatorBall 𝕜 E M} (h : R.operator = S.operator) : R = S := by
  cases R
  cases S
  congr

variable [SeparableSpace E]

/-- Countable strong evaluation coordinates. -/
def code (R : StrongOperatorBall 𝕜 E M) : ℕ → E :=
  fun n => R.operator (denseSeq E n)

instance uniformSpace : UniformSpace (StrongOperatorBall 𝕜 E M) :=
  UniformSpace.comap code inferInstance

theorem isUniformInducing_code : IsUniformInducing (code (𝕜 := 𝕜) (E := E) (M := M)) := ⟨rfl⟩

theorem code_injective : Function.Injective (code (𝕜 := 𝕜) (E := E) (M := M)) := by
  intro R S h
  apply ext
  apply DFunLike.coe_injective
  exact (denseRange_denseSeq E).equalizer R.operator.continuous S.operator.continuous h

theorem isUniformEmbedding_code : IsUniformEmbedding (code (𝕜 := 𝕜) (E := E) (M := M)) :=
  ⟨isUniformInducing_code, code_injective⟩

instance t0Space : T0Space (StrongOperatorBall 𝕜 E M) :=
  isUniformEmbedding_code.isEmbedding.t0Space

instance secondCountableTopology : SecondCountableTopology (StrongOperatorBall 𝕜 E M) :=
  isUniformInducing_code.isInducing.secondCountableTopology

instance uniformity_countablyGenerated :
    (𝓤 (StrongOperatorBall 𝕜 E M)).IsCountablyGenerated := by
  change (Filter.comap (Prod.map code code) (𝓤 (ℕ → E))).IsCountablyGenerated
  infer_instance

omit [SeparableSpace E] in
theorem norm_apply_le (R : StrongOperatorBall 𝕜 E M) (x : E) :
    ‖R.operator x‖ ≤ M * ‖x‖ :=
  (R.operator.le_opNorm x).trans (mul_le_mul_of_nonneg_right R.norm_le (norm_nonneg x))

omit [SeparableSpace E] in
theorem dist_apply_le (R : StrongOperatorBall 𝕜 E M) (x y : E) :
    dist (R.operator x) (R.operator y) ≤ M * dist x y := by
  simpa only [dist_eq_norm, ← map_sub] using norm_apply_le R (x - y)

theorem uniformContinuous_eval (x : E) :
    UniformContinuous (fun R : StrongOperatorBall 𝕜 E M => R.operator x) := by
  rw [UniformContinuous, Metric.uniformity_basis_dist.tendsto_right_iff]
  intro ε hε
  have hδ : 0 < ε / (6 * ((M : ℝ) + 1)) := by positivity
  obtain ⟨n, hn⟩ := (denseRange_denseSeq E).exists_dist_lt x hδ
  have hcoord : UniformContinuous (fun R : StrongOperatorBall 𝕜 E M =>
      R.operator (denseSeq E n)) :=
    (Pi.uniformContinuous_proj (fun _ : ℕ => E) n).comp
      isUniformInducing_code.uniformContinuous
  have hsmall := hcoord (Metric.dist_mem_uniformity (by positivity : 0 < ε / 3))
  filter_upwards [hsmall] with p hp
  have hbound : (M : ℝ) * dist x (denseSeq E n) < ε / 6 := by
    have hM : (M : ℝ) < (M : ℝ) + 1 := by linarith
    have hprod' : ((M : ℝ) + 1) * dist x (denseSeq E n) < ε / 6 := by
      have hn' := (lt_div_iff₀ (by positivity : 0 < 6 * ((M : ℝ) + 1))).mp hn
      nlinarith
    exact (mul_le_mul_of_nonneg_right hM.le dist_nonneg).trans_lt hprod'
  calc
    dist (p.1.operator x) (p.2.operator x) ≤
      dist (p.1.operator x) (p.1.operator (denseSeq E n)) +
        dist (p.1.operator (denseSeq E n)) (p.2.operator (denseSeq E n)) +
        dist (p.2.operator (denseSeq E n)) (p.2.operator x) := dist_triangle4 _ _ _ _
    _ ≤ M * dist x (denseSeq E n) +
        dist (p.1.operator (denseSeq E n)) (p.2.operator (denseSeq E n)) +
        M * dist x (denseSeq E n) := by
      gcongr
      · exact dist_apply_le p.1 x (denseSeq E n)
      · simpa only [dist_comm] using dist_apply_le p.2 (denseSeq E n) x
    _ < ε := by
      change dist (p.1.operator (denseSeq E n))
        (p.2.operator (denseSeq E n)) < ε / 3 at hp
      linarith

theorem continuous_eval (x : E) :
    Continuous (fun R : StrongOperatorBall 𝕜 E M => R.operator x) :=
  (uniformContinuous_eval x).continuous

/-- Evaluation is jointly continuous on each fixed bounded strong operator
ball, exactly as needed for vector-valued multipliers. -/
theorem continuous_apply :
    Continuous (fun p : StrongOperatorBall 𝕜 E M × E => p.1.operator p.2) := by
  rw [Metric.continuous_iff']
  intro p ε hε
  have heval : ∀ᶠ q : StrongOperatorBall 𝕜 E M × E in 𝓝 p,
      dist (q.1.operator p.2) (p.1.operator p.2) < ε / 2 := Metric.continuousAt_iff'.mp
    ((continuous_eval (𝕜 := 𝕜) (M := M) p.2).comp
      (continuous_fst : Continuous (fun p : StrongOperatorBall 𝕜 E M × E => p.1))).continuousAt
        (ε / 2) (by positivity)
  have hvec : ∀ᶠ q : StrongOperatorBall 𝕜 E M × E in 𝓝 p,
      dist q.2 p.2 < ε / (2 * ((M : ℝ) + 1)) := Metric.continuousAt_iff'.mp
    (continuous_snd : Continuous (fun p : StrongOperatorBall 𝕜 E M × E => p.2)).continuousAt
      (ε / (2 * ((M : ℝ) + 1))) (by positivity)
  filter_upwards [heval, hvec] with q hqeval hqvec
  have hbound : (M : ℝ) * dist q.2 p.2 < ε / 2 := by
    have hqvec' := (lt_div_iff₀ (by positivity : 0 < 2 * ((M : ℝ) + 1))).mp hqvec
    nlinarith [M.coe_nonneg, dist_nonneg (x := q.2) (y := p.2)]
  calc
    dist (q.1.operator q.2) (p.1.operator p.2) ≤
      dist (q.1.operator q.2) (q.1.operator p.2) +
        dist (q.1.operator p.2) (p.1.operator p.2) := dist_triangle _ _ _
    _ ≤ (M : ℝ) * dist q.2 p.2 + dist (q.1.operator p.2) (p.1.operator p.2) :=
      add_le_add_right (dist_apply_le q.1 q.2 p.2) _
    _ < ε := by linarith

theorem isUniformInducing_all_eval :
    IsUniformInducing (fun R : StrongOperatorBall 𝕜 E M => fun x => R.operator x) := by
  apply IsUniformInducing.of_comp
      (uniformContinuous_pi.mpr uniformContinuous_eval)
      (Pi.uniformContinuous_precomp' (fun _ : E => E) (denseSeq E))
  exact isUniformInducing_code

theorem continuous_iff {P : Type*} [TopologicalSpace P]
    {R : P → StrongOperatorBall 𝕜 E M} :
    Continuous R ↔ ∀ x : E, Continuous (fun t => (R t).operator x) := by
  rw [isUniformInducing_all_eval.isInducing.continuous_iff]
  exact continuous_pi_iff

theorem tendsto_iff {P : Type*} {l : Filter P}
    {R : P → StrongOperatorBall 𝕜 E M} {R₀ : StrongOperatorBall 𝕜 E M} :
    Tendsto R l (𝓝 R₀) ↔ ∀ x : E,
      Tendsto (fun t => (R t).operator x) l (𝓝 (R₀.operator x)) := by
  rw [isUniformInducing_all_eval.isInducing.tendsto_nhds_iff]
  exact tendsto_pi_nhds

instance measurableSpace : MeasurableSpace (StrongOperatorBall 𝕜 E M) :=
  borel (StrongOperatorBall 𝕜 E M)

instance borelSpace : BorelSpace (StrongOperatorBall 𝕜 E M) := ⟨rfl⟩

/-- Composition of bounded operators, with the bound multiplied. -/
def comp {N : ℝ≥0} (R : StrongOperatorBall 𝕜 E M) (S : StrongOperatorBall 𝕜 E N) :
    StrongOperatorBall 𝕜 E (M * N) where
  operator := R.operator.comp S.operator
  norm_le := (R.operator.opNorm_comp_le S.operator).trans
    (mul_le_mul R.norm_le S.norm_le (norm_nonneg _) M.coe_nonneg)

/-- Multiplication is jointly strong-continuous when the operator bounds are
fixed, as in Lemma `lem:strong-balls` of the paper. -/
theorem continuous_comp {N : ℝ≥0} :
    Continuous (fun p : StrongOperatorBall 𝕜 E M × StrongOperatorBall 𝕜 E N =>
      comp p.1 p.2) := by
  apply continuous_iff.mpr
  intro x
  exact continuous_apply.comp
    (continuous_fst.prodMk ((continuous_eval x).comp continuous_snd))

/-- Regard a bounded operator in any larger norm ball. -/
def inclusion {N : ℝ≥0} (hMN : M ≤ N) (R : StrongOperatorBall 𝕜 E M) :
    StrongOperatorBall 𝕜 E N :=
  ⟨R.operator, R.norm_le.trans (by exact_mod_cast hMN)⟩

theorem continuous_inclusion {N : ℝ≥0} (hMN : M ≤ N) :
    Continuous (inclusion (𝕜 := 𝕜) (E := E) hMN) := by
  apply continuous_iff.mpr
  exact continuous_eval

/-- The complementary operator `I - R`, in a fixed larger ball. -/
def complement (R : StrongOperatorBall 𝕜 E M) : StrongOperatorBall 𝕜 E (1 + M) where
  operator := ContinuousLinearMap.id 𝕜 E - R.operator
  norm_le := (norm_sub_le _ _).trans
    (add_le_add ContinuousLinearMap.norm_id_le R.norm_le)

theorem continuous_complement :
    Continuous (complement (𝕜 := 𝕜) (E := E) (M := M)) := by
  apply continuous_iff.mpr
  intro x
  change Continuous (fun R : StrongOperatorBall 𝕜 E M => x - R.operator x)
  exact continuous_const.sub (continuous_eval x)

omit [SeparableSpace E] in
private theorem isClosed_range_all_eval :
    IsClosed (Set.range (fun R : StrongOperatorBall 𝕜 E M => fun x => R.operator x)) := by
  have heq : Set.range (fun R : StrongOperatorBall 𝕜 E M => fun x => R.operator x) =
      {f : E → E | (∀ x y, f (x + y) = f x + f y) ∧
        (∀ (c : 𝕜) x, f (c • x) = c • f x) ∧ ∀ x, ‖f x‖ ≤ M * ‖x‖} := by
    ext f
    constructor
    · rintro ⟨R, rfl⟩
      exact ⟨R.operator.map_add, R.operator.map_smul, norm_apply_le R⟩
    · rintro ⟨hfadd, hfsmul, hfbound⟩
      let L : E →ₗ[𝕜] E :=
        { toFun := f
          map_add' := hfadd
          map_smul' := hfsmul }
      let R : E →L[𝕜] E := L.mkContinuous M hfbound
      exact ⟨⟨R, LinearMap.mkContinuous_norm_le L M.coe_nonneg hfbound⟩, rfl⟩
  rw [heq]
  simp only [setOf_and, setOf_forall]
  refine (isClosed_iInter fun x => isClosed_iInter fun y => ?_).inter
    ((isClosed_iInter fun c => isClosed_iInter fun x => ?_).inter
      (isClosed_iInter fun x => ?_))
  · exact isClosed_eq (_root_.continuous_apply (x + y))
      ((_root_.continuous_apply x).add (_root_.continuous_apply y))
  · exact isClosed_eq (_root_.continuous_apply (c • x))
      ((_root_.continuous_apply x).const_smul c)
  · exact isClosed_le ((_root_.continuous_apply x).norm) continuous_const

instance completeSpace [CompleteSpace E] : CompleteSpace (StrongOperatorBall 𝕜 E M) :=
  isUniformInducing_all_eval.completeSpace isClosed_range_all_eval.isComplete

instance polishSpace [CompleteSpace E] : PolishSpace (StrongOperatorBall 𝕜 E M) :=
  inferInstance

/-- Borel measurability into a bounded strong operator ball is exactly Borel
measurability after evaluation on every fixed vector. -/
theorem measurable_iff [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {S : Type*} [MeasurableSpace S] {R : S → StrongOperatorBall 𝕜 E M} :
    Measurable R ↔ ∀ x : E, Measurable (fun t => (R t).operator x) := by
  constructor
  · intro hR x
    exact (continuous_eval x).measurable.comp hR
  · intro heval
    have hcode : MeasurableEmbedding (code (𝕜 := 𝕜) (E := E) (M := M)) :=
      isUniformEmbedding_code.isClosedEmbedding.measurableEmbedding
    apply hcode.measurable_comp_iff.mp
    change Measurable (fun t : S => fun n : ℕ => (R t).operator (denseSeq E n))
    exact measurable_pi_iff.mpr fun n => heval (denseSeq E n)

/-- A strongly Borel bounded operator field applied to a Borel vector field
is Borel. This is Lemma `lem:borel-evaluation` of the paper. -/
theorem measurable_apply [MeasurableSpace E] [BorelSpace E]
    {S : Type*} [MeasurableSpace S]
    {R : S → StrongOperatorBall 𝕜 E M} {u : S → E}
    (hR : Measurable R) (hu : Measurable u) :
    Measurable (fun t => (R t).operator (u t)) :=
  (continuous_apply (𝕜 := 𝕜) (E := E) (M := M)).measurable.comp (hR.prodMk hu)

end StrongOperatorBall

end CKEUPFP
