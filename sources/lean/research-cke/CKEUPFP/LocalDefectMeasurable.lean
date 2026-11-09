import CKEUPFP.LocalDefect
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.Metrizable.Basic

/-!
# Borel local defects via a dense unit-ball sequence

The space of continuous functions vanishing outside `O` is a genuine submodule.
Its unit ball admits one fixed dense sequence, independent of the evaluation
point. Continuity in the function argument identifies the paper's supremum
with a countable supremum, proving its Borelness.
-/

noncomputable section

open TopologicalSpace

namespace CKEUPFP

variable {𝕜 K E : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Continuous functions zero on the complement of `O`. -/
def SupportedFunctions (𝕜 : Type*) [RCLike 𝕜] (K E : Type*)
    [TopologicalSpace K] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (O : Set K) : Submodule 𝕜 C(K, E) where
  carrier := {f | VanishesOff O f}
  zero_mem' := vanishesOff_zero O
  add_mem' := by
    intro f g hf hg t ht
    change f t + g t = 0
    rw [hf t ht, hg t ht, zero_add]
  smul_mem' := by
    intro c f hf t ht
    change c • f t = 0
    rw [hf t ht, smul_zero]

/-- The closed unit ball in the supported subspace, with its subtype topology. -/
abbrev SupportedUnitBall (𝕜 : Type*) [RCLike 𝕜] (K E : Type*)
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (O : Set K) :=
  {f : SupportedFunctions 𝕜 K E O // ‖f‖ ≤ 1}

variable [CompactSpace K] [SecondCountableTopology K] [T2Space K] [SeparableSpace E]

instance supportedFunctions_secondCountable (O : Set K) :
    SecondCountableTopology (SupportedFunctions 𝕜 K E O) := by
  exact (isometry_subtype_coe : Isometry
    ((↑) : SupportedFunctions 𝕜 K E O → C(K, E))).isEmbedding.secondCountableTopology

instance supportedUnitBall_secondCountable (O : Set K) :
    SecondCountableTopology (SupportedUnitBall 𝕜 K E O) := by
  exact (isometry_subtype_coe : Isometry
    ((↑) : SupportedUnitBall 𝕜 K E O → SupportedFunctions 𝕜 K E O)).isEmbedding.secondCountableTopology

instance supportedUnitBall_nonempty (O : Set K) : Nonempty (SupportedUnitBall 𝕜 K E O) :=
  ⟨⟨0, by simp⟩⟩

/-- A dense sequence in the supported unit ball. -/
def supportedUnitSeq (O : Set K) : ℕ → SupportedUnitBall 𝕜 K E O :=
  TopologicalSpace.denseSeq _

theorem denseRange_supportedUnitSeq (O : Set K) : DenseRange (supportedUnitSeq (𝕜 := 𝕜) (E := E) O) :=
  TopologicalSpace.denseRange_denseSeq _

/-- The real supremum defining the local defect equals a countable supremum
over the fixed dense sequence in the supported unit ball. -/
theorem localDefect_eq_iSup_supportedUnitSeq
    (T : C(K, E) →L[𝕜] C(K, E)) (A : K → E →L[𝕜] E) (O : Set K) (t : K) :
    localDefect T A O t =
      ⨆ n : ℕ, ‖T (supportedUnitSeq (𝕜 := 𝕜) (E := E) O n).val.val t -
        A t ((supportedUnitSeq (𝕜 := 𝕜) (E := E) O n).val.val t)‖ := by
  let q := supportedUnitSeq (𝕜 := 𝕜) (E := E) O
  let F : C(K, E) →L[𝕜] E := rowOperator T t - (A t).comp (ContinuousMap.evalCLM 𝕜 t)
  let a : ℕ → ℝ := fun n => ‖F (q n).val.val‖
  have hbdd : BddAbove (Set.range a) := by
    refine ⟨‖T‖ + ‖A t‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hh := mul_le_mul_of_nonneg_left ((q n).property)
      (add_nonneg (norm_nonneg T) (norm_nonneg (A t)))
    exact (defect_norm_le T A t (q n).val.val).trans (by simpa only [mul_one] using hh)
  change localDefect T A O t = ⨆ n, a n
  apply le_antisymm
  · apply csSup_le (localDefect_set_nonempty T A O t)
    rintro r ⟨f, hf, hO, rfl⟩
    let z : SupportedUnitBall 𝕜 K E O := ⟨⟨f, hO⟩, hf⟩
    have hc : Continuous (fun z : SupportedUnitBall 𝕜 K E O => ‖F z.val.val‖) :=
      (F.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)).norm
    have hz : ‖F z.val.val‖ ≤ ⨆ n, a n :=
      (denseRange_supportedUnitSeq (𝕜 := 𝕜) (E := E) O).induction_on z
        (isClosed_le hc continuous_const) (fun n => le_ciSup hbdd n)
    exact hz
  · apply ciSup_le
    intro n
    exact norm_sub_le_localDefect T A O t (q n).val.val (q n).property (q n).val.property

variable [MeasurableSpace K] [BorelSpace K] [MeasurableSpace E] [BorelSpace E]

/-- Borel variable-vector evaluation of the field makes every local defect
Borel. The field's measurable-evaluation input is explicit here. -/
theorem localDefect_measurable_of_measurable_evaluation
    (T : C(K, E) →L[𝕜] C(K, E)) (A : K → E →L[𝕜] E)
    (hA : ∀ f : C(K, E), Measurable (fun t => A t (f t))) (O : Set K) :
    Measurable (localDefect T A O) := by
  have heq : localDefect T A O = fun t =>
      ⨆ n : ℕ, ‖T (supportedUnitSeq (𝕜 := 𝕜) (E := E) O n).val.val t -
        A t ((supportedUnitSeq (𝕜 := 𝕜) (E := E) O n).val.val t)‖ :=
    funext (localDefect_eq_iSup_supportedUnitSeq T A O)
  rw [heq]
  apply Measurable.iSup
  intro n
  let f := (supportedUnitSeq (𝕜 := 𝕜) (E := E) O n).val.val
  exact ((T f).continuous.measurable.sub (hA f)).norm

end CKEUPFP
