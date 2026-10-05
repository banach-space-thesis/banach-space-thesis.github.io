import JFA.CZeroTensorEmbedding
import Mathlib.Topology.Algebra.Module.Basic

/-! Finite-support truncations prove surjectivity of the actual tensor map for
discrete spaces. In particular C₀(ℕ) ⊗̂ε X ≅ C₀(ℕ,X). The scalar coordinate
vectors also prove separability of C₀(A) when A is countable and discrete. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Filter Set
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
local instance : DecidableEq A := Classical.decEq A

def czeroDelta (a : A) : C₀(A, 𝕜) := by
  classical
  exact {
    toFun := fun b => if b = a then 1 else 0
    continuous_toFun := continuous_of_discreteTopology
    zero_at_infty' := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      apply Filter.eventually_of_mem (isCompact_singleton (x := a)).compl_mem_cocompact
      intro b hb
      have hba : b ≠ a := by simpa only [mem_compl_iff, mem_singleton_iff] using hb
      simpa only [if_neg hba, dist_self] using hε }

@[simp] theorem czeroDelta_apply (a b : A) :
    czeroDelta (𝕜 := 𝕜) a b = if b = a then 1 else 0 := rfl

def czeroTruncate (t : Finset A) (g : C₀(A, X)) : C₀(A, X) :=
  ∑ a ∈ t, czeroPureFunction (czeroDelta (𝕜 := 𝕜) a) (g a)

omit [CompleteSpace X] in
@[simp] theorem czeroTruncate_apply (t : Finset A) (g : C₀(A, X)) (b : A) :
    czeroTruncate (𝕜 := 𝕜) t g b = if b ∈ t then g b else 0 := by
  classical
  simp [czeroTruncate, czeroDelta_apply, ite_smul]

omit [CompleteSpace X] in
theorem exists_czeroTruncate_approx (g : C₀(A, X)) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Finset A, ‖g - czeroTruncate (𝕜 := 𝕜) t g‖ < ε := by
  classical
  obtain ⟨K, hK, htail⟩ := czero_vector_compact_tail g (ε / 2) (half_pos hε)
  let t := hK.finite_of_discrete.toFinset
  refine ⟨t, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  change ‖(g - czeroTruncate (𝕜 := 𝕜) t g).toBCF‖ ≤ ε / 2
  apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
  intro b
  change ‖g b - czeroTruncate (𝕜 := 𝕜) t g b‖ ≤ ε / 2
  rw [czeroTruncate_apply]
  by_cases hb : b ∈ t
  · simp only [if_pos hb, sub_self, norm_zero]
    exact (half_pos hε).le
  · rw [if_neg hb, sub_zero]
    exact (htail b (by simpa only [t, Set.Finite.mem_toFinset] using hb)).le

theorem exists_tensorCzero_approx (g : C₀(A, X)) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : InjectiveTensor 𝕜 C₀(A, 𝕜) X, ‖g - tensorCzeroFunction z‖ < ε := by
  obtain ⟨t, ht⟩ := exists_czeroTruncate_approx (𝕜 := 𝕜) g ε hε
  let z : InjectiveTensor 𝕜 C₀(A, 𝕜) X :=
    ∑ a ∈ t, injectivePure 𝕜 C₀(A, 𝕜) X (czeroDelta a) (g a)
  have hz : tensorCzeroFunction z = czeroTruncate (𝕜 := 𝕜) t g := by
    ext b
    simp only [z, czeroTruncate, map_sum, czero_sum_apply,
      tensorCzeroFunction_pure, czeroPureFunction_apply]
  exact ⟨z, hz.symm ▸ ht⟩

theorem tensorCzeroFunction_dense :
    DenseRange (tensorCzeroFunction (𝕜 := 𝕜) (A := A) (X := X)) := by
  apply Metric.denseRange_iff.mpr
  intro g ε hε
  obtain ⟨z, hz⟩ := exists_tensorCzero_approx (𝕜 := 𝕜) g ε hε
  exact ⟨z, by simpa only [dist_eq_norm] using hz⟩

theorem tensorCzeroIsometry_surjective :
    Function.Surjective (tensorCzeroIsometry (𝕜 := 𝕜) (A := A) (X := X)) := by
  intro g
  have hclosed := (tensorCzeroIsometry (𝕜 := 𝕜) (A := A) (X := X)).isometry.isClosedEmbedding.isClosed_range
  have hg := tensorCzeroFunction_dense (𝕜 := 𝕜) (A := A) (X := X) g
  change g ∈ closure (range (tensorCzeroIsometry (𝕜 := 𝕜) (A := A) (X := X))) at hg
  rw [hclosed.closure_eq] at hg
  exact hg

def tensorCzeroDiscreteEquiv : InjectiveTensor 𝕜 C₀(A, 𝕜) X ≃ₗᵢ[𝕜] C₀(A, X) :=
  LinearIsometryEquiv.ofSurjective tensorCzeroIsometry tensorCzeroIsometry_surjective

theorem czero_countable_discrete_separable [Countable A] : SeparableSpace C₀(A, 𝕜) := by
  let V : Submodule 𝕜 C₀(A, 𝕜) := Submodule.span 𝕜 (range (czeroDelta (𝕜 := 𝕜) (A := A)))
  have hV : IsSeparable (V : Set C₀(A, 𝕜)) := (countable_range _).isSeparable.span
  have hdense : Dense (V : Set C₀(A, 𝕜)) := by
    apply Metric.dense_iff.mpr
    intro g ε hε
    obtain ⟨t, ht⟩ := exists_czeroTruncate_approx (𝕜 := 𝕜) g ε hε
    refine ⟨czeroTruncate (𝕜 := 𝕜) t g, ?_, ?_⟩
    · apply Metric.mem_ball.mpr
      rw [dist_comm, dist_eq_norm]
      exact ht
    · change (∑ a ∈ t, czeroPureFunction (czeroDelta (𝕜 := 𝕜) a) (g a)) ∈ V
      apply V.sum_mem
      intro a ha
      have heq : czeroPureFunction (czeroDelta (𝕜 := 𝕜) a) (g a) = g a • czeroDelta a := by
        ext b
        simp only [czeroPureFunction_apply, ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
        exact mul_comm _ _
      rw [heq]
      exact V.smul_mem _ (Submodule.subset_span (mem_range_self a))
  exact hdense.isSeparable_iff.mp hV

end JFA
