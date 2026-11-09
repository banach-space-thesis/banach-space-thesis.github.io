import SurveyStatements.P4FiniteComplementBasis
import SurveyStatements.P4BlockOrthogonality
import SurveyStatements.P4BlockIndex
import SurveyStatements.P4SchauderCriterion

/-! The finite block bases in the product with an actual square-summable
complement: continuous coordinates, biorthogonality, and dense span. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

open Set Finset Filter Topology Module
open scoped BigOperators ENNReal

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {Z : Type v} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable (D : ContractiveFiniteDecomposition 𝕜 Z)
variable (G : ∀ n, FiniteBasisExtension 𝕜 (D.Block n))

abbrev BlockBasisSpace := Z × lp (fun n => (G n).Complement) 2
abbrev BlockBasisBlock (n : ℕ) := D.Block n × (G n).Complement

def blockBasisInjection (n : ℕ) : BlockBasisBlock D G n →L[𝕜] BlockBasisSpace D G :=
  ((D.Block n).subtypeL.comp (ContinuousLinearMap.fst 𝕜 _ _)).prod
    ((lp.singleContinuousLinearMap 𝕜 (fun n => (G n).Complement) 2 n).comp
      (ContinuousLinearMap.snd 𝕜 _ _))

@[simp] lemma blockBasisInjection_apply (n : ℕ) (x : BlockBasisBlock D G n) :
    blockBasisInjection D G n x = (x.1.val, lp.single 2 n x.2) := rfl

lemma norm_blockBasisInjection_apply (n : ℕ) (x : BlockBasisBlock D G n) :
    ‖blockBasisInjection D G n x‖ = ‖x‖ := by
  simp only [blockBasisInjection_apply, Prod.norm_def, lp.norm_single (by norm_num :
    (0 : ℝ≥0∞) < 2), Submodule.norm_coe]

lemma norm_blockBasisInjection_le (n : ℕ) : ‖blockBasisInjection D G n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [norm_blockBasisInjection_apply, one_mul]

def blockBasisCoordinate (n : ℕ) : BlockBasisSpace D G →L[𝕜] BlockBasisBlock D G n :=
  ((D.coordinate n).comp (ContinuousLinearMap.fst 𝕜 _ _)).prod
    ((lp2Eval (𝕜 := 𝕜) n).comp (ContinuousLinearMap.snd 𝕜 _ _))

@[simp] lemma blockBasisCoordinate_apply (n : ℕ) (x : BlockBasisSpace D G) :
    blockBasisCoordinate D G n x = (D.coordinate n x.1, x.2 n) := rfl

lemma norm_blockBasisCoordinate_le (n : ℕ) : ‖blockBasisCoordinate D G n‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [blockBasisCoordinate_apply, Prod.norm_def]
  apply max_le
  · exact ((D.coordinate n).le_opNorm x.1).trans
      ((mul_le_mul_of_nonneg_right (D.norm_coordinate_le_two n) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (norm_fst_le x) (by norm_num)))
  · exact (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x.2 n).trans
      ((norm_snd_le x).trans (by nlinarith [norm_nonneg x]))

@[simp] lemma blockBasisCoordinate_injection (n : ℕ) (x : BlockBasisBlock D G n) :
    blockBasisCoordinate D G n (blockBasisInjection D G n x) = x := by
  ext <;> simp [D.coordinate_on_block]

lemma blockBasisCoordinate_injection_of_ne {n m : ℕ} (hnm : n ≠ m)
    (x : BlockBasisBlock D G m) :
    blockBasisCoordinate D G n (blockBasisInjection D G m x) = 0 := by
  ext
  · simp [D.coordinate_on_other_block hnm]
  · simp [Pi.single_eq_of_ne hnm]

def blockBasisVector : blockIndexSet (fun n => (G n).length) → BlockBasisSpace D G :=
  fun i => let j := (blockIndexEquiv (fun n => (G n).length)).symm i
    blockBasisInjection D G j.1 ((G j.1).complementBasis j.2)

def blockBasisSigmaFunctional (j : Σ n, Fin (G n).length) :
    StrongDual 𝕜 (BlockBasisSpace D G) :=
  (((G j.1).complementBasis.coord j.2).toContinuousLinearMap).comp
    (blockBasisCoordinate D G j.1)

def blockBasisFunctional : blockIndexSet (fun n => (G n).length) →
    StrongDual 𝕜 (BlockBasisSpace D G) :=
  fun i => blockBasisSigmaFunctional D G ((blockIndexEquiv (fun n => (G n).length)).symm i)

@[simp] lemma blockBasisVector_encode (j : Σ n, Fin (G n).length) :
    blockBasisVector D G (blockEncode (fun n => (G n).length) j) =
      blockBasisInjection D G j.1 ((G j.1).complementBasis j.2) := by
  change blockBasisVector D G ((blockIndexEquiv (fun n => (G n).length)) j) = _
  dsimp only [blockBasisVector]
  rw [Equiv.symm_apply_apply]

@[simp] lemma blockBasisFunctional_encode (j : Σ n, Fin (G n).length)
    (x : BlockBasisSpace D G) :
    blockBasisFunctional D G (blockEncode (fun n => (G n).length) j) x =
      (G j.1).complementBasis.repr (blockBasisCoordinate D G j.1 x) j.2 := by
  change blockBasisFunctional D G ((blockIndexEquiv (fun n => (G n).length)) j) x = _
  dsimp only [blockBasisFunctional]
  rw [Equiv.symm_apply_apply]
  rfl

theorem blockBasis_biorthogonal : ∀ i j,
    blockBasisFunctional D G i (blockBasisVector D G j) = if i = j then 1 else 0 := by
  classical
  intro i j
  obtain ⟨⟨n, a⟩, rfl⟩ := blockEncode_surjective (fun n => (G n).length) i
  obtain ⟨⟨m, b⟩, rfl⟩ := blockEncode_surjective (fun n => (G n).length) j
  rw [blockBasisVector_encode, blockBasisFunctional_encode]
  by_cases hnm : n = m
  · subst m
    rw [blockBasisCoordinate_injection]
    have heq : blockEncode (fun n => (G n).length) ⟨n, a⟩ =
        blockEncode (fun n => (G n).length) ⟨n, b⟩ ↔ a = b := by
      constructor
      · intro h
        have hh := blockEncode_injective (fun n => (G n).length) h
        simpa using hh
      · rintro rfl
        rfl
    simp [Basis.repr_self, Finsupp.single_apply, heq, eq_comm]
  · rw [blockBasisCoordinate_injection_of_ne D G hnm]
    have heq : blockEncode (fun n => (G n).length) ⟨n, a⟩ ≠
        blockEncode (fun n => (G n).length) ⟨m, b⟩ := by
      intro h
      exact hnm (congrArg Sigma.fst (blockEncode_injective _ h))
    simp [heq]

def blockBasisFullProjection (N : ℕ) : BlockBasisSpace D G →L[𝕜] BlockBasisSpace D G :=
  ∑ n ∈ range N, (blockBasisInjection D G n).comp (blockBasisCoordinate D G n)

lemma blockBasisFullProjection_apply (N : ℕ) (x : BlockBasisSpace D G) :
    blockBasisFullProjection D G N x =
      (D.projection N x.1, lp2Projection (𝕜 := 𝕜) (range N) x.2) := by
  simp only [blockBasisFullProjection, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, blockBasisCoordinate_apply, blockBasisInjection_apply]
  rw [← D.sum_blockProjection N x.1, lp2Projection_apply]
  simp only [D.coordinate_val]
  induction N with
  | zero =>
      simp only [Finset.sum_range_zero]
      rfl
  | succ N ih =>
      simp only [Finset.sum_range_succ, ih]
      rfl

lemma norm_blockBasisFullProjection_le (N : ℕ) :
    ‖blockBasisFullProjection D G N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [blockBasisFullProjection_apply, Prod.norm_def, one_mul]
  exact max_le
    (((D.projection N).le_opNorm x.1).trans ((mul_le_mul_of_nonneg_right
      (D.norm_le N) (norm_nonneg _)).trans_eq (one_mul _)) |>.trans (norm_fst_le x))
    ((norm_lp2Projection_apply_le (𝕜 := 𝕜) (range N) x.2).trans (norm_snd_le x))

theorem blockBasisFullProjection_tendsto (x : BlockBasisSpace D G) :
    Tendsto (fun N => blockBasisFullProjection D G N x) atTop (𝓝 x) := by
  simpa only [blockBasisFullProjection_apply] using
    (D.tendsto x.1).prodMk_nhds (lp2_nat_truncation_tendsto (𝕜 := 𝕜) x.2)

lemma blockBasisInjection_mem_span (n : ℕ) (x : BlockBasisBlock D G n) :
    blockBasisInjection D G n x ∈ Submodule.span 𝕜 (range (blockBasisVector D G)) := by
  classical
  rw [← (G n).complementBasis.sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨blockEncode (fun n => (G n).length) ⟨n, i⟩, blockBasisVector_encode D G _⟩

theorem blockBasis_span_dense :
    Dense (Submodule.span 𝕜 (range (blockBasisVector D G)) : Set (BlockBasisSpace D G)) := by
  intro x
  apply isClosed_closure.mem_of_tendsto (blockBasisFullProjection_tendsto D G x)
  apply Filter.Eventually.of_forall
  intro N
  apply subset_closure
  simp only [blockBasisFullProjection, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  exact Submodule.sum_mem _ (fun n hn => blockBasisInjection_mem_span D G n _)

end SurveyStatements.P4
