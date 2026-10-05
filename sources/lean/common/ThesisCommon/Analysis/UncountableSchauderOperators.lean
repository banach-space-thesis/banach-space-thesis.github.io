import ThesisCommon.Analysis.SchauderSymmetry
import ThesisCommon.Analysis.UncountableSchauderSolidity
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! Construct bounded operators from finite-sum estimates on a Schauder
basis. The construction starts on the actual algebraic span and extends by
continuity along its dense inclusion. It is not an assumed extension axiom.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
namespace NormalizedSchauderFamily
variable {𝕜 Γ X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable (b : NormalizedSchauderFamily 𝕜 Γ X)


/-- Symmetry controls every finite part of an arbitrary coordinate injection. -/
theorem finite_subsequence_norm (hb : b.HasSymmetricNorm)
    (f : Γ ↪ Γ) (F : Finset Γ) (a : Γ → 𝕜) :
    ‖∑ n ∈ F, a n • b.vector (f n)‖ = ‖∑ n ∈ F, a n • b.vector n‖ := by
  obtain ⟨σ, hσ⟩ := finite_embedding_extends_permutation f F
  calc
    _ = ‖∑ n ∈ F, a n • b.vector (σ n)‖ := by
      congr 1
      exact Finset.sum_congr rfl (fun n hn => by rw [hσ n hn])
    _ = _ := hb.2 σ F a
theorem linearIndependent : LinearIndependent 𝕜 b.vector := by
  classical
  rw [linearIndependent_iff']
  intro F a h i hi
  have hh := congrArg (b.coord i) h
  simpa only [b.coord_finite_sum, if_pos hi, map_zero] using hh

/-- The algebraic span of the basis is norm dense. -/
theorem dense_span : DenseRange (Submodule.span 𝕜 (Set.range b.vector)).subtypeL := by
  intro x
  apply isClosed_closure.mem_of_tendsto (b.expansion x)
  apply Filter.Eventually.of_forall
  intro N
  apply subset_closure
  refine ⟨⟨_, ?_⟩, rfl⟩
  change (∑ n ∈ N, b.coord n x • b.vector n) ∈
    Submodule.span 𝕜 (Set.range b.vector)
  apply Submodule.sum_mem
  intro n _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

/-- A finite-sum operator estimate constructs a bounded map on the entire
space, with exactly the same bound and exactly the prescribed basis values. -/
theorem exists_operator [CompleteSpace Y] (v : Γ → Y) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ (F : Finset Γ) (a : Γ → 𝕜),
      ‖∑ n ∈ F, a n • v n‖ ≤ C * ‖∑ n ∈ F, a n • b.vector n‖) :
    ∃ T : X →L[𝕜] Y, ‖T‖ ≤ C ∧ ∀ n, T (b.vector n) = v n := by
  classical
  let S := Submodule.span 𝕜 (Set.range b.vector)
  let L : S →ₗ[𝕜] Y := (Finsupp.linearCombination 𝕜 v).comp b.linearIndependent.repr
  have hL (x : S) : ‖L x‖ ≤ C * ‖x‖ := by
    have hh := hv (b.linearIndependent.repr x).support (b.linearIndependent.repr x)
    change ‖Finsupp.linearCombination 𝕜 v (b.linearIndependent.repr x)‖ ≤
      C * ‖Finsupp.linearCombination 𝕜 b.vector (b.linearIndependent.repr x)‖ at hh
    simpa only [b.linearIndependent.linearCombination_repr] using hh
  let F : S →L[𝕜] Y := L.mkContinuous C hL
  have hu : IsUniformInducing S.subtypeL := isometry_subtype_coe.isUniformInducing
  let T : X →L[𝕜] Y := F.extend S.subtypeL b.dense_span hu
  have he (x : S) : T x = F x := ContinuousLinearMap.extend_eq _ _ _ _ x
  refine ⟨T, ?_, ?_⟩
  · apply T.opNorm_le_bound hC
    intro x
    refine b.dense_span.induction_on x
      (isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)) ?_
    intro y
    change ‖T (y : X)‖ ≤ C * ‖y‖
    rw [he]
    exact hL y
  · intro n
    let x : S := ⟨b.vector n, Submodule.subset_span ⟨n, rfl⟩⟩
    change T (x : X) = v n
    rw [he]
    change Finsupp.linearCombination 𝕜 v (b.linearIndependent.repr x) = v n
    rw [b.linearIndependent.repr_eq_single n x rfl]
    simp

/-- Continuous operators agreeing on every basis vector agree everywhere. -/
theorem operator_ext {S T : X →L[𝕜] Y} (h : ∀ n, S (b.vector n) = T (b.vector n)) :
    S = T := by
  apply ContinuousLinearMap.ext
  intro x
  have hs := (S.continuous.tendsto x).comp (b.expansion x)
  have ht := (T.continuous.tendsto x).comp (b.expansion x)
  apply tendsto_nhds_unique hs
  convert ht using 1
  ext N
  simp only [Function.comp_apply, map_sum, map_smul, h]

/-- A symmetric basis supplies genuine isometric subsequence insertions.
Isometry on the whole space follows by passing finite-sum equalities to limits. -/
theorem exists_subsequence_insertion [CompleteSpace X] (hb : b.HasSymmetricNorm)
    (f : Γ ↪ Γ) : ∃ B : X →L[𝕜] X,
      ‖B‖ ≤ 1 ∧ (∀ x, ‖B x‖ = ‖x‖) ∧ ∀ n, B (b.vector n) = b.vector (f n) := by
  obtain ⟨B, hB, hBe⟩ := b.exists_operator (fun n => b.vector (f n)) zero_le_one
    (fun F a => by rw [b.finite_subsequence_norm hb, one_mul])
  refine ⟨B, hB, ?_, hBe⟩
  intro x
  have ht := ((B.continuous.tendsto x).comp (b.expansion x)).norm
  apply tendsto_nhds_unique ht
  convert (b.expansion x).norm using 1
  funext N
  simp only [Function.comp_apply, map_sum, map_smul, hBe]
  exact b.finite_subsequence_norm hb f _ _

/-- Restriction and insertion for a symmetric basis, both constructed from
finite-sum bounds. Restriction extracts exactly the chosen coordinates. -/
theorem exists_subsequence_compression [Nonempty Γ] [CompleteSpace X] (hb : b.HasSymmetricNorm)
    (f : Γ ↪ Γ) : ∃ A B : X →L[𝕜] X,
      A.comp B = ContinuousLinearMap.id 𝕜 X ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      (∀ n, B (b.vector n) = b.vector (f n)) ∧
      ∀ i x, b.coord i (A x) = b.coord (f i) x := by
  classical
  obtain ⟨B, hB, hBnorm, hBe⟩ := b.exists_subsequence_insertion hb f
  let v : Γ → X := fun n => if n ∈ Set.range f then
    b.vector (Function.invFun f n) else 0
  have hvin (n : Γ) : v (f n) = b.vector n := by
    simp only [v, if_pos (Set.mem_range_self n)]
    rw [Function.leftInverse_invFun f.injective n]
  have hBv (n : Γ) : B (v n) = if n ∈ Set.range f then b.vector n else 0 := by
    by_cases hn : n ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hn
      rw [hvin, hBe, if_pos (Set.mem_range_self i)]
    · simp only [v, if_neg hn, map_zero]
  have hv (F : Finset Γ) (a : Γ → 𝕜) :
      ‖∑ n ∈ F, a n • v n‖ ≤ 1 * ‖∑ n ∈ F, a n • b.vector n‖ := by
    rw [← hBnorm, map_sum]
    simp only [map_smul, hBv]
    have hh := hb.1.2 F (fun n => if n ∈ Set.range f then a n else 0) a (by
      intro n _
      dsimp only
      split_ifs <;> simp)
    simpa only [ite_smul, zero_smul, smul_ite, smul_zero] using hh
  obtain ⟨A, hA, hAe⟩ := b.exists_operator v zero_le_one hv
  have hcoord (i : Γ) : (b.coord i).comp A = b.coord (f i) := by
    apply b.operator_ext
    intro n
    simp only [ContinuousLinearMap.comp_apply, hAe]
    by_cases hn : n ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hn
      rw [hvin, b.biorthogonal, b.biorthogonal]
      simp only [f.injective.eq_iff]
    · have hi : f i ≠ n := fun heq => hn ⟨i, heq⟩
      simp only [v, if_neg hn, map_zero, b.biorthogonal, if_neg hi]
  refine ⟨A, B, ?_, hA, hB, hBe, ?_⟩
  · apply b.operator_ext
    intro n
    simp only [ContinuousLinearMap.comp_apply, hBe, hAe, hvin,
      ContinuousLinearMap.id_apply]
  · intro i x
    exact DFunLike.congr_fun (hcoord i) x


/-- An insertion's action on all coordinates follows from its basis action,
including zero values outside the image of the coordinate injection. -/
theorem coord_insertion (f : Γ ↪ Γ) (B : X →L[𝕜] X)
    (hBe : ∀ n, B (b.vector n) = b.vector (f n)) (x : X) (j : Γ) :
    b.coord j (B x) =
      if h : j ∈ Set.range f then b.coord h.choose x else 0 := by
  classical
  let ψ : X →L[𝕜] 𝕜 := if h : j ∈ Set.range f then b.coord h.choose else 0
  have he : (b.coord j).comp B = ψ := by
    apply b.operator_ext
    intro n
    simp only [ContinuousLinearMap.comp_apply, hBe]
    by_cases hj : j ∈ Set.range f
    · have hf : f hj.choose = j := hj.choose_spec
      simp only [ψ, dif_pos hj, b.biorthogonal]
      have hiff : j = f n ↔ hj.choose = n :=
        ⟨fun h => f.injective (hf.trans h), fun h => hf.symm.trans (congrArg f h)⟩
      simp only [hiff]
    · have hne : j ≠ f n := fun h => hj ⟨n, h.symm⟩
      simp only [ψ, dif_neg hj, b.biorthogonal, if_neg hne,
        ContinuousLinearMap.zero_apply]
  have hh := DFunLike.congr_fun he x
  by_cases hj : j ∈ Set.range f
  · simpa only [ψ, dif_pos hj, ContinuousLinearMap.comp_apply] using hh
  · simpa only [ψ, dif_neg hj, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] using hh

end NormalizedSchauderFamily
end ThesisCommon

