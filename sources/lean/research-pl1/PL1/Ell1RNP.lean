import PL1.ScalarDecompositionRNP
import PL1.L1Sum
import PL1.SingularResolvents
import PL1.RNPTransport

/-! # Full RNP of genuine scalar ℓ₁ and the resulting isomorphism obstruction -/

noncomputable section
universe u v
open Filter
open scoped Topology ENNReal BigOperators

namespace PL1.Ell1RNP

variable (K : Type*) [RCLike K]

def coordinate (j : ℕ) : Ell1 K →L[K] Ell1 K :=
  (lp.singleContinuousLinearMap K (fun _ : ℕ => K) 1 j).comp
    (lp.evalCLM K (fun _ : ℕ => K) 1 j)

def projection (N : ℕ) : Ell1 K →L[K] Ell1 K :=
  ∑ j ∈ Finset.range (N + 1), coordinate K j

theorem projection_apply (N : ℕ) (x : Ell1 K) :
    projection K N x = ∑ j ∈ Finset.range (N + 1), lp.single 1 j (x j) := by
  simp only [projection, sum_apply, coordinate,
    ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
  rfl

theorem projection_apply_coordinate (N : ℕ) (x : Ell1 K) (j : ℕ) :
    projection K N x j = if j ≤ N then x j else 0 := by
  rw [projection_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single,
    Finset.mem_range, Nat.lt_succ_iff]

theorem projection_comp (m n : ℕ) (hmn : m ≤ n) :
    (projection K m).comp (projection K n) = projection K m := by
  ext x j
  simp only [ContinuousLinearMap.comp_apply, projection_apply_coordinate]
  by_cases hj : j ≤ m
  · simp [hj, hj.trans hmn]
  · simp [hj]

def finiteSpan (N : ℕ) : Submodule K (Ell1 K) :=
  Submodule.span K ((fun j => lp.single 1 j (1 : K)) '' (Finset.range (N + 1) : Set ℕ))

instance finiteDimensional_span (N : ℕ) : FiniteDimensional K (finiteSpan K N) :=
  FiniteDimensional.span_of_finite K
    ((Finset.finite_toSet (Finset.range (N + 1))).image _)

theorem projection_mem_span (N : ℕ) (x : Ell1 K) : projection K N x ∈ finiteSpan K N := by
  rw [projection_apply]
  apply Submodule.sum_mem
  intro j hj
  have h : lp.single 1 j (1 : K) ∈ finiteSpan K N :=
    Submodule.subset_span ⟨j, hj, rfl⟩
  have hs := (finiteSpan K N).smul_mem (x j) h
  simpa only [← lp.single_smul, smul_eq_mul, mul_one] using hs

instance finiteDimensional_range (N : ℕ) : FiniteDimensional K (projection K N).range := by
  have hle : (projection K N).range ≤ finiteSpan K N := by
    rintro x ⟨y, rfl⟩
    exact projection_mem_span K N y
  exact FiniteDimensional.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective _)

theorem norm_projection_apply_le (N : ℕ) (x : Ell1 K) : ‖projection K N x‖ ≤ ‖x‖ := by
  rw [projection_apply]
  have h := lp.norm_sum_single (p := 1) (by norm_num) (fun j => x j)
    (Finset.range (N + 1))
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  rw [h, L1Sum.norm_eq_tsum]
  exact (L1Sum.summable_norm x).sum_le_tsum _ (fun _ _ => norm_nonneg _)

theorem norm_projection_le (N : ℕ) : ‖projection K N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
    intro x
    simpa using norm_projection_apply_le K N x)

theorem tendsto_projection (x : Ell1 K) :
    Tendsto (fun N => projection K N x) atTop (𝓝 x) := by
  simpa only [projection_apply, Function.comp_def] using
    ((lp.hasSum_single (p := 1) (by norm_num) x).tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1))

theorem boundedlyComplete : ScalarDecompositionRNP.BoundedlyComplete (projection K) := by
  intro x hx hbounded
  obtain ⟨M, hM⟩ := hbounded
  let a : ℕ → K := fun j => x j j
  have hcoord (N j : ℕ) (hj : j ≤ N) : x N j = a j := by
    have h := congrArg (fun z : Ell1 K => z j) (hx j N hj)
    simpa only [projection_apply_coordinate, le_refl, ite_true] using h
  have hs : Summable (fun j => ‖a j‖) := by
    apply summable_of_sum_range_le (fun _ => norm_nonneg _) (c := M)
    intro N
    calc
      ∑ j ∈ Finset.range N, ‖a j‖ = ∑ j ∈ Finset.range N, ‖x N j‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoord N j (Nat.le_of_lt (Finset.mem_range.mp hj))]
      _ ≤ ‖x N‖ := by
        rw [L1Sum.norm_eq_tsum]
        exact (L1Sum.summable_norm (x N)).sum_le_tsum _ (fun _ _ => norm_nonneg _)
      _ ≤ M := hM N
  let z : Ell1 K := ⟨a, memℓp_gen (by simpa using hs)⟩
  have heq (N : ℕ) : x N = projection K N z := by
    ext j
    rw [projection_apply_coordinate]
    by_cases hj : j ≤ N
    · simp only [hj, ite_true]
      exact hcoord N j hj
    · have h := congrArg (fun w : Ell1 K => w j) (hx N N le_rfl)
      simpa only [projection_apply_coordinate, hj, ite_false] using h.symm
  exact ⟨z, (tendsto_projection K z).congr' (Filter.Eventually.of_forall (fun N => (heq N).symm))⟩

theorem hasRadonNikodymProperty :
    @PL1.HasRadonNikodymProperty.{_, v} (UnderlyingReal K (Ell1 K))
      (inferInstanceAs (NormedAddCommGroup (Ell1 K))) (NormedSpace.restrictScalars ℝ K (Ell1 K)) :=
  ScalarDecompositionRNP.hasRNP_of_scalar_projections (projection K)
    (finiteDimensional_range K) (projection_comp K) ⟨1, norm_projection_le K⟩
    (tendsto_projection K) (boundedlyComplete K)

theorem not_isomorphic_of_not_RNP {E : Type u} [NormedAddCommGroup E] [NormedSpace K E]
    (hE : ¬ @PL1.HasRadonNikodymProperty.{u, 0} (UnderlyingReal K E)
      (inferInstanceAs (NormedAddCommGroup E)) (NormedSpace.restrictScalars ℝ K E)) :
    IsEmpty (E ≃L[K] Ell1 K) := by
  refine ⟨fun e => ?_⟩
  exact hE ((RNPTransport.hasRadonNikodymProperty_restrictScalars_iff e).mpr
    (hasRadonNikodymProperty K))

theorem schur_intrinsic_not_isomorphic_ell1 :
    IsEmpty ((Noise.dyadicSystem K Noise.schurRates).IntrinsicSpace ≃L[K] Ell1 K) := by
  refine ⟨fun e => ?_⟩
  exact Noise.schur_intrinsic_not_RNP K
    ((RNPTransport.hasRadonNikodymProperty_restrictScalars_iff e).mpr
      (hasRadonNikodymProperty K))

theorem constant_intrinsic_not_isomorphic_ell1 :
    IsEmpty ((Noise.dyadicSystem K Noise.constantRates).IntrinsicSpace ≃L[K] Ell1 K) := by
  refine ⟨fun e => ?_⟩
  exact Noise.constant_intrinsic_not_RNP K
    ((RNPTransport.hasRadonNikodymProperty_restrictScalars_iff e).mpr
      (hasRadonNikodymProperty K))

theorem schur_projection_range_not_isomorphic_ell1 :
    IsEmpty ((Noise.projection K Noise.schurRates).range ≃L[K] Ell1 K) :=
  not_isomorphic_of_not_RNP K (Noise.schur_projection_range_not_RNP K)

theorem constant_projection_range_not_isomorphic_ell1 :
    IsEmpty ((Noise.projection K Noise.constantRates).range ≃L[K] Ell1 K) :=
  not_isomorphic_of_not_RNP K (Noise.constant_projection_range_not_RNP K)

end PL1.Ell1RNP
