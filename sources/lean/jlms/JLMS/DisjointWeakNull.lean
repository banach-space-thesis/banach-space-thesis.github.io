import JLMS.Rudin
import JLMS.DisjointSynthesis

/-!
# Weak convergence of disjoint functions

Rudin for the discrete space ℕ identifies every functional on c₀ with an
absolutely summable sequence. Its values on the coordinate vectors therefore
tend to zero. The disjoint synthesis contraction transfers this fact to every
disjoint sequence in the unit ball of C₀(K), and then to its operator images.
This is the weak-null input to the cited factorization argument.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Every discrete space is scattered. -/
theorem isScattered_discrete (I : Type*) [TopologicalSpace I] [DiscreteTopology I] :
    IsScattered I := by
  intro s hs
  obtain ⟨x, hx⟩ := hs
  refine ⟨x, hx, {x}, isOpen_discrete _, ?_⟩
  exact Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hx)

/-- The coefficients of an ℓ¹ sequence tend to zero. -/
theorem ellOne_tendsto_zero (a : ellOne 𝕜) : Tendsto a atTop (𝓝 0) := by
  have h := (ellOneOn_summable_norm a).tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop] at h
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h

/-- The canonical coordinate vectors of c₀ are weakly null. -/
@[simp] theorem atomicFunctional_cZeroUnit (a : ellOne 𝕜) (n : ℕ) :
    atomicFunctional a (cZeroUnit 𝕜 n) = a n := by
  change (∑' m, a m * cZeroUnit 𝕜 n m) = a n
  rw [tsum_eq_single n]
  · simp
  · intro m hmn
    simp [hmn]

/-- The canonical coordinate vectors of c₀ are weakly null. -/
theorem weakNull_cZero_units (φ : cZero 𝕜 →L[𝕜] 𝕜) :
    Tendsto (fun n => φ (cZeroUnit 𝕜 n)) atTop (𝓝 0) := by
  obtain ⟨a, rfl⟩ := atomicSynthesis_surjective (𝕜 := 𝕜) (isScattered_discrete ℕ) φ
  simp only [atomicSynthesis_apply, atomicFunctional_cZeroUnit]
  exact ellOne_tendsto_zero a

/-- The mass of any finite set of dual coordinate values is bounded by the norm. -/
theorem cZero_dual_finite_coordinate_mass (φ : cZero 𝕜 →L[𝕜] 𝕜) (t : Finset ℕ) :
    ∑ j ∈ t, ‖φ (cZeroUnit 𝕜 j)‖ ≤ ‖φ‖ := by
  obtain ⟨a, rfl⟩ := atomicSynthesis_surjective (𝕜 := 𝕜) (isScattered_discrete ℕ) φ
  simp only [atomicSynthesis_apply, atomicFunctional_cZeroUnit]
  change (∑ j ∈ t, ‖a j‖) ≤ ‖atomicFunctional a‖
  rw [norm_atomicFunctional (isScattered_discrete ℕ), ellOneOn_norm_eq_tsum]
  exact (ellOneOn_summable_norm a).sum_le_tsum t (fun _ _ => norm_nonneg _)

variable {K : Type*} [TopologicalSpace K]

/-- A disjoint unit-ball sequence in C₀(K) is weakly null, for arbitrary K. -/
theorem weakNull_disjointFunctions (η : ℕ → CZero 𝕜 K) (hunit : ∀ n, ‖η n‖ ≤ 1)
    (hd : Pairwise fun i j => Disjoint (Function.support (η i)) (Function.support (η j)))
    (φ : CZero 𝕜 K →L[𝕜] 𝕜) : Tendsto (fun n => φ (η n)) atTop (𝓝 0) := by
  simpa only [ContinuousLinearMap.comp_apply, disjointSynthesis_unit] using
    weakNull_cZero_units (φ.comp (disjointSynthesis η hunit hd))

/-- Bounded operators preserve the weak-null disjoint sequence. -/
theorem weakNull_disjointImages {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (η : ℕ → CZero 𝕜 K) (hunit : ∀ n, ‖η n‖ ≤ 1)
    (hd : Pairwise fun i j => Disjoint (Function.support (η i)) (Function.support (η j)))
    (T : CZero 𝕜 K →L[𝕜] X) (φ : X →L[𝕜] 𝕜) :
    Tendsto (fun n => φ (T (η n))) atTop (𝓝 0) :=
  weakNull_disjointFunctions η hunit hd (φ.comp T)

end JLMS
