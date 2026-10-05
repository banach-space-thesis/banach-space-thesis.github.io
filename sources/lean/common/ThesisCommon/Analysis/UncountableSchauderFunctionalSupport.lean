import ThesisCommon.Analysis.UncountableSchauderSumSupport
import Mathlib.Analysis.Normed.Operator.NNNorm

/-! Incoming coordinate support of scalar functionals on the genuine
arbitrary-index norm-series sum. Finite permutation symmetry transports a
lower estimate on infinitely many fibres to every finite coefficient family.
This is the phase-alignment argument of manuscript Lemma 4.17.
-/
noncomputable section
open scoped BigOperators
namespace ThesisCommon

/-- A finite collection of indices can be moved into any infinite subset
by a permutation of the whole index type. -/
theorem finite_permutation_into_infinite {Γ : Type*} (F : Finset Γ)
    {A : Set Γ} (hA : A.Infinite) :
    ∃ σ : Equiv.Perm Γ, ∀ γ ∈ F, σ γ ∈ A := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨Equiv.refl Γ, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨σ, hσ⟩ := ih
    obtain ⟨v, hv, hvF⟩ := hA.exists_notMem_finset (F.image σ)
    refine ⟨σ.trans (Equiv.swap (σ a) v), ?_⟩
    intro γ hγ
    rcases Finset.mem_insert.mp hγ with rfl | hγ
    · simpa using hv
    · have h₁ : σ γ ≠ σ a := fun h => ha (σ.injective h ▸ hγ)
      have h₂ : σ γ ≠ v := fun h => hvF (h ▸ Finset.mem_image.mpr ⟨γ, hγ, rfl⟩)
      simpa only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h₁ h₂] using hσ γ hγ

namespace UncountableSchauderSum
variable {𝕜 Γ E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {b : NormalizedSchauderFamily 𝕜 Γ E}

/-- A functional uniformly large on infinitely many unit-ball fibre vectors
forces the outer scalar family to satisfy an ℓ₁ lower estimate. -/
theorem equivalentEllOne_of_large_fibres (hs : b.HasSymmetricNorm)
    (φ : UncountableSchauderSum b hs.1 X →L[𝕜] 𝕜)
    {A : Set Γ} (hA : A.Infinite) (u : Γ → X) {ε : ℝ} (hε : 0 < ε)
    (hu : ∀ γ ∈ A, ‖u γ‖ ≤ 1)
    (hφu : ∀ γ ∈ A, ε ≤ ‖φ (single γ (u γ))‖) : b.EquivalentEllOne := by
  classical
  have hφ : 0 < ‖φ‖ := by
    obtain ⟨γ, hγ⟩ := hA.nonempty
    have hh := (hφu γ hγ).trans (φ.le_opNorm (single γ (u γ)))
    rw [norm_single] at hh
    have hm := mul_le_mul_of_nonneg_left (hu γ hγ) (norm_nonneg φ)
    exact hε.trans_le (hh.trans (by simpa using hm))
  refine ⟨ε / ‖φ‖, div_pos hε hφ, ?_⟩
  intro F a
  obtain ⟨σ, hσ⟩ := finite_permutation_into_infinite F hA
  let G := F.image σ
  have hGA : ∀ γ ∈ G, γ ∈ A := by
    intro γ hγ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hγ
    exact hσ i hi
  let d : Γ → 𝕜 := fun γ => ((ε * ‖a (σ.symm γ)‖ : ℝ) : 𝕜) /
    φ (single γ (u γ))
  have hn (γ : Γ) (hγ : γ ∈ G) : φ (single γ (u γ)) ≠ 0 :=
    norm_pos_iff.mp (hε.trans_le (hφu γ (hGA γ hγ)))
  have hd (γ : Γ) (hγ : γ ∈ G) : ‖d γ‖ ≤ ‖a (σ.symm γ)‖ := by
    dsimp [d]
    rw [norm_div, RCLike.norm_ofReal,
      abs_of_nonneg (mul_nonneg hε.le (norm_nonneg _))]
    apply (div_le_iff₀ (hε.trans_le (hφu γ (hGA γ hγ)))).mpr
    nlinarith [norm_nonneg (a (σ.symm γ)), hφu γ (hGA γ hγ)]
  let z : UncountableSchauderSum b hs.1 X := ∑ γ ∈ G, single γ (d γ • u γ)
  have hnorm : ‖z‖ ≤ ‖∑ i ∈ F, a i • b.vector i‖ := by
    calc
      ‖z‖ = ‖∑ γ ∈ G, (‖d γ • u γ‖ : 𝕜) • b.vector γ‖ := norm_sum_single _ _
      _ ≤ ‖∑ γ ∈ G, a (σ.symm γ) • b.vector γ‖ := by
        have hcoef : ∀ γ ∈ G, ‖(‖d γ • u γ‖ : 𝕜)‖ ≤ ‖a (σ.symm γ)‖ := by
          intro γ hγ
          rw [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), norm_smul]
          exact (mul_le_mul_of_nonneg_left (hu γ (hGA γ hγ)) (norm_nonneg _)).trans
            (by simpa using hd γ hγ)
        simpa only [one_mul] using hs.1.2 G _ _ hcoef
      _ = ‖∑ i ∈ F, a i • b.vector (σ i)‖ := by
        simp [G, Finset.sum_image, σ.injective.injOn]
      _ = ‖∑ i ∈ F, a i • b.vector i‖ := hs.2 σ F a
  have heval : φ z = ((ε * ∑ i ∈ F, ‖a i‖ : ℝ) : 𝕜) := by
    calc
      φ z = ∑ γ ∈ G, d γ * φ (single γ (u γ)) := by
        simp only [z, map_sum, ← singleL_apply, map_smul, smul_eq_mul]
      _ = ∑ γ ∈ G, ((ε * ‖a (σ.symm γ)‖ : ℝ) : 𝕜) := by
        apply Finset.sum_congr rfl
        intro γ hγ
        exact div_mul_cancel₀ _ (hn γ hγ)
      _ = _ := by simp [G, Finset.sum_image, σ.injective.injOn, Finset.mul_sum]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hφ).mpr
  calc
    ε * ∑ i ∈ F, ‖a i‖ = ‖φ z‖ := by
      rw [heval, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    _ ≤ ‖φ‖ * ‖z‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * ‖∑ i ∈ F, a i • b.vector i‖ :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- Positive level sets of the norms of the fibre restrictions are finite.
Otherwise unit-ball witnesses and scalar phases would give the forbidden
outer ℓ₁ lower estimate. -/
theorem functional_finite_large_fibres (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne)
    (φ : UncountableSchauderSum b hs.1 X →L[𝕜] 𝕜) {ε : ℝ} (hε : 0 < ε) :
    {γ : Γ | ε < ‖φ.comp (singleL γ)‖}.Finite := by
  classical
  by_contra hA
  let A : Set Γ := {γ | ε < ‖φ.comp (singleL γ)‖}
  have hw (γ : A) : ∃ x : X, ‖x‖ < 1 ∧ ε < ‖φ (single γ.val x)‖ := by
    simpa only [ContinuousLinearMap.comp_apply, singleL_apply] using
      (φ.comp (singleL γ.val)).exists_lt_apply_of_lt_opNorm γ.property
  choose v hvnorm hvval using hw
  let u : Γ → X := fun γ => if hγ : γ ∈ A then v ⟨γ, hγ⟩ else 0
  apply hnot
  apply equivalentEllOne_of_large_fibres hs φ hA u hε
  · intro γ hγ
    change γ ∈ A at hγ
    dsimp only [u]
    rw [dif_pos hγ]
    exact (hvnorm ⟨γ, hγ⟩).le
  · intro γ hγ
    change γ ∈ A at hγ
    dsimp only [u]
    rw [dif_pos hγ]
    exact (hvval ⟨γ, hγ⟩).le

theorem coordinateProjection_singleton (hb : b.IsOneUnconditional) (γ : Γ)
    (x : UncountableSchauderSum b hb X) :
    coordinateProjection (b := b) (hb := hb) (Y := X) {γ} x = single γ (x γ) := by
  apply UncountableSchauderSum.ext
  intro η
  by_cases h : η = γ
  · subst η; simp
  · simp [h]

/-- A scalar functional annihilates all but countably many full coordinate
fibres. The exceptional set is a countable union of finite positive levels. -/
theorem functional_countable_coordinate_support (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne)
    (φ : UncountableSchauderSum b hs.1 X →L[𝕜] 𝕜) :
    ∃ Δ : Set Γ, Δ.Countable ∧ ∀ γ ∉ Δ,
      φ.comp (coordinateProjection {γ}) = 0 := by
  classical
  let Δ : Set Γ := ⋃ n : ℕ, {γ | 1 / ((n : ℝ) + 1) < ‖φ.comp (singleL γ)‖}
  refine ⟨Δ, Set.countable_iUnion (fun n =>
    (functional_finite_large_fibres hs hnot φ (by positivity : 0 < 1 / ((n : ℝ) + 1))).countable), ?_⟩
  intro γ hγ
  have hz : φ.comp (singleL γ) = 0 := by
    by_contra hn
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hn)
    exact hγ (Set.mem_iUnion.mpr ⟨n, hn⟩)
  apply ContinuousLinearMap.ext
  intro x
  simpa only [ContinuousLinearMap.comp_apply, coordinateProjection_singleton,
    singleL_apply, ContinuousLinearMap.zero_apply] using DFunLike.congr_fun hz (x γ)

end UncountableSchauderSum
end ThesisCommon
