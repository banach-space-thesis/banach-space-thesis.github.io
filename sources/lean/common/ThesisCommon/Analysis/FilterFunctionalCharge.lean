import ThesisCommon.Analysis.FilterConvergenceCriteria
import Mathlib.Analysis.RCLike.Lemmas

/-! Genuine finitely additive charges obtained by evaluating bounded scalar
functionals on indicators. Finite variation is proved by aligning phases on
pairwise disjoint sets; no measure or integral representation is assumed. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ : Type*} [RCLike 𝕜]

def infinityIndicator (A : Set Γ) : lp (fun _ : Γ => 𝕜) ∞ :=
  ⟨fun γ => if γ ∈ A then 1 else 0, memℓp_infty ⟨1, by
    rintro _ ⟨γ, rfl⟩
    by_cases hγ : γ ∈ A <;> simp [hγ]⟩⟩

@[simp] theorem infinityIndicator_apply (A : Set Γ) (γ : Γ) :
    infinityIndicator (𝕜 := 𝕜) A γ = if γ ∈ A then 1 else 0 := rfl

@[simp] theorem infinityIndicator_empty : infinityIndicator (𝕜 := 𝕜) (∅ : Set Γ) = 0 := by
  ext γ
  simp

theorem infinityIndicator_union {A B : Set Γ} (hAB : Disjoint A B) :
    infinityIndicator (𝕜 := 𝕜) (A ∪ B) = infinityIndicator A + infinityIndicator B := by
  ext γ
  have h := Set.disjoint_left.mp hAB
  by_cases hA : γ ∈ A <;> by_cases hB : γ ∈ B
  · exact False.elim (h hA hB)
  · simp [hA, hB]
  · simp [hA, hB]
  · simp [hA, hB]

theorem norm_infinityIndicator_le (A : Set Γ) : ‖infinityIndicator (𝕜 := 𝕜) A‖ ≤ 1 := by
  apply lp.norm_le_of_forall_le zero_le_one
  intro γ
  by_cases hγ : γ ∈ A <;> simp [hγ]

theorem infinity_indicator_synthesis_norm_le {ι : Type*} [Fintype ι]
    (A : ι → Set Γ) (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (c : ι → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) :
    ‖∑ i, c i • infinityIndicator (𝕜 := 𝕜) (A i)‖ ≤ C := by
  classical
  apply lp.norm_le_of_forall_le hC
  intro γ
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    infinityIndicator_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h : ∃ i, γ ∈ A i
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · simpa only [if_pos hi] using hc i
    · intro j _ hji
      have hj : γ ∉ A j := fun hj => Set.disjoint_left.mp (hA hji.symm) hi hj
      simp only [if_neg hj]
    · simp
  · push_neg at h
    simpa only [if_neg (h _), Finset.sum_const_zero, norm_zero] using hC

theorem infinity_functional_disjoint_variation
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) {n : ℕ}
    (A : Fin n → Set Γ) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∑ i, ‖φ (infinityIndicator (A i))‖ ≤ ‖φ‖ := by
  classical
  choose c hc hphase using fun i => RCLike.exists_norm_eq_mul_self (φ (infinityIndicator (A i)))
  have heq : φ (∑ i, c i • infinityIndicator (A i)) =
      ((∑ i, ‖φ (infinityIndicator (A i))‖ : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => (hphase i).symm)
  calc
    _ = ‖φ (∑ i, c i • infinityIndicator (A i))‖ := by
      rw [heq, RCLike.norm_ofReal,
        abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    _ ≤ ‖φ‖ * ‖∑ i, c i • infinityIndicator (A i)‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * 1 := mul_le_mul_of_nonneg_left
      (infinity_indicator_synthesis_norm_le A hA c zero_le_one (fun i => (hc i).le))
      (norm_nonneg φ)
    _ = _ := mul_one _

def functionalCharge (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) :
    BoundedScalarCharge 𝕜 Γ where
  toFun A := φ (infinityIndicator A)
  map_empty := by rw [infinityIndicator_empty, map_zero]
  map_union A B h := by rw [infinityIndicator_union h, map_add]
  bounded_variation := ⟨‖φ‖, norm_nonneg _, fun _ A hA =>
    infinity_functional_disjoint_variation φ A hA⟩

@[simp] theorem functionalCharge_apply (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜)
    (A : Set Γ) : functionalCharge φ A = φ (infinityIndicator A) := rfl

theorem functionalCharge_variation_le (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜)
    (A : Set Γ) : (functionalCharge φ).variation A ≤ ‖φ‖ := by
  apply csSup_le ((functionalCharge φ).variationValues_nonempty A)
  rintro r ⟨n, B, hB, _, rfl⟩
  exact infinity_functional_disjoint_variation φ B hB

theorem functionalCharge_family_le_variation
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) {n : ℕ}
    (B : Fin n → Set Γ) (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    {A : Set Γ} (hBA : ∀ i, B i ⊆ A) :
    ∑ i, ‖φ (infinityIndicator (B i))‖ ≤ (functionalCharge φ).variation A := by
  apply le_csSup ((functionalCharge φ).variationValues_bddAbove A)
  exact ⟨n, B, hB, hBA, rfl⟩

theorem functionalCharge_simple_bound
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) {n : ℕ}
    (B : Fin n → Set Γ) (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    {A : Set Γ} (hBA : ∀ i, B i ⊆ A) (c : Fin n → 𝕜) {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) :
    ‖φ (∑ i, c i • infinityIndicator (B i))‖ ≤ (functionalCharge φ).variation A * C := by
  calc
    _ = ‖∑ i, c i * φ (infinityIndicator (B i))‖ := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ ≤ ∑ i, ‖c i * φ (infinityIndicator (B i))‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * ‖φ (infinityIndicator (B i))‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
    _ = C * ∑ i, ‖φ (infinityIndicator (B i))‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (functionalCharge φ).variation A :=
      mul_le_mul_of_nonneg_left (functionalCharge_family_le_variation φ B hB hBA) hC
    _ = _ := mul_comm _ _

end ThesisCommon
