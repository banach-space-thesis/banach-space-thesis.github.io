import SurveyStatements.P1BasicCriterion
import Mathlib.Data.Finsupp.SMul

/-!
Finite sparse coefficients for the rapid flat-block construction. These
lemmas keep gaps in supports and use actual ordered initial projections.
-/

noncomputable section
set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Every coefficient on the finite support is unimodular. -/
def HasFlatCoefficients (b : ℕ →₀ ℂ) : Prop :=
  ∀ i ∈ b.support, b i ∈ unitScalars

/-- The successive finite covers needed by the rapid backward recursion. -/
structure RapidCoverData (e : ℕ → X) (η γ : ℕ → ℝ) where
  m : ℕ → ℕ
  strictMono : StrictMono m
  families : ℕ → Finset (ℕ →₀ ℂ)
  nonempty : ∀ j, (families j).Nonempty
  flat : ∀ j b, b ∈ families j → HasFlatCoefficients b
  support : ∀ j b, b ∈ families j →
    ∀ i ∈ b.support, m j ≤ i ∧ i < m (j + 1)
  norm : ∀ j b, b ∈ families j → |‖Finsupp.linearCombination ℂ e b‖ - 1| ≤ η j
  projection : ∀ j p q r : ℕ, m j ≤ p → p ≤ q → q ≤ r → ∀ a : ℕ → ℂ,
    ‖∑ i ∈ Finset.Icc p q, a i • e i‖ ≤
      (1 + γ j) * ‖∑ i ∈ Finset.Icc p r, a i • e i‖
  cover : ∀ j : ℕ, ∀ z : ℕ →₀ ℂ, HasFlatCoefficients z →
    Finsupp.linearCombination ℂ e z ≠ 0 →
    (∀ i ∈ z.support, m j ≤ i) →
    |‖Finsupp.linearCombination ℂ e z‖ - 1| ≤ η j →
    ∃ b ∈ families j, ∃ θ ∈ unitScalars,
      ‖unitNormalize (Finsupp.linearCombination ℂ e b) -
        θ • unitNormalize (Finsupp.linearCombination ℂ e z)‖ ≤ 1 + η j

theorem flatCoefficients_single (n : ℕ) :
    HasFlatCoefficients (Finsupp.single n (1 : ℂ)) := by
  intro i hi
  have hi' : i = n := by
    by_contra hne
    simp [Finsupp.mem_support_iff, Finsupp.single_apply, hne] at hi
  subst i
  simp [unitScalars]

theorem flatCoefficients_smul {b : ℕ →₀ ℂ} (hb : HasFlatCoefficients b)
    {θ : ℂ} (hθ : θ ∈ unitScalars) : HasFlatCoefficients (θ • b) := by
  intro i hi
  have hb' : b i ≠ 0 := by
    intro hzero
    have hnonzero := Finsupp.mem_support_iff.mp hi
    simp [hzero] at hnonzero
  have hi' : i ∈ b.support := Finsupp.mem_support_iff.mpr hb'
  change ‖θ * b i‖ = 1
  have hbNorm : ‖b i‖ = 1 := hb i hi'
  have hθNorm : ‖θ‖ = 1 := hθ
  rw [norm_mul, hθNorm, hbNorm, mul_one]

theorem flatCoefficients_add {b c : ℕ →₀ ℂ}
    (hb : HasFlatCoefficients b) (hc : HasFlatCoefficients c)
    (hdis : Disjoint b.support c.support) : HasFlatCoefficients (b + c) := by
  intro i hi
  by_cases hib : i ∈ b.support
  · have hic : i ∉ c.support := fun hic => Finset.disjoint_left.mp hdis hib hic
    simpa [Finsupp.notMem_support_iff.mp hic] using hb i hib
  · have hbzero := Finsupp.notMem_support_iff.mp hib
    have hic : i ∈ c.support := by
      apply Finsupp.mem_support_iff.mpr
      simpa [hbzero] using Finsupp.mem_support_iff.mp hi
    simpa [hbzero] using hc i hic

theorem flatCoefficients_sub_phase {b c : ℕ →₀ ℂ}
    (hb : HasFlatCoefficients b) (hc : HasFlatCoefficients c)
    (hdis : Disjoint b.support c.support) {θ : ℂ} (hθ : θ ∈ unitScalars) :
    HasFlatCoefficients (b - θ • c) := by
  have hneg : -θ ∈ unitScalars := by simpa [unitScalars] using hθ
  have hd : Disjoint b.support ((-θ) • c).support :=
    hdis.mono_right Finsupp.support_smul
  simpa [neg_smul, sub_eq_add_neg] using
    flatCoefficients_add hb (flatCoefficients_smul hc hneg) hd

theorem flatCoefficients_isFlatBlock {e : ℕ → X} {b : ℕ →₀ ℂ}
    (hb : HasFlatCoefficients b)
    (hvec : Finsupp.linearCombination ℂ e b ≠ 0) :
    IsFlatBlock e (Finsupp.linearCombination ℂ e b) := by
  refine ⟨hvec, b.support, ?_, b, hb, ?_⟩
  · by_contra h
    have hzero : b = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    simp [hzero] at hvec
  · exact Finsupp.linearCombination_apply ℂ b

theorem phased_coefficient_sum_support (S : Finset ℕ) (b : ℕ → ℕ →₀ ℂ)
    (α : ℕ → ℂ) {p q : ℕ}
    (hsupport : ∀ n ∈ S, ∀ i ∈ (b n).support, p ≤ i ∧ i < q) :
    ∀ i ∈ (∑ n ∈ S, α n • b n).support, p ≤ i ∧ i < q := by
  intro i hi
  have hex : ∃ n ∈ S, i ∈ (b n).support := by
    by_contra h
    push_neg at h
    have hzero : (∑ n ∈ S, α n • b n) i = 0 := by
      simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply]
      exact Finset.sum_eq_zero fun n hn => by
        simp [Finsupp.notMem_support_iff.mp (h n hn)]
    exact (Finsupp.mem_support_iff.mp hi) hzero
  obtain ⟨n, hn, hin⟩ := hex
  exact hsupport n hn i hin

/-- The initial part of a sparse coefficient sum is controlled by the
source's tail-initial monotonicity estimate. -/
theorem sparse_initial_projection_bound {e : ℕ → X} {m N : ℕ} {γ : ℝ}
    (hprojection : ∀ p q r : ℕ, m ≤ p → p ≤ q → q ≤ r → ∀ a : ℕ → ℂ,
      ‖∑ i ∈ Finset.Icc p q, a i • e i‖ ≤
        (1 + γ) * ‖∑ i ∈ Finset.Icc p r, a i • e i‖)
    (b z : ℕ →₀ ℂ) (hN : m < N)
    (hb : ∀ i ∈ b.support, m ≤ i ∧ i < N)
    (hz : ∀ i ∈ z.support, N ≤ i) :
    ‖Finsupp.linearCombination ℂ e b‖ ≤
      (1 + γ) * ‖Finsupp.linearCombination ℂ e (b + z)‖ := by
  classical
  obtain ⟨R, hR⟩ := (b + z).support.exists_nat_subset_range
  let r := max N R
  have hbsub : b.support ⊆ Finset.Icc m (N - 1) := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨(hb i hi).1, by have := (hb i hi).2; omega⟩
  have hsumsub : (b + z).support ⊆ Finset.Icc m r := by
    intro i hi
    have hiR : i < R := Finset.mem_range.mp (hR hi)
    have hlo : m ≤ i := by
      have hiunion := Finsupp.support_add hi
      rcases Finset.mem_union.mp hiunion with hib | hiz
      · exact (hb i hib).1
      · exact hN.le.trans (hz i hiz)
    exact Finset.mem_Icc.mpr ⟨hlo, hiR.le.trans (Nat.le_max_right _ _)⟩
  have hbEq : Finsupp.linearCombination ℂ e b =
      ∑ i ∈ Finset.Icc m (N - 1), (b + z) i • e i := by
    rw [Finsupp.linearCombination_apply_of_mem_supported ℂ hbsub]
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : i < N := by have := Finset.mem_Icc.mp hi; omega
    have hiz : i ∉ z.support := fun hiz => (not_le_of_gt hiN) (hz i hiz)
    simp [Finsupp.notMem_support_iff.mp hiz]
  have hsumEq : Finsupp.linearCombination ℂ e (b + z) =
      ∑ i ∈ Finset.Icc m r, (b + z) i • e i :=
    Finsupp.linearCombination_apply_of_mem_supported ℂ hsumsub
  rw [hbEq, hsumEq]
  exact hprojection m (N - 1) r le_rfl (by omega)
    (by dsimp [r]; omega) (b + z)

end SurveyStatements.P1
