import SurveyStatements.P1C0Sequence
import SurveyStatements.P1BasicCriterion
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Actual finitely supported vectors in complex c₀ and stabilization of
the tail operator norms of an arbitrary isomorphic embedding. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

def c0Finsupp (b : ℕ →₀ ℂ) : ComplexC0 where
  toFun := b
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) (cocompact ℕ) (𝓝 0)).congr'
    filter_upwards [b.support.finite_toSet.isCompact.compl_mem_cocompact] with i hi
    exact (Finsupp.notMem_support_iff.mp hi).symm

@[simp] theorem c0Finsupp_apply (b : ℕ →₀ ℂ) (i : ℕ) : c0Finsupp b i = b i := rfl

def c0FinsuppLinear : (ℕ →₀ ℂ) →ₗ[ℂ] ComplexC0 where
  toFun := c0Finsupp
  map_add' a b := by ext i; rfl
  map_smul' z b := by ext i; rfl

theorem norm_c0Finsupp_le {b : ℕ →₀ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, ‖b i‖ ≤ C) : ‖c0Finsupp b‖ ≤ C := by
  change ‖(c0Finsupp b).toBCF‖ ≤ C
  exact (BoundedContinuousFunction.norm_le hC).mpr hb

theorem c0Finsupp_apply_norm_le (b : ℕ →₀ ℂ) (i : ℕ) : ‖b i‖ ≤ ‖c0Finsupp b‖ :=
  (c0Finsupp b).toBCF.norm_coe_le_norm i

@[simp] theorem norm_c0Finsupp_single (i : ℕ) :
    ‖c0Finsupp (Finsupp.single i 1)‖ = 1 := by
  apply le_antisymm
  · apply norm_c0Finsupp_le (by norm_num)
    intro k
    by_cases hk : k = i <;> simp [Finsupp.single_apply, hk]
  · simpa using c0Finsupp_apply_norm_le (Finsupp.single i 1) i

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def c0TailNorms (T : ComplexC0 →L[ℂ] X) (N : ℕ) : Set ℝ :=
  {t | ∃ b : ℕ →₀ ℂ, (∀ i ∈ b.support, N ≤ i) ∧
    (∀ i, ‖b i‖ ≤ 1) ∧ t = ‖T (c0Finsupp b)‖}

def c0TailUpperNorm (T : ComplexC0 →L[ℂ] X) (N : ℕ) : ℝ := sSup (c0TailNorms T N)

theorem c0TailNorms_nonempty (T : ComplexC0 →L[ℂ] X) (N : ℕ) :
    (c0TailNorms T N).Nonempty := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · simp
  · simp
  · have hzero : c0Finsupp 0 = 0 := by ext i; rfl
    simp [hzero]

theorem c0TailNorms_bddAbove (T : ComplexC0 →L[ℂ] X) (N : ℕ) :
    BddAbove (c0TailNorms T N) := by
  refine ⟨‖T‖, ?_⟩
  rintro t ⟨b, _, hb, rfl⟩
  exact (T.le_opNorm _).trans (by
    simpa using mul_le_mul_of_nonneg_left (norm_c0Finsupp_le (by norm_num) hb) (norm_nonneg T))

theorem norm_c0Finsupp_image_le_tail (T : ComplexC0 →L[ℂ] X) (N : ℕ) (b : ℕ →₀ ℂ)
    (hsupp : ∀ i ∈ b.support, N ≤ i) (hb : ∀ i, ‖b i‖ ≤ 1) :
    ‖T (c0Finsupp b)‖ ≤ c0TailUpperNorm T N :=
  le_csSup (c0TailNorms_bddAbove T N) ⟨b, hsupp, hb, rfl⟩

theorem c0TailUpperNorm_bounds (T : ComplexC0 →L[ℂ] X) {L : ℝ}
    (hlower : ∀ v : ComplexC0, L * ‖v‖ ≤ ‖T v‖) (N : ℕ) :
    L ≤ c0TailUpperNorm T N ∧ c0TailUpperNorm T N ≤ ‖T‖ := by
  constructor
  · have hsupp : ∀ i ∈ (Finsupp.single N (1 : ℂ)).support, N ≤ i := by
      intro i hi
      have hiN : i = N := by
        simpa only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] using hi
      omega
    have hunit : ∀ i, ‖(Finsupp.single N (1 : ℂ)) i‖ ≤ 1 := by
      intro i
      by_cases hi : i = N <;> simp [Finsupp.single_apply, hi]
    have hsingle : L ≤ ‖T (c0Finsupp (Finsupp.single N 1))‖ := by
      simpa using hlower (c0Finsupp (Finsupp.single N 1))
    exact hsingle.trans
      (norm_c0Finsupp_image_le_tail T N (Finsupp.single N 1) hsupp hunit)
  · apply csSup_le (c0TailNorms_nonempty T N)
    rintro t ⟨b, _, hb, rfl⟩
    exact (T.le_opNorm _).trans (by
      simpa using mul_le_mul_of_nonneg_left (norm_c0Finsupp_le (by norm_num) hb) (norm_nonneg T))

/-- Finite tail upper norms approach a positive limit; every later tail
contains a coefficient-unit block with image norm above 99 percent of it. -/
theorem c0TailUpperNorm_stabilizes (T : ComplexC0 →L[ℂ] X) {L : ℝ} (hL : 0 < L)
    (hlower : ∀ v : ComplexC0, L * ‖v‖ ≤ ‖T v‖) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ,
      c0TailUpperNorm T N < (101 / 100 : ℝ) * B ∧
      ∀ M : ℕ, ∃ b : ℕ →₀ ℂ, (∀ i ∈ b.support, M ≤ i) ∧
        (∀ i, ‖b i‖ ≤ 1) ∧ (99 / 100 : ℝ) * B < ‖T (c0Finsupp b)‖ := by
  let B : ℝ := sInf (Set.range (c0TailUpperNorm T))
  have hB : BddBelow (Set.range (c0TailUpperNorm T)) := by
    refine ⟨L, ?_⟩
    rintro t ⟨n, rfl⟩
    exact (c0TailUpperNorm_bounds T hlower n).1
  have hle (n : ℕ) : B ≤ c0TailUpperNorm T n := csInf_le hB ⟨n, rfl⟩
  have hBL : L ≤ B := by
    apply le_csInf (Set.range_nonempty _)
    rintro t ⟨n, rfl⟩
    exact (c0TailUpperNorm_bounds T hlower n).1
  have hBpos : 0 < B := hL.trans_le hBL
  obtain ⟨t, ⟨N, rfl⟩, hN⟩ := exists_lt_of_csInf_lt (Set.range_nonempty (c0TailUpperNorm T))
    (show B < (101 / 100 : ℝ) * B by linarith)
  refine ⟨B, hBpos, N, hN, ?_⟩
  intro M
  obtain ⟨t, ⟨b, hsupp, hb, rfl⟩, hnorm⟩ := exists_lt_of_lt_csSup (c0TailNorms_nonempty T M)
    (show (99 / 100 : ℝ) * B < c0TailUpperNorm T M from
      (by linarith : (99 / 100 : ℝ) * B < B).trans_le (hle M))
  exact ⟨b, hsupp, hb, hnorm⟩

end SurveyStatements.P1
