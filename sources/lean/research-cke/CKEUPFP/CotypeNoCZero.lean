import CKEUPFP.DefinitionEquivalences
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Finite cotype excludes isomorphic copies of c₀

The finite-sign cotype definition and the two elementary estimates are adapted
from the supplied local sources `ThesisCommon/Analysis/Cotype.lean` and
`CotypeEstimates.lean`. The coordinate signed-sum argument follows
`ThesisCommon/Analysis/DisjointSequenceBlocks.lean`. All proofs are included
here; no theorem from that external project is assumed or imported.

An embedding of c₀ sends its unit coordinate vectors to vectors with a common
positive lower norm bound. Every finite signed sum has a common upper bound.
The cotype inequality contradicts these bounds for sufficiently many vectors.
This module does not assert cotype of any particular Lp or ℓp space.
-/

noncomputable section

universe u v

namespace CKEUPFP

open scoped BigOperators ZeroAtInfty

variable (E : Type v) [NormedAddCommGroup E]

/-- The finite uniform Rademacher cotype inequality, in the q-moment
convention. The expectation is the average over exactly `2^n` sign vectors. -/
def HasRademacherCotype (q C : ℝ) : Prop :=
  2 ≤ q ∧ 1 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
    (∑ i, ‖x i‖ ^ q) ≤
      C ^ q * ((2 : ℝ) ^ n)⁻¹ *
        ∑ ε : Fin n → Bool, ‖∑ i, if ε i then x i else -x i‖ ^ q

/-- One finite exponent and one constant work for every finite vector family. -/
def HasFiniteCotype : Prop := ∃ q C : ℝ, HasRademacherCotype E q C

variable {E}

/-- A bound on every signed sum bounds the cotype power sum. -/
theorem HasRademacherCotype.sum_rpow_le_of_sign_bound {q C : ℝ}
    (h : HasRademacherCotype E q C) {n : ℕ} (x : Fin n → E)
    {M : ℝ} (_hM : 0 ≤ M)
    (hsign : ∀ ε : Fin n → Bool, ‖∑ i, if ε i then x i else -x i‖ ≤ M) :
    ∑ i, ‖x i‖ ^ q ≤ C ^ q * M ^ q := by
  have hq : 0 ≤ q := (by norm_num : (0 : ℝ) ≤ 2).trans h.1
  have hC : 0 ≤ C := zero_le_one.trans h.2.1
  have hc : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  have hsum : (∑ ε : Fin n → Bool, ‖∑ i, if ε i then x i else -x i‖ ^ q)
      ≤ (2 : ℝ) ^ n * M ^ q := by
    calc
      _ ≤ ∑ _ε : Fin n → Bool, M ^ q := Finset.sum_le_sum fun ε _ =>
        Real.rpow_le_rpow (norm_nonneg _) (hsign ε) hq
      _ = _ := by simp [hc]
  calc
    _ ≤ C ^ q * ((2 : ℝ) ^ n)⁻¹ *
        ∑ ε : Fin n → Bool, ‖∑ i, if ε i then x i else -x i‖ ^ q := h.2.2 n x
    _ ≤ C ^ q * ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n * M ^ q) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

/-- A sufficiently large finite family with bounded signed sums contains a
vector below any prescribed positive lower norm bound. -/
theorem HasRademacherCotype.exists_norm_lt_of_sign_bound {q C : ℝ}
    (h : HasRademacherCotype E q C) {n : ℕ} (x : Fin n → E)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hsign : ∀ ε : Fin n → Bool, ‖∑ i, if ε i then x i else -x i‖ ≤ M)
    (hlarge : C ^ q * M ^ q < (n : ℝ) * δ ^ q) :
    ∃ i, ‖x i‖ < δ := by
  by_contra! hn
  have hq : 0 ≤ q := (by norm_num : (0 : ℝ) ≤ 2).trans h.1
  have hlower : (n : ℝ) * δ ^ q ≤ ∑ i, ‖x i‖ ^ q := by
    calc
      _ = ∑ _i : Fin n, δ ^ q := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => Real.rpow_le_rpow hδ (hn i) hq
  exact (not_lt_of_ge (hlower.trans (h.sum_rpow_le_of_sign_bound x hM hsign))) hlarge

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The actual scalar c₀ unit vector at coordinate `n`. -/
def cZeroUnitVector (n : ℕ) : CZero 𝕜 where
  toFun k := if k = n then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    classical
    rw [Filter.cocompact_eq_cofinite]
    apply tendsto_const_nhds.congr'
    filter_upwards [(Set.finite_singleton n).compl_mem_cofinite] with k hk
    have hkn : k ≠ n := by simpa using hk
    simp [hkn]

@[simp] theorem cZeroUnitVector_apply (n k : ℕ) :
    cZeroUnitVector (𝕜 := 𝕜) n k = if k = n then 1 else 0 := rfl

@[simp] theorem norm_cZeroUnitVector (n : ℕ) :
    ‖cZeroUnitVector (𝕜 := 𝕜) n‖ = 1 := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
    intro k
    by_cases hk : k = n <;> simp [hk]
  · have h := BoundedContinuousFunction.norm_coe_le_norm
      (cZeroUnitVector (𝕜 := 𝕜) n).toBCF n
    change ‖cZeroUnitVector (𝕜 := 𝕜) n n‖ ≤ ‖cZeroUnitVector (𝕜 := 𝕜) n‖ at h
    simpa using h

private theorem norm_sign_sum_apply_le {ι κ : Type*} [Fintype ι]
    (f : ι → κ → 𝕜) (hf : ∀ i k, ‖f i k‖ ≤ 1)
    (hdis : ∀ i j, i ≠ j → ∀ k, f i k = 0 ∨ f j k = 0)
    (θ : ι → Bool) (k : κ) :
    ‖∑ i, if θ i then f i k else -f i k‖ ≤ 1 := by
  classical
  by_cases h : ∃ i, f i k ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · split_ifs <;> simpa only [norm_neg] using hf i k
    · intro j _ hj
      have hz := (hdis i j hj.symm k).resolve_left hi
      simp [hz]
    · simp
  · push_neg at h
    simp [h]

/-- Every signed sum of distinct scalar coordinate unit vectors has c₀ norm
at most one, independently of the number of vectors. -/
theorem norm_signed_sum_cZeroUnitVector_le {n : ℕ} (θ : Fin n → Bool) :
    ‖∑ i : Fin n, if θ i then cZeroUnitVector (𝕜 := 𝕜) i.val
      else -cZeroUnitVector (𝕜 := 𝕜) i.val‖ ≤ 1 := by
  classical
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro k
  have hdis : ∀ i j : Fin n, i ≠ j → ∀ k : ℕ,
      cZeroUnitVector (𝕜 := 𝕜) i.val k = 0 ∨ cZeroUnitVector (𝕜 := 𝕜) j.val k = 0 := by
    intro i j hij k
    by_cases hki : k = i.val
    · right
      have hkj : k ≠ j.val := by
        intro heq
        exact hij (Fin.ext (hki.symm.trans heq))
      simp [hkj]
    · left
      simp [hki]
  have hb := norm_sign_sum_apply_le
    (fun (i : Fin n) k => cZeroUnitVector (𝕜 := 𝕜) i.val k)
    (fun i k => by simp only [cZeroUnitVector_apply]; split_ifs <;> simp)
    hdis θ k
  convert hb using 1
  simp
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

variable [NormedSpace 𝕜 E]

/-- Finite cotype excludes bounded-below scalar c₀ embeddings, hence excludes
isomorphic c₀ subspaces. Completeness and separability are unnecessary here. -/
theorem HasFiniteCotype.containsNoCZero (h : HasFiniteCotype E) :
    ContainsNoCZero 𝕜 E := by
  rintro ⟨J, c, hc, hJ⟩
  obtain ⟨q, C, hCotype⟩ := h
  have hcq : 0 < c ^ q := Real.rpow_pos_of_pos hc q
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ q * ‖J‖ ^ q / c ^ q)
  have hlarge : C ^ q * ‖J‖ ^ q < (n : ℝ) * c ^ q :=
    (div_lt_iff₀ hcq).mp hn
  have hsign : ∀ θ : Fin n → Bool,
      ‖∑ i, if θ i then J (cZeroUnitVector (𝕜 := 𝕜) i.val)
        else -J (cZeroUnitVector (𝕜 := 𝕜) i.val)‖ ≤ ‖J‖ := by
    intro θ
    have heq : (∑ i, if θ i then J (cZeroUnitVector (𝕜 := 𝕜) i.val)
        else -J (cZeroUnitVector (𝕜 := 𝕜) i.val)) =
        J (∑ i, if θ i then cZeroUnitVector (𝕜 := 𝕜) i.val
          else -cZeroUnitVector (𝕜 := 𝕜) i.val) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [heq]
    exact (J.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left (norm_signed_sum_cZeroUnitVector_le θ)
        (norm_nonneg J)).trans_eq (mul_one ‖J‖))
  obtain ⟨i, hi⟩ := hCotype.exists_norm_lt_of_sign_bound
    (fun i : Fin n => J (cZeroUnitVector (𝕜 := 𝕜) i.val))
    (norm_nonneg J) hc.le hsign hlarge
  have hlower : c ≤ ‖J (cZeroUnitVector (𝕜 := 𝕜) i.val)‖ := by
    simpa only [norm_cZeroUnitVector, mul_one] using hJ (cZeroUnitVector (𝕜 := 𝕜) i.val)
  exact (not_lt_of_ge hlower) hi

end CKEUPFP
