import NonCalkinAlgebra.CompactSpectralSupport
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.NormNum

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open Module Topology
universe v
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The span of the first n vectors, with its literal inherited topology. -/
def eigenvectorSpan (v : ℕ → X) (n : ℕ) : Submodule ℂ X :=
  Submodule.span ℂ (v '' (Finset.range n : Set ℕ))

instance eigenvectorSpan_finiteDimensional (v : ℕ → X) (n : ℕ) :
    FiniteDimensional ℂ (eigenvectorSpan v n) :=
  FiniteDimensional.span_of_finite ℂ ((Finset.range n).finite_toSet.image v)

theorem eigenvectorSpan_isClosed (v : ℕ → X) (n : ℕ) :
    IsClosed (eigenvectorSpan v n : Set X) :=
  (eigenvectorSpan v n).closed_of_finiteDimensional

theorem eigenvectorSpan_mono (v : ℕ → X) : Monotone (eigenvectorSpan v) := by
  intro n m hnm
  apply Submodule.span_mono
  apply Set.image_mono
  intro k hk
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hnm)

theorem eigenvector_mem_span (v : ℕ → X) (n k : ℕ) (hk : k < n) :
    v k ∈ eigenvectorSpan v n :=
  Submodule.subset_span ⟨k, Finset.mem_range.mpr hk, rfl⟩

theorem eigenvector_not_mem_previous_span (v : ℕ → X) (hv : LinearIndependent ℂ v) (n : ℕ) :
    v n ∉ eigenvectorSpan v n :=
  hv.notMem_span_image (by simp only [Finset.mem_coe, Finset.mem_range, lt_self_iff_false, not_false_eq_true])

/-- Riesz's lemma provides a uniformly bounded sequence separated from the
preceding finite spans. Completeness of the ambient space is not needed. -/
theorem eigenvectorFlag_separated_sequence (v : ℕ → X) (hv : LinearIndependent ℂ v) :
    ∃ f : ℕ → X, (∀ n, f n ∈ eigenvectorSpan v (n + 1)) ∧
      (∀ n, ‖f n‖ ≤ 3) ∧
      (∀ n, ∀ y ∈ eigenvectorSpan v n, 1 ≤ ‖f n - y‖) := by
  classical
  have hex (n : ℕ) : ∃ x ∈ eigenvectorSpan v (n + 1), ‖x‖ ≤ 3 ∧
      ∀ y ∈ eigenvectorSpan v n, 1 ≤ ‖x - y‖ := by
    let V := eigenvectorSpan v (n + 1)
    let W := (eigenvectorSpan v n).comap V.subtype
    have hWclosed : IsClosed (W : Set V) :=
      (eigenvectorSpan_isClosed v n).preimage continuous_subtype_val
    have hproper : ∃ x : V, x ∉ W :=
      ⟨⟨v n, eigenvector_mem_span v (n + 1) n (Nat.lt_succ_self n)⟩,
        eigenvector_not_mem_previous_span v hv n⟩
    obtain ⟨x, hxnorm, hxfar⟩ := riesz_lemma_of_norm_lt
      (c := (2 : ℂ)) (R := (3 : ℝ)) (by norm_num) (by norm_num) hWclosed hproper
    refine ⟨x.val, x.property, hxnorm, ?_⟩
    intro y hy
    exact hxfar ⟨y, eigenvectorSpan_mono v (Nat.le_succ n) hy⟩ hy
  choose f hfmem hfnorm hffar using hex
  exact ⟨f, hfmem, hfnorm, hffar⟩

theorem operator_preserves_eigenvectorSpan (T : X →L[ℂ] X) (μ : ℕ → ℂ) (v : ℕ → X)
    (heigen : ∀ k, T (v k) = μ k • v k) (n : ℕ) {x : X}
    (hx : x ∈ eigenvectorSpan v n) : T x ∈ eigenvectorSpan v n := by
  have hle : eigenvectorSpan v n ≤ (eigenvectorSpan v n).comap T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨k, hk, rfl⟩
    change T (v k) ∈ eigenvectorSpan v n
    rw [heigen k]
    exact (eigenvectorSpan v n).smul_mem (μ k)
      (eigenvector_mem_span v n k (Finset.mem_range.mp hk))
  exact hle hx

/-- Subtracting the last eigenvalue lowers this finite eigenvector flag. -/
theorem eigenvectorSpan_defect_lowers (T : X →L[ℂ] X) (μ : ℕ → ℂ) (v : ℕ → X)
    (heigen : ∀ k, T (v k) = μ k • v k) (n : ℕ) {x : X}
    (hx : x ∈ eigenvectorSpan v (n + 1)) :
    T x - μ n • x ∈ eigenvectorSpan v n := by
  have hle : eigenvectorSpan v (n + 1) ≤
      (eigenvectorSpan v n).comap (T - μ n • 1).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨k, hk, rfl⟩
    change T (v k) - μ n • v k ∈ eigenvectorSpan v n
    by_cases heq : k = n
    · subst k
      rw [heigen n, sub_self]
      exact (eigenvectorSpan v n).zero_mem
    · rw [heigen k, ← sub_smul]
      apply (eigenvectorSpan v n).smul_mem
      apply eigenvector_mem_span v n k
      have hk' := Finset.mem_range.mp hk
      omega
  exact hle hx

end NonCalkinAlgebra
