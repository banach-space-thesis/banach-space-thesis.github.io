import Mathlib.Analysis.NormedSpace.RieszLemma
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Algebra.Module.LinearMap.End

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.CompactSpectralSupport
open Module Topology
variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem range_powers_antitone (S : End 𝕜 X) :
    Antitone (fun n : ℕ => LinearMap.range (S ^ n)) := by
  apply antitone_nat_of_succ_le
  intro n
  rintro y ⟨x, rfl⟩
  exact ⟨S x, by rw [pow_succ, Module.End.mul_apply]⟩

theorem closedEmbedding_powers (S : End 𝕜 X) (hS : IsClosedEmbedding S) (n : ℕ) :
    IsClosedEmbedding (S ^ n : End 𝕜 X) := by
  induction n with
  | zero => exact IsClosedEmbedding.id
  | succ n ih =>
    have h := hS.comp ih
    convert h using 1
    ext x
    simp only [pow_succ', Module.End.mul_apply, Function.comp_apply]

/-- The separated-shell sequence used in the compact Fredholm argument.
It is built from Riesz's lemma for the strictly decreasing ranges of powers. -/
theorem separation_sequence {S : End 𝕜 X} (hS_not_surj : ¬ Function.Surjective S)
    (hS : IsClosedEmbedding S) {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) :
    ∃ f : ℕ → X, (∀ n, 1 ≤ ‖f n‖) ∧ (∀ n, ‖f n‖ ≤ R) ∧
      (∀ n, f n ∈ LinearMap.range (S ^ n)) ∧
      (∀ n, ∀ y ∈ LinearMap.range (S ^ (n + 1)), 1 ≤ ‖f n - y‖) := by
  classical
  have hmissing : ∃ x₀ : X, ∀ y : X, S y ≠ x₀ := by
    simpa only [Function.Surjective, not_forall, not_exists] using hS_not_surj
  obtain ⟨x₀, hx₀⟩ := hmissing
  let V (n : ℕ) : Submodule 𝕜 X := LinearMap.range (S ^ n)
  have hVclosed (n : ℕ) : IsClosed (V n : Set X) := (closedEmbedding_powers S hS n).isClosed_range
  have hex (n : ℕ) : ∃ x ∈ V n, 1 ≤ ‖x‖ ∧ ‖x‖ ≤ R ∧
      ∀ y ∈ V (n + 1), 1 ≤ ‖x - y‖ := by
    have hclosed : IsClosed ((V (n + 1)).comap (V n).subtype : Set (V n)) :=
      (hVclosed (n + 1)).preimage continuous_subtype_val
    have hproper : ∃ x : V n, x ∉ (V (n + 1)).comap (V n).subtype := by
      refine ⟨⟨(S ^ n) x₀, ⟨x₀, rfl⟩⟩, ?_⟩
      change (S ^ n) x₀ ∉ LinearMap.range (S ^ (n + 1))
      rintro ⟨y, hy⟩
      have heq : (S ^ n) (S y) = (S ^ n) x₀ := by
        simpa only [pow_succ, Module.End.mul_apply] using hy
      exact hx₀ y (Module.End.iterate_injective hS.injective n heq)
    obtain ⟨x, hxnorm, hxfar⟩ := riesz_lemma_of_norm_lt hc hR hclosed hproper
    refine ⟨x.val, x.property, ?_, hxnorm, ?_⟩
    · have h := hxfar 0 ((V (n + 1)).comap (V n).subtype).zero_mem
      simpa only [sub_zero] using h
    · intro y hy
      exact hxfar ⟨y, range_powers_antitone S (Nat.le_succ n) hy⟩ hy
  choose f hfmem hflower hfupper hffar using hex
  exact ⟨f, hflower, hfupper, hfmem, hffar⟩

end NonCalkinAlgebra.CompactSpectralSupport
