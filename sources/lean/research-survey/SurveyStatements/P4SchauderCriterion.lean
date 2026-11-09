import SurveyStatements.P4Definitions
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! The genuine ordered Schauder criterion from biorthogonal continuous
coordinates, dense span, and uniformly bounded initial projections. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Filter Topology
open scoped BigOperators

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : Set ℕ}

def orderedBasisProjection (b : I → E) (φ : I → StrongDual 𝕜 E) (N : ℕ) : E →L[𝕜] E := by
  classical
  exact ∑ n ∈ Finset.range N, if h : n ∈ I then (φ ⟨n, h⟩).smulRight (b ⟨n, h⟩) else 0

lemma orderedBasisProjection_apply (b : I → E) (φ : I → StrongDual 𝕜 E) (N : ℕ) (x : E) :
    orderedBasisProjection b φ N x = schauderPartialSum 𝕜 b (fun i => φ i x) N := by
  classical
  simp only [orderedBasisProjection, schauderPartialSum, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> rfl

lemma partialSum_biorthogonal_eval (b : I → E) (φ : I → StrongDual 𝕜 E)
    (hbi : ∀ i j, φ i (b j) = if i = j then 1 else 0)
    (a : I → 𝕜) (i : I) {N : ℕ} (hN : i.val < N) :
    φ i (schauderPartialSum 𝕜 b a N) = a i := by
  classical
  simp only [schauderPartialSum, map_sum]
  rw [Finset.sum_eq_single i.val]
  · simp [i.property, hbi]
  · intro n hn hni
    by_cases hnI : n ∈ I
    · have hne : i ≠ (⟨n, hnI⟩ : I) := by
        intro h
        exact hni (congrArg Subtype.val h).symm
      simp [hnI, map_smul, hbi, hne]
    · simp [hnI]
  · intro hi
    exact False.elim (hi (Finset.mem_range.mpr hN))

lemma orderedBasisProjection_basis (b : I → E) (φ : I → StrongDual 𝕜 E)
    (hbi : ∀ i j, φ i (b j) = if i = j then 1 else 0)
    (i : I) {N : ℕ} (hN : i.val < N) : orderedBasisProjection b φ N (b i) = b i := by
  classical
  rw [orderedBasisProjection_apply]
  unfold schauderPartialSum
  rw [Finset.sum_eq_single i.val]
  · simp [i.property, hbi]
  · intro n hn hni
    by_cases hnI : n ∈ I
    · have hne : (⟨n, hnI⟩ : I) ≠ i := by
        intro h
        exact hni (congrArg Subtype.val h)
      simp [hnI, hbi, hne]
    · simp [hnI]
  · intro hi
    exact False.elim (hi (Finset.mem_range.mpr hN))

lemma orderedBasisProjection_eventually_fixed_of_mem_span
    (b : I → E) (φ : I → StrongDual 𝕜 E)
    (hbi : ∀ i j, φ i (b j) = if i = j then 1 else 0)
    {x : E} (hx : x ∈ Submodule.span 𝕜 (Set.range b)) :
    ∃ N : ℕ, ∀ M, N ≤ M → orderedBasisProjection b φ M x = x := by
  classical
  let Q : Submodule 𝕜 E :=
    { carrier := {x | ∃ N : ℕ, ∀ M, N ≤ M → orderedBasisProjection b φ M x = x}
      zero_mem' := ⟨0, fun M hM => map_zero _⟩
      add_mem' := by
        rintro x y ⟨N, hN⟩ ⟨M, hM⟩
        exact ⟨max N M, fun L hL => by
          rw [map_add, hN L ((le_max_left _ _).trans hL),
            hM L ((le_max_right _ _).trans hL)]⟩
      smul_mem' := by
        rintro a x ⟨N, hN⟩
        exact ⟨N, fun M hM => by rw [map_smul, hN M hM]⟩ }
  have hb : Set.range b ⊆ Q := by
    rintro y ⟨i, rfl⟩
    exact ⟨i.val + 1, fun M hM => orderedBasisProjection_basis b φ hbi i (by omega)⟩
  exact (Submodule.span_le.mpr hb) hx

theorem isSchauderBasis_of_biorthogonal_uniform_bound
    (hI : IsLowerSet I) (b : I → E) (φ : I → StrongDual 𝕜 E)
    (hbi : ∀ i j, φ i (b j) = if i = j then 1 else 0)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ N, ‖orderedBasisProjection b φ N‖ ≤ B)
    (hdense : Dense (Submodule.span 𝕜 (Set.range b) : Set E)) :
    IsSchauderBasis 𝕜 b := by
  classical
  refine ⟨hI, ?_⟩
  intro x
  let a : I → 𝕜 := fun i => φ i x
  have ha : Tendsto (schauderPartialSum 𝕜 b a) atTop (𝓝 x) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hden : 0 < B + 1 := by linarith
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hdense x)
      (ε / (2 * (B + 1))) (div_pos hε (mul_pos (by norm_num) hden))
    obtain ⟨N, hN⟩ := orderedBasisProjection_eventually_fixed_of_mem_span b φ hbi hy
    refine ⟨N, fun M hM => ?_⟩
    rw [← orderedBasisProjection_apply, dist_eq_norm]
    have heq : orderedBasisProjection b φ M x - x =
        orderedBasisProjection b φ M (x - y) - (x - y) := by
      rw [map_sub, hN M hM]
      abel
    rw [heq]
    have hsmall : (B + 1) * ‖x - y‖ < ε / 2 := by
      rw [dist_eq_norm] at hxy
      nlinarith [(lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hden)).mp hxy]
    calc
      ‖orderedBasisProjection b φ M (x - y) - (x - y)‖ ≤
          ‖orderedBasisProjection b φ M (x - y)‖ + ‖x - y‖ := norm_sub_le _ _
      _ ≤ B * ‖x - y‖ + ‖x - y‖ := by
        apply add_le_add_right
        exact ((orderedBasisProjection b φ M).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hbound M) (norm_nonneg _))
      _ = (B + 1) * ‖x - y‖ := by ring
      _ < ε / 2 := hsmall
      _ < ε := half_lt_self hε
  refine ⟨a, ha, ?_⟩
  intro c hc
  funext i
  have ht : Tendsto (fun N => φ i (schauderPartialSum 𝕜 b c N)) atTop (𝓝 (φ i x)) :=
    (φ i).continuous.tendsto x |>.comp hc
  have hevent : (fun N => φ i (schauderPartialSum 𝕜 b c N)) =ᶠ[atTop] fun _ => c i :=
    (eventually_ge_atTop (i.val + 1)).mono fun N hN =>
      partialSum_biorthogonal_eval b φ hbi c i (by omega)
  exact (tendsto_nhds_unique (ht.congr' hevent) tendsto_const_nhds).symm

end SurveyStatements.P4
