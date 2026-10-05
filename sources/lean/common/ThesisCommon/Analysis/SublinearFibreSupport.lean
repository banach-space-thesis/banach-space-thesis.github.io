import ThesisCommon.Analysis.ScalarBlockEstimate
import ThesisCommon.Analysis.CountableTotalDual

/-! Scalar phase alignment and sublinear finite-sum growth imply countable
incoming fibre support. All finite-sum norm bounds are explicit hypotheses
here and are discharged by the actual lp and c0 models in later modules. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 Γ X Z Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem functional_countable_fibre_support (J : Γ → X →L[𝕜] Z) (B : ℕ → ℝ)
    (hJ : ∀ n (e : Fin n ↪ Γ) (x : Fin n → X), (∀ i, ‖x i‖ ≤ 1) →
      ‖∑ i, J (e i) (x i)‖ ≤ B n)
    (hgrowth : ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ∃ n, M * B n < n * ε)
    (φ : Z →L[𝕜] 𝕜) : {γ | φ.comp (J γ) ≠ 0}.Countable := by
  classical
  have hfinite (ε : ℝ) (hε : 0 < ε) : {γ | ε < ‖φ.comp (J γ)‖}.Finite := by
    by_contra hA
    let A : Set Γ := {γ | ε < ‖φ.comp (J γ)‖}
    have hAinf : A.Infinite := hA
    obtain ⟨n, hn⟩ := hgrowth ‖φ‖ (norm_nonneg φ) ε hε
    let e : Fin n ↪ Γ :=
      (Fin.valEmbedding.trans (hAinf.natEmbedding A)).trans (Function.Embedding.subtype A)
    obtain ⟨i, hi⟩ := exists_small_scalar_block (fun i : Fin n => J (e i))
      (norm_nonneg φ) (hJ n e) φ le_rfl hn
    exact ((hAinf.natEmbedding A i.val).property).not_ge hi
  let Δ : Set Γ := ⋃ n : ℕ, {γ | 1 / ((n : ℝ) + 1) < ‖φ.comp (J γ)‖}
  have hΔ : Δ.Countable := Set.countable_iUnion (fun n =>
    (hfinite (1 / ((n : ℝ) + 1)) (by positivity)).countable)
  apply hΔ.mono
  intro γ hγ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hγ)
  exact Set.mem_iUnion.mpr ⟨n, hn⟩

theorem operator_countable_fibre_support (J : Γ → X →L[𝕜] Z) (B : ℕ → ℝ)
    (hJ : ∀ n (e : Fin n ↪ Γ) (x : Fin n → X), (∀ i, ‖x i‖ ≤ 1) →
      ‖∑ i, J (e i) (x i)‖ ≤ B n)
    (hgrowth : ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ∃ n, M * B n < n * ε)
    (htotal : HasCountableTotalDual 𝕜 Y) (T : Z →L[𝕜] Y) :
    {γ | T.comp (J γ) ≠ 0}.Countable := by
  classical
  obtain ⟨M, hM, hsep⟩ := htotal
  letI : Countable M := hM.to_subtype
  let Δ : Set Γ := ⋃ φ : M, {γ | (φ.val.comp T).comp (J γ) ≠ 0}
  have hΔ : Δ.Countable := Set.countable_iUnion (fun φ =>
    functional_countable_fibre_support J B hJ hgrowth (φ.val.comp T))
  apply hΔ.mono
  intro γ hγ
  by_contra hn
  apply hγ
  apply ContinuousLinearMap.ext
  intro x
  apply hsep
  intro φ hφ
  have hz : (φ.comp T).comp (J γ) = 0 := by
    by_contra hne
    exact hn (Set.mem_iUnion.mpr ⟨⟨φ, hφ⟩, hne⟩)
  exact DFunLike.congr_fun hz x

end ThesisCommon
