import CKEUPFP.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Certification of the paper's foundational definitions

These results prove that the bounded-below formulation of an isomorphic copy
agrees with the usual closed-subspace formulation for Banach spaces. They also
certify the pointwise factorisation equation and the null-sequence model of c₀.
The elementary permanence results below use the actual operators and norms.
-/

noncomputable section

universe u v w z t

namespace CKEUPFP

open scoped ZeroAtInfty

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {Z : Type z} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable {W : Type t} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The bundled operator equation means precisely the paper's pointwise
equation `U(T(Vz)) = Sz`, with its factorisation cost unchanged. -/
theorem factorsThroughWith_iff_pointwise
    (S : Z →L[𝕜] W) (T : X →L[𝕜] Y) (C : ℝ) :
    FactorsThroughWith S T C ↔
      ∃ U : Y →L[𝕜] W, ∃ V : Z →L[𝕜] X,
        (∀ z : Z, U (T (V z)) = S z) ∧ ‖U‖ * ‖V‖ ≤ C := by
  constructor
  · rintro ⟨U, V, h, hnorm⟩
    exact ⟨U, V, fun z => congrArg (fun F : Z →L[𝕜] W => F z) h, hnorm⟩
  · rintro ⟨U, V, h, hnorm⟩
    exact ⟨U, V, ContinuousLinearMap.ext h, hnorm⟩

/-- Omitting a factorisation bound means that some finite real bound exists. -/
theorem factorsThrough_iff_exists_bound (S : Z →L[𝕜] W) (T : X →L[𝕜] Y) :
    FactorsThrough S T ↔ ∃ C : ℝ, FactorsThroughWith S T C := by
  constructor
  · rintro ⟨U, V, h⟩
    exact ⟨‖U‖ * ‖V‖, U, V, h, le_rfl⟩
  · rintro ⟨C, U, V, h, _⟩
    exact ⟨U, V, h⟩

theorem FactorsThroughWith.factorsThrough
    {S : Z →L[𝕜] W} {T : X →L[𝕜] Y} {C : ℝ}
    (h : FactorsThroughWith S T C) : FactorsThrough S T := by
  obtain ⟨U, V, hUV, _⟩ := h
  exact ⟨U, V, hUV⟩

theorem FactorsThroughWith.mono
    {S : Z →L[𝕜] W} {T : X →L[𝕜] Y} {C D : ℝ}
    (h : FactorsThroughWith S T C) (hCD : C ≤ D) :
    FactorsThroughWith S T D := by
  obtain ⟨U, V, hUV, hnorm⟩ := h
  exact ⟨U, V, hUV, hnorm.trans hCD⟩

theorem HasCPFP.hasPFP {C : ℝ} (h : HasCPFP 𝕜 X C) : HasPFP 𝕜 X := by
  intro T
  rcases h.2 T with hT | hT
  · exact Or.inl hT.factorsThrough
  · exact Or.inr hT.factorsThrough

theorem HasUPFP.hasPFP (h : HasUPFP 𝕜 X) : HasPFP 𝕜 X := by
  obtain ⟨C, hC⟩ := h
  exact hC.hasPFP

theorem HasCPFP.mono {C D : ℝ} (h : HasCPFP 𝕜 X C) (hCD : C ≤ D) :
    HasCPFP 𝕜 X D := by
  refine ⟨h.1.trans hCD, fun T => ?_⟩
  rcases h.2 T with hT | hT
  · exact Or.inl (hT.mono hCD)
  · exact Or.inr (hT.mono hCD)

/-- The zero Banach space is included in the paper's main theorem. -/
theorem hasCPFP_of_subsingleton [Subsingleton X] {C : ℝ} (hC : 1 ≤ C) :
    HasCPFP 𝕜 X C := by
  refine ⟨hC, fun T => Or.inl ?_⟩
  refine ⟨0, 0, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  · simpa using (zero_le_one.trans hC : (0 : ℝ) ≤ C)

theorem hasUPFP_of_subsingleton [Subsingleton X] : HasUPFP 𝕜 X :=
  ⟨1, hasCPFP_of_subsingleton le_rfl⟩

/-- Every member of our `CZero` model is a scalar null sequence. -/
theorem cZero_tendsto_zero (f : CZero 𝕜) :
    Filter.Tendsto (fun n : ℕ => f n) Filter.atTop (nhds 0) := by
  simpa only [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    using f.zero_at_infty'

/-- Every scalar null sequence is represented in `CZero`, and conversely. -/
theorem exists_cZero_iff_tendsto_zero (a : ℕ → 𝕜) :
    (∃ f : CZero 𝕜, ∀ n : ℕ, f n = a n) ↔
      Filter.Tendsto a Filter.atTop (nhds 0) := by
  constructor
  · rintro ⟨f, hf⟩
    have hfa : (fun n : ℕ => f n) = a := funext hf
    simpa only [hfa] using cZero_tendsto_zero f
  · intro ha
    refine ⟨{
      toFun := a
      continuous_toFun := continuous_of_discreteTopology
      zero_at_infty' := ?_
    }, fun _ => rfl⟩
    simpa only [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using ha

/-- The norm on `CZero` is exactly the supremum of scalar coordinate norms. -/
theorem cZero_norm_eq_iSup (f : CZero 𝕜) : ‖f‖ = ⨆ n : ℕ, ‖f n‖ := by
  change ‖f.toBCF‖ = _
  exact BoundedContinuousFunction.norm_eq_iSup_norm f.toBCF

/-- A positive lower bound implies injectivity; no complement is required. -/
theorem injective_of_positive_lower_bound
    (J : Y →L[𝕜] X) {c : ℝ} (hc : 0 < c)
    (hJ : ∀ y : Y, c * ‖y‖ ≤ ‖J y‖) : Function.Injective J := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h := hJ (x - y)
  rw [map_sub, hxy, sub_self, norm_zero] at h
  nlinarith [norm_nonneg (x - y)]

/-- A positive lower bound supplies the usual inverse Lipschitz estimate. -/
theorem antilipschitz_of_positive_lower_bound
    (J : Y →L[𝕜] X) {c : ℝ} (hc : 0 < c)
    (hJ : ∀ y : Y, c * ‖y‖ ≤ ‖J y‖) :
    AntilipschitzWith ⟨c⁻¹, (inv_pos.mpr hc).le⟩ J := by
  apply J.antilipschitz_of_bound
  intro y
  have h : ‖y‖ ≤ ‖J y‖ / c :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hJ y)
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- A complete source embedded with a positive lower bound has closed range. -/
theorem isClosed_range_of_positive_lower_bound [CompleteSpace Y]
    (J : Y →L[𝕜] X) {c : ℝ} (hc : 0 < c)
    (hJ : ∀ y : Y, c * ‖y‖ ≤ ‖J y‖) : IsClosed (Set.range J) :=
  (antilipschitz_of_positive_lower_bound J hc hJ).isClosed_range J.uniformContinuous

/-- For Banach spaces, the paper's "contains an isomorphic copy" means exactly
that some closed linear subspace is bounded-linearly isomorphic to the source.
The equivalence also covers the zero source and the zero target. -/
theorem containsIsomorphicCopy_iff_closed_subspace
    [CompleteSpace X] [CompleteSpace Y] :
    ContainsIsomorphicCopy 𝕜 X Y ↔
      ∃ S : Submodule 𝕜 X, IsClosed (S : Set X) ∧ Nonempty (Y ≃L[𝕜] S) := by
  constructor
  · rintro ⟨J, c, hc, hJ⟩
    have hinj := injective_of_positive_lower_bound J hc hJ
    have hclosed := isClosed_range_of_positive_lower_bound J hc hJ
    refine ⟨LinearMap.range J.toLinearMap, ?_, ⟨J.equivRange hinj hclosed⟩⟩
    change IsClosed (Set.range J)
    exact hclosed
  · rintro ⟨S, _, ⟨e⟩⟩
    let J : Y →L[𝕜] X := S.subtypeL.comp e.toContinuousLinearMap
    let M : ℝ := ‖e.symm.toContinuousLinearMap‖ + 1
    have hM : 0 < M := by
      dsimp [M]
      positivity
    refine ⟨J, M⁻¹, inv_pos.mpr hM, fun y => ?_⟩
    have hbound : ‖y‖ ≤ M * ‖J y‖ := by
      calc
        ‖y‖ = ‖e.symm (e y)‖ := by rw [e.symm_apply_apply]
        _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e y‖ :=
          e.symm.toContinuousLinearMap.le_opNorm (e y)
        _ ≤ M * ‖e y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          dsimp [M]
          linarith
        _ = M * ‖J y‖ := rfl
    have hdiv : ‖y‖ / M ≤ ‖J y‖ :=
      (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hbound)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- The no-c₀ hypothesis has the usual closed-subspace interpretation. -/
theorem containsNoCZero_iff_no_closed_subspace [CompleteSpace X] :
    ContainsNoCZero 𝕜 X ↔
      ¬ ∃ S : Submodule 𝕜 X, IsClosed (S : Set X) ∧ Nonempty (CZero 𝕜 ≃L[𝕜] S) := by
  exact not_congr containsIsomorphicCopy_iff_closed_subspace

end CKEUPFP
