import Posets.UltrafilterBimoduleOperators

/-! Biorthogonality and the multiplier identities for the functionals F_n. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem multiplicationOperator_unitVector {P : Type*} (a : Discrete P →ᵇ 𝕜) (p : P) :
    multiplicationOperator a (unitVector 𝕜 p) = a ⟨p⟩ • unitVector 𝕜 p := by
  ext x
  change a x * (if x.val = p then 1 else 0) = a ⟨p⟩ * (if x.val = p then 1 else 0)
  rcases x with ⟨x⟩
  by_cases h : x = p <;> simp [h]

theorem ultrafilterMatrixFunctional_left (U : Ultrafilter RowDomain) (n : ℕ)
    (a : Discrete RowDomain →ᵇ 𝕜) (T : OffDiagonal 𝕜) :
    ultrafilterMatrixFunctional (𝕜 := 𝕜) U n ((multiplicationOperator a).comp T) =
      ultrafilterEvaluation U a * ultrafilterMatrixFunctional (𝕜 := 𝕜) U n T := by
  change limUnder (U : Filter RowDomain)
    (fun x => a ⟨x⟩ * T (unitVector 𝕜 (selector n x)) ⟨x⟩) = _
  exact ((tendsto_ultrafilter_evaluation U a).mul
    (tendsto_ultrafilterMatrixFunctional U n T)).limUnder_eq

theorem synchronizedSelector_tendsto (U : Ultrafilter RowDomain)
    (V : Ultrafilter ColumnDomain) (h : Synchronized U V) (n : ℕ) :
    Tendsto (selector n) (U : Filter RowDomain) (V : Filter ColumnDomain) := by
  change Filter.map (selector n) (U : Filter RowDomain) ≤ (V : Filter ColumnDomain)
  rw [← Ultrafilter.coe_map, h.2.2.1 n]

theorem ultrafilterMatrixFunctional_right (U : Ultrafilter RowDomain)
    (V : Ultrafilter ColumnDomain) (h : Synchronized U V) (n : ℕ)
    (b : Discrete ColumnDomain →ᵇ 𝕜) (T : OffDiagonal 𝕜) :
    ultrafilterMatrixFunctional (𝕜 := 𝕜) U n (T.comp (multiplicationOperator b)) =
      ultrafilterMatrixFunctional (𝕜 := 𝕜) U n T * ultrafilterEvaluation V b := by
  have hp (x : RowDomain) :
      (T.comp (multiplicationOperator b)) (unitVector 𝕜 (selector n x)) ⟨x⟩ =
        b ⟨selector n x⟩ * T (unitVector 𝕜 (selector n x)) ⟨x⟩ := by
    rw [ContinuousLinearMap.comp_apply, multiplicationOperator_unitVector, map_smul]
    rfl
  rw [ultrafilterMatrixFunctional_apply]
  simp_rw [hp]
  exact (((tendsto_ultrafilter_evaluation V b).comp (synchronizedSelector_tendsto U V h n)).mul
    (tendsto_ultrafilterMatrixFunctional U n T)).limUnder_eq.trans (mul_comm _ _)

theorem ultrafilterMatrixFunctional_selectorPullback (U : Ultrafilter RowDomain)
    (V : Ultrafilter ColumnDomain) (h : Synchronized U V) (n m : ℕ) :
    ultrafilterMatrixFunctional (𝕜 := 𝕜) U n (selectorPullbackOperator (𝕜 := 𝕜) m) =
      if m = n then 1 else 0 := by
  rw [ultrafilterMatrixFunctional_apply]
  simp only [selectorPullbackOperator_apply]
  have hp (x : RowDomain) : (unitVector 𝕜 (selector n x)) ⟨selector m x⟩ =
      if selector m x = selector n x then (1 : 𝕜) else 0 := by
    by_cases hx : selector m x = selector n x <;> simp [unitVector, hx]
  simp_rw [hp]
  by_cases hmn : m = n
  · subst m
    simp only
    exact tendsto_const_nhds.limUnder_eq
  · rw [if_neg hmn]
    have hdis : ∀ᶠ x in (U : Filter RowDomain), selector m x ≠ selector n x :=
      Ultrafilter.compl_mem_iff_notMem.mpr (h.2.2.2 m n hmn)
    apply Filter.Tendsto.limUnder_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [hdis] with x hx
    simp [hx]

end Posets
