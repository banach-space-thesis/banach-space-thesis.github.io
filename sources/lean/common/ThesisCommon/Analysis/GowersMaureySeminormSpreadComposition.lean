import ThesisCommon.Analysis.GowersMaureyIntervalSpreadBounds
import ThesisCommon.Analysis.GowersMaureyEndomorphismSeminorm
import ThesisCommon.Analysis.GowersMaureyLaurentOperators
import ThesisCommon.Analysis.WienerContinuousConvolution

/-! Right composition by actual tail spreads preserves the block seminorm
kernel. The transformed test sequences retain all interval bounds. Norm
convergence then gives the same kernel assertion for every Laurent operator.
No finite-spread approximation premise is needed in this module. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem Before.spread {x y : C00 𝕜} (h : Before x y) (m n : ℕ) :
    Before (GowersMaurey.spread m n x) (GowersMaurey.spread m n y) := by
  intro s hs t ht
  have hsn := Finsupp.mem_support_iff.mp hs
  have htn := Finsupp.mem_support_iff.mp ht
  rw [spread_apply] at hsn htn
  have hs' : n ≤ s ∧ x (s - n + m) ≠ 0 := by
    simpa only [ne_eq, ite_eq_right_iff, Classical.not_imp] using hsn
  have ht' : n ≤ t ∧ y (t - n + m) ≠ 0 := by
    simpa only [ne_eq, ite_eq_right_iff, Classical.not_imp] using htn
  have hlt := h _ (Finsupp.mem_support_iff.mpr hs'.2) _
    (Finsupp.mem_support_iff.mpr ht'.2)
  omega

def BlockTestSequence.spread {D : ConstructionData 𝕜}
    (u : BlockTestSequence D ⊤) (m n : ℕ) : BlockTestSequence D ⊤ where
  vector k := GowersMaurey.spread m n (u.vector k)
  mem_subspace _ := Submodule.mem_top
  successive i j hij := (u.successive i j hij).spread m n
  norm_bound k := (intervalNorm_spread_le D (k+1) m n _).trans (u.norm_bound k)

theorem spaceOperatorSeminorm_comp_spread_le (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (m n : ℕ) :
    spaceOperatorSeminorm D (T.comp (completedSpread D m n)) ≤
      spaceOperatorSeminorm D T := by
  rw [spaceOperatorSeminorm_apply]
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨u, rfl⟩
  have h := (u.spread m n).limsup_le_spaceOperatorSeminorm T
  simpa only [BlockTestSequence.spread, completedSpread_denseEmbedding,
    ContinuousLinearMap.comp_apply] using h

theorem spaceOperatorSeminorm_comp_spread_eq_zero (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (m n : ℕ)
    (hT : spaceOperatorSeminorm D T = 0) :
    spaceOperatorSeminorm D (T.comp (completedSpread D m n)) = 0 := by
  apply le_antisymm _ (apply_nonneg _ _)
  simpa only [hT] using spaceOperatorSeminorm_comp_spread_le D T m n

theorem spaceOperatorSeminorm_comp_integerShift_le (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (d : ℤ) :
    spaceOperatorSeminorm D (T.comp (integerShift D d)) ≤
      spaceOperatorSeminorm D T := by
  cases d <;> exact spaceOperatorSeminorm_comp_spread_le D T _ _

theorem spaceOperatorSeminorm_comp_integerShift_eq_zero (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (d : ℤ)
    (hT : spaceOperatorSeminorm D T = 0) :
    spaceOperatorSeminorm D (T.comp (integerShift D d)) = 0 := by
  apply le_antisymm _ (apply_nonneg _ _)
  simpa only [hT] using spaceOperatorSeminorm_comp_integerShift_le D T d

theorem spaceOperatorSeminorm_comp_laurent_eq_zero (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (a : WienerSequences 𝕜)
    (hT : spaceOperatorSeminorm D T = 0) :
    spaceOperatorSeminorm D (T.comp (laurentOperator D a)) = 0 := by
  let F : WienerSequences 𝕜 →L[𝕜] (ShiftSpace D →L[𝕜] ShiftSpace D) :=
    (ContinuousLinearMap.compL 𝕜 _ _ _ T).comp (laurentOperator D)
  change spaceOperatorSeminorm D (F a) = 0
  apply wiener_map_seminorm_zero_of_single (spaceOperatorSeminorm D)
    (spaceOperatorSeminorm_continuous D) F
  intro i c
  have hs : (lp.single 1 i c : WienerSequences 𝕜) =
      c • (lp.single 1 i (1 : 𝕜) : WienerSequences 𝕜) := by
    ext j
    by_cases h : i = j <;> simp [lp.single_apply, h]
  rw [hs, map_smul]
  change spaceOperatorSeminorm D (c • T.comp (laurentOperator D (lp.single 1 i 1))) = 0
  rw [laurentOperator_single, map_smul_eq_mul,
    spaceOperatorSeminorm_comp_integerShift_eq_zero D T i hT, mul_zero]

end ThesisCommon.GowersMaurey
