import SurveyStatements.P4FiniteFrame

/-!
# Finite coefficient paths with monotone coordinate projections

The coefficient space is realized as an actual finite-dimensional submodule
of a finite product of the original space, with its inherited supremum norm.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set Finset Module

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {N : ℕ}

def finitePrefixPath (v : Fin N → E) : (Fin N → 𝕜) →ₗ[𝕜] (Fin (N + 1) → E) where
  toFun c k := ∑ i : Fin N, if i.val < k.val then c i • v i else 0
  map_add' c d := by
    funext k
    simp only [Pi.add_apply, add_smul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp_all
  map_smul' a c := by
    funext k
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp_all [smul_smul]

lemma finitePrefixPath_step (v : Fin N → E) (c : Fin N → 𝕜) (i : Fin N) :
    finitePrefixPath v c ⟨i.val + 1, by omega⟩ -
      finitePrefixPath v c ⟨i.val, by omega⟩ = c i • v i := by
  simp only [finitePrefixPath, LinearMap.coe_mk, AddHom.coe_mk, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    by_cases hjlt : j.val < i.val
    · have hjlt' : j.val < i.val + 1 := by omega
      simp [hjlt, hjlt']
    · have hjnlt : ¬ j.val < i.val + 1 := by omega
      simp [hjlt, hjnlt]
  · simp

lemma finitePrefixPath_injective (v : Fin N → E) (hv : ∀ i, v i ≠ 0) :
    Function.Injective (finitePrefixPath (𝕜 := 𝕜) v) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro c hc
  funext i
  have hstep := finitePrefixPath_step v c i
  rw [hc] at hstep
  have heq : c i • v i = 0 := by simpa using hstep.symm
  exact (smul_eq_zero.mp heq).resolve_right (hv i)

def finiteCoefficientPrefix (k : Fin (N + 1)) : (Fin N → 𝕜) →ₗ[𝕜] (Fin N → 𝕜) where
  toFun c i := if i.val < k.val then c i else 0
  map_add' c d := by
    funext i
    simp only [Pi.add_apply]
    by_cases h : i.val < k.val <;> simp [h]
  map_smul' a c := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h : i.val < k.val <;> simp [h]

lemma finitePrefixPath_prefix (v : Fin N → E) (c : Fin N → 𝕜)
    (k l : Fin (N + 1)) :
    finitePrefixPath v (finiteCoefficientPrefix k c) l = finitePrefixPath v c (min k l) := by
  have hmin : (min k l).val = min k.val l.val := by
    by_cases h : k ≤ l
    · rw [min_eq_left h]
      exact (min_eq_left (show k.val ≤ l.val from h)).symm
    · rw [min_eq_right (le_of_not_ge h)]
      exact (min_eq_right (show l.val ≤ k.val from le_of_not_ge h)).symm
  simp only [finitePrefixPath, LinearMap.coe_mk, AddHom.coe_mk,
    finiteCoefficientPrefix, hmin]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hk : i.val < k.val <;> by_cases hl : i.val < l.val <;>
    simp [hk, hl, lt_min_iff]

abbrev FinitePathSpace (v : Fin N → E) := LinearMap.range (finitePrefixPath (𝕜 := 𝕜) v)

instance (priority := 1100) (v : Fin N → E) :
    NormedSpace 𝕜 (FinitePathSpace (𝕜 := 𝕜) v) where
  norm_smul_le c f := norm_smul_le c f.val

instance (v : Fin N → E) : FiniteDimensional 𝕜 (FinitePathSpace (𝕜 := 𝕜) v) :=
  LinearMap.finiteDimensional_range (finitePrefixPath (𝕜 := 𝕜) v)

def finitePathEquiv (v : Fin N → E) (hv : ∀ i, v i ≠ 0) :
    (Fin N → 𝕜) ≃ₗ[𝕜] FinitePathSpace (𝕜 := 𝕜) v :=
  LinearEquiv.ofInjective (finitePrefixPath (𝕜 := 𝕜) v) (finitePrefixPath_injective v hv)

lemma finitePathEquiv_apply (v : Fin N → E) (hv : ∀ i, v i ≠ 0) (c : Fin N → 𝕜) :
    (finitePathEquiv v hv c).val = finitePrefixPath v c := rfl

def finitePathBasis (v : Fin N → E) (hv : ∀ i, v i ≠ 0) :
    Basis (Fin N) 𝕜 (FinitePathSpace (𝕜 := 𝕜) v) :=
  (Pi.basisFun 𝕜 (Fin N)).map (finitePathEquiv v hv)

def finitePathProjection (v : Fin N → E) (hv : ∀ i, v i ≠ 0) (k : Fin (N + 1)) :
    FinitePathSpace (𝕜 := 𝕜) v →L[𝕜] FinitePathSpace (𝕜 := 𝕜) v :=
  ((finitePathEquiv v hv).toLinearMap.comp
    ((finiteCoefficientPrefix k).comp (finitePathEquiv v hv).symm.toLinearMap)).toContinuousLinearMap

lemma finitePathProjection_apply (v : Fin N → E) (hv : ∀ i, v i ≠ 0)
    (k : Fin (N + 1)) (f : FinitePathSpace (𝕜 := 𝕜) v) (l : Fin (N + 1)) :
    (finitePathProjection v hv k f).val l = f.val (min k l) := by
  let c := (finitePathEquiv v hv).symm f
  have hc : finitePathEquiv v hv c = f := (finitePathEquiv v hv).apply_symm_apply f
  rw [← hc]
  simp only [finitePathProjection, LinearMap.coe_toContinuousLinearMap',
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
    finitePathEquiv_apply]
  exact finitePrefixPath_prefix v c k l

/-- Prefix projections in this actual finite path norm have norm at most one. -/
lemma finitePathProjection_norm_le_one (v : Fin N → E) (hv : ∀ i, v i ≠ 0)
    (k : Fin (N + 1)) : ‖finitePathProjection (𝕜 := 𝕜) v hv k‖ ≤ 1 := by
  apply (finitePathProjection (𝕜 := 𝕜) v hv k).opNorm_le_bound (by norm_num)
  intro f
  change ‖(finitePathProjection v hv k f).val‖ ≤ 1 * ‖f.val‖
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg f.val)]
  intro l
  rw [finitePathProjection_apply]
  exact norm_le_pi_norm f.val (min k l)

end SurveyStatements.P4
