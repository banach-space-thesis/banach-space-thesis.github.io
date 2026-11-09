import BanachIsometric.QuaternionicNormalTrace
import BanachIsometric.QuaternionicSimilarityNormalization
import BanachIsometric.HermitianTraceSaturation
import Mathlib.Analysis.NormedSpace.Normalize

/-!
# Quaternionic simultaneous-similarity rigidity via actual real traces

Alternative to a separate quaternionic spectral theorem: use an actual real
maximal eigenvector and the four-rank normal trace formula. All input section
maps are linear for the original right quaternionic action. The real spectral
theorem is used internally; no eigenbasis or proportionality premise is added.
-/

namespace BanachIsometric.Quaternionic

open NormedSpace
open scoped Quaternion BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module Hᵐᵒᵖ E] [IsScalarTower ℝ Hᵐᵒᵖ E] [FiniteDimensional Hᵐᵒᵖ E]

local instance : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ Hᵐᵒᵖ E

private theorem exists_unit_mem_real_submodule (S : Submodule ℝ E)
    (hS : 0 < Module.finrank ℝ S) : ∃ x : E, x ∈ S ∧ ‖x‖ = 1 := by
  let b := stdOrthonormalBasis ℝ S
  let i : Fin (Module.finrank ℝ S) := ⟨0, hS⟩
  exact ⟨b i, (b i).property, b.orthonormal.1 i⟩

omit [Module Hᵐᵒᵖ E] [IsScalarTower ℝ Hᵐᵒᵖ E] [FiniteDimensional Hᵐᵒᵖ E] in
private theorem common_max_scale_one
    (q : E → ℝ) (S T : Submodule ℝ E) (U : S ≃ₗᵢ[ℝ] T) {c M : ℝ}
    (hc : 0 < c) (hM : 0 < M) (hs : ∀ x, q (U x) = c * q x)
    (hbound : ∀ x, q x ≤ M * ‖x‖ ^ 2)
    (x : S) (hx : ‖x‖ = 1) (hqx : q x = M)
    (y : T) (hy : ‖y‖ = 1) (hqy : q y = M) : c = 1 := by
  have hle : c * M ≤ M := by
    have h := hbound (U x)
    rw [hs, hqx] at h
    have hn : ‖(U x : E)‖ = 1 := by change ‖U x‖ = 1; rw [U.norm_map, hx]
    rwa [hn, one_pow, mul_one] at h
  have hge : M ≤ c * M := by
    have h := hbound (U.symm y)
    have hn : ‖(U.symm y : E)‖ = 1 := by change ‖U.symm y‖ = 1; rw [U.symm.norm_map, hy]
    rw [hn, one_pow, mul_one] at h
    have ht := hs (U.symm y)
    rw [U.apply_symm_apply, hqy] at ht
    exact ht.trans_le (mul_le_mul_of_nonneg_left h hc.le)
  nlinarith

theorem hermitianSquare_proportional_of_quaternionic_similarities
    {n : ℕ} (hn : 2 ≤ n) (hdim : Module.finrank Hᵐᵒᵖ E = n + 1)
    (P Q : HermitianForm E) (hP : ∀ x y, (P.form x y).re = inner ℝ x y)
    (hQpos : ∀ x : E, x ≠ 0 → 0 < (Q.form x x).re)
    (hsim : ∀ S T : Submodule Hᵐᵒᵖ E, Module.finrank Hᵐᵒᵖ S = n → Module.finrank Hᵐᵒᵖ T = n →
      ∃ U : S ≃ₗ[Hᵐᵒᵖ] T, ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        (∀ x, ‖U x‖ = c₁ * ‖x‖) ∧
        ∀ x, (Q.form (U x : E) (U x : E)).re = c₂ ^ 2 * (Q.form (x : E) (x : E)).re) :
    ∃ M : ℝ, 0 < M ∧ ∀ x, (Q.form x x).re = M * ‖x‖ ^ 2 := by
  classical
  let B := Q.realBilinear
  have hB : ∀ x y, star (B x y) = B y x := Q.realBilinear_symmetric
  have hreal : Module.finrank ℝ E = 4 * (n + 1) := by
    have h := Module.finrank_mul_finrank ℝ Hᵐᵒᵖ E
    rw [finrank_real_opposite, hdim] at h
    exact h.symm
  obtain ⟨b, a, ha, heig⟩ := exists_positive_eigenbasis_hermitianRelativeOperator B hB hQpos rfl
  let z : Fin (Module.finrank ℝ E) := ⟨0, by rw [hreal]; omega⟩
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ a
    (show (Finset.univ : Finset (Fin (Module.finrank ℝ E))).Nonempty from ⟨z, Finset.mem_univ z⟩)
  let u : E := b m
  let M : ℝ := a m
  have hu : ‖u‖ = 1 := b.orthonormal.1 m
  have hM : 0 < M := ha m
  have hQu : (Q.form u u).re = M :=
    re_relativeOperator_eigenvector_diagonal B hB u hu M (heig m)
  have hbound (x : E) : (Q.form x x).re ≤ M * ‖x‖ ^ 2 := by
    change B x x ≤ M * ‖x‖ ^ 2
    rw [← inner_hermitianRelativeOperator B hB]
    exact re_inner_apply_le_eigenvalue_bound _ (hermitianRelativeOperator_isSymmetric B hB)
      b a heig (fun i => hm i (Finset.mem_univ i)) x
  have hmaps (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
      ∃ U : realHermitianNormalHyperplane P x ≃ₗᵢ[ℝ] realHermitianNormalHyperplane P y,
        ∃ c : ℝ, 0 < c ∧ ∀ z,
          (Q.form (U z : E) (U z : E)).re = c * (Q.form (z : E) (z : E)).re := by
    obtain ⟨T, c₁, c₂, hc₁, hc₂, hp, hq⟩ := hsim
      (hermitianNormalHyperplane P x) (hermitianNormalHyperplane P y)
      (hermitianNormalHyperplane_finrank P hP hdim x hx)
      (hermitianNormalHyperplane_finrank P hP hdim y hy)
    exact exists_real_isometry_of_quaternionic_simultaneous_similarity Q _ _ T c₁ c₂ hc₁ hc₂ hp hq
  have hu_mem (x : E) (hx : x ∈ realHermitianNormalHyperplane P u) :
      u ∈ realHermitianNormalHyperplane P x := by
    rw [mem_realHermitianNormalHyperplane] at hx ⊢
    rw [← P.star_symm u x, hx, star_zero]
  have hdimU := realHermitianNormalHyperplane_finrank P hP hdim u hu
  obtain ⟨v, hv_mem, hv⟩ := exists_unit_mem_real_submodule (realHermitianNormalHyperplane P u)
    (by rw [hdimU]; omega)
  let A : ℝ := (Q.form v v).re
  have hunit (x : E) (hx : x ∈ realHermitianNormalHyperplane P u) (hxn : ‖x‖ = 1) :
      (Q.form x x).re = A := by
    obtain ⟨U, c, hc, hs⟩ := hmaps x v hxn hv
    have hc1 : c = 1 := common_max_scale_one (fun z => (Q.form z z).re) _ _ U hc hM hs hbound
      ⟨u, hu_mem x hx⟩ hu hQu ⟨u, hu_mem v hv_mem⟩ hu hQu
    have ht := re_trace_relativeOperator_scaling_of_isometry
      (restrictSesqForm B (realHermitianNormalHyperplane P x))
      (restrictSesqForm B (realHermitianNormalHyperplane P v))
      (restrictSesqForm_hermitian B hB _) (restrictSesqForm_hermitian B hB _) U c hs
    change LinearMap.trace ℝ _ (hermitianRelativeOperator (restrictSesqForm B _)) =
      c * LinearMap.trace ℝ _ (hermitianRelativeOperator (restrictSesqForm B _)) at ht
    rw [trace_realHermitianNormalHyperplane P Q hP v hv,
      trace_realHermitianNormalHyperplane P Q hP x hxn, hc1, one_mul] at ht
    dsimp [A]
    linarith
  have hconstant (x : realHermitianNormalHyperplane P u) :
      (Q.form x.val x.val).re = A * ‖x‖ ^ 2 := by
    by_cases hx : x = 0
    · subst x
      simp only [ZeroMemClass.coe_zero, Q.zero_right, Quaternion.re_zero, norm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    have hxv : x.val ≠ 0 := fun h => hx (Subtype.ext h)
    have hn : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr hxv
    have hw : normalize x.val ∈ realHermitianNormalHyperplane P u :=
      (realHermitianNormalHyperplane P u).smul_mem (‖x.val‖⁻¹) x.property
    have h := hunit (normalize x.val) hw (norm_normalize hxv)
    change B (‖x.val‖⁻¹ • x.val) (‖x.val‖⁻¹ • x.val) = A at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    change B x.val x.val = A * ‖x.val‖ ^ 2
    field_simp [hn] at h
    nlinarith
  let S := hermitianNormalHyperplane P u
  let T := hermitianNormalHyperplane P v
  have hdS : Module.finrank Hᵐᵒᵖ S = n := hermitianNormalHyperplane_finrank P hP hdim u hu
  have hdT : Module.finrank Hᵐᵒᵖ T = n := hermitianNormalHyperplane_finrank P hP hdim v hv
  have hposZ : 0 < Module.finrank Hᵐᵒᵖ ↥(S ⊓ T) := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq S T
    have hle := Submodule.finrank_le (S ⊔ T)
    omega
  have hposZR : 0 < Module.finrank ℝ ((S ⊓ T).restrictScalars ℝ) := by
    have h := Module.finrank_mul_finrank ℝ Hᵐᵒᵖ ((S ⊓ T).restrictScalars ℝ)
    rw [finrank_real_opposite, ((S ⊓ T).restrictScalarsEquiv ℝ).finrank_eq] at h
    omega
  obtain ⟨w, hw_mem, hw⟩ := exists_unit_mem_real_submodule ((S ⊓ T).restrictScalars ℝ) hposZR
  have hwU : w ∈ realHermitianNormalHyperplane P u := hw_mem.1
  have hwV : w ∈ realHermitianNormalHyperplane P v := hw_mem.2
  obtain ⟨U, c, _, hs⟩ := hmaps u v hu hv
  have hvalue (x : realHermitianNormalHyperplane P v) (hx : ‖x‖ = 1) :
      (Q.form x.val x.val).re = c * A := by
    have h := hs (U.symm x)
    rw [U.apply_symm_apply, hconstant, U.symm.norm_map, hx, one_pow, mul_one] at h
    exact h
  have hMA : M = A := by
    have hm' := hvalue ⟨u, hu_mem v hv_mem⟩ hu
    rw [hQu] at hm'
    have hw' := hvalue ⟨w, hwV⟩ hw
    rw [hunit w hwU hw] at hw'
    linarith
  have ht := trace_relativeOperator_of_scalar_diagonal
    (restrictSesqForm B (realHermitianNormalHyperplane P u))
    (fun x y => Q.realBilinear_symmetric x.val y.val) M
    (fun x => by rw [hMA]; exact hconstant x)
  rw [trace_realHermitianNormalHyperplane P Q hP u hu, hdimU, hQu] at ht
  have htrace : LinearMap.trace ℝ E (hermitianRelativeOperator B) = (Module.finrank ℝ E : ℝ) * M := by
    rw [hreal]
    push_cast at ht ⊢
    nlinarith
  refine ⟨M, hM, ?_⟩
  intro x
  have h := symmetric_scalar_diagonal_of_trace_saturates_bound (hermitianRelativeOperator B)
    (hermitianRelativeOperator_isSymmetric B hB) M
    (fun z => by rw [inner_hermitianRelativeOperator B hB]; exact hbound z) htrace x
  rwa [inner_hermitianRelativeOperator B hB] at h

end

end BanachIsometric.Quaternionic
