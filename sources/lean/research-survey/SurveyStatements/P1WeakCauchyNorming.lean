import SurveyStatements.P1GoldstineSequences
import SurveyStatements.P1WeakCauchyBidual
import Mathlib.Tactic.FieldSimp

/-! A noncanonical bidual functional has an isomorphically norming kernel
in the original dual. This proves the norming ingredient in Rosenthal's
basic subsequence construction from an actual nontrivial weak-Cauchy
sequence. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
open Set Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

local instance : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
local instance : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
local instance : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
local instance : NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ X)) := inferInstance

theorem bidual_annihilator_kernel_norms
    (ξ : StrongDual ℂ (StrongDual ℂ X))
    (ψ : StrongDual ℂ (StrongDual ℂ (StrongDual ℂ X)))
    (hψ : ‖ψ‖ ≤ 1)
    (hvanish : ∀ x : X, ψ (NormedSpace.inclusionInDoubleDual ℂ X x) = 0)
    (hψξ : ψ ξ ≠ 0) :
    ∃ q : ℝ, 0 < q ∧ ∀ x : X,
      ∃ f : StrongDual ℂ X, ‖f‖ ≤ 1 ∧ ξ f = 0 ∧ q * ‖x‖ ≤ ‖f x‖ := by
  classical
  let c : ℝ := ‖ψ ξ‖
  have hc : 0 < c := norm_pos_iff.mpr hψξ
  let B : ℝ := ‖ξ‖
  have hB : 0 ≤ B := norm_nonneg ξ
  let R : ℝ := 2 * B / c
  have hR : 0 ≤ R := div_nonneg (by positivity) hc.le
  have hRc : R * (c / 2) = B := by
    dsimp [R]
    field_simp
  let C : ℝ := 1 + R
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨1 / (2 * C), by positivity, ?_⟩
  intro x
  by_cases hx : x = 0
  · refine ⟨0, by simp, by simp, ?_⟩
    simp [hx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let δ : ℝ := min (c / 2) (‖x‖ / (2 * C))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨g, hg, hgapprox⟩ := goldstine_finite_approximation ψ hψ
    {ξ, NormedSpace.inclusionInDoubleDual ℂ X x} hδ
  have hgξ : ‖ξ g - ψ ξ‖ < c / 2 :=
    (hgapprox ξ (by simp)).trans_le (min_le_left _ _)
  have hgx : ‖g x‖ ≤ ‖x‖ / (2 * C) := by
    have h := hgapprox (NormedSpace.inclusionInDoubleDual ℂ X x) (by simp)
    simpa only [hvanish, sub_zero] using h.le.trans (min_le_right _ _)
  have hgξlower : c / 2 ≤ ‖ξ g‖ := by
    have h := norm_sub_norm_le (ψ ξ) (ξ g)
    rw [norm_sub_rev] at h
    change c - ‖ξ g‖ ≤ _ at h
    linarith
  have hgξpos : 0 < ‖ξ g‖ := lt_of_lt_of_le (by positivity) hgξlower
  obtain ⟨f, hfnorm, hfx⟩ := exists_dual_vector ℂ x hx
  have hξf : ‖ξ f‖ ≤ B := by
    simpa only [hfnorm, mul_one] using ξ.le_opNorm f
  have hratio : ‖ξ f / ξ g‖ ≤ R := by
    rw [norm_div]
    apply (div_le_iff₀ hgξpos).mpr
    exact hξf.trans (by
      have h := mul_le_mul_of_nonneg_left hgξlower hR
      rwa [hRc] at h)
  let h : StrongDual ℂ X := f - (ξ f / ξ g) • g
  have hhξ : ξ h = 0 := by
    dsimp [h]
    simp only [map_sub, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mp hgξpos.ne')]
    exact sub_self _
  have hhnorm : ‖h‖ ≤ C := by
    calc
      ‖h‖ ≤ ‖f‖ + ‖(ξ f / ξ g) • g‖ := norm_sub_le _ _
      _ ≤ 1 + R := by
        rw [hfnorm, norm_smul]
        exact add_le_add_left ((mul_le_mul_of_nonneg_left hg (norm_nonneg _)).trans
          (by simpa only [mul_one] using hratio)) _
      _ = C := rfl
  have herror : ‖(ξ f / ξ g) • g x‖ ≤ ‖x‖ / 2 := by
    rw [norm_smul]
    have hratioC : ‖ξ f / ξ g‖ ≤ C := hratio.trans (by dsimp [C]; linarith)
    calc
      _ ≤ C * (‖x‖ / (2 * C)) :=
        mul_le_mul hratioC hgx (norm_nonneg _) hC.le
      _ = ‖x‖ / 2 := by field_simp
  have hhx : ‖x‖ / 2 ≤ ‖h x‖ := by
    have hnear : ‖f x‖ ≤ ‖h x‖ + ‖(ξ f / ξ g) • g x‖ := by
      calc
        ‖f x‖ = ‖h x + (ξ f / ξ g) • g x‖ := by
          simp only [h, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
            sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have hfxnorm : ‖f x‖ = ‖x‖ := by rw [hfx]; simp
    rw [hfxnorm] at hnear
    linarith
  let k : StrongDual ℂ X := (C : ℂ)⁻¹ • h
  have hknorm : ‖k‖ = C⁻¹ * ‖h‖ := by
    simp only [k, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hC]
  have hkx : ‖k x‖ = C⁻¹ * ‖h x‖ := by
    simp only [k, ContinuousLinearMap.smul_apply, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [hknorm]
    have h := mul_le_mul_of_nonneg_left hhnorm (inv_nonneg.mpr hC.le)
    simpa only [inv_mul_cancel₀ hC.ne'] using h
  · simp only [k, map_smul, hhξ, smul_zero]
  · rw [hkx]
    have h := mul_le_mul_of_nonneg_left hhx (inv_nonneg.mpr hC.le)
    convert h using 1 <;> field_simp

theorem noncanonical_bidual_kernel_norms [CompleteSpace X]
    (ξ : StrongDual ℂ (StrongDual ℂ X))
    (hξ : ξ ∉ Set.range (NormedSpace.inclusionInDoubleDual ℂ X)) :
    ∃ q : ℝ, 0 < q ∧ ∀ x : X,
      ∃ f : StrongDual ℂ X, ‖f‖ ≤ 1 ∧ ξ f = 0 ∧ q * ‖x‖ ≤ ‖f x‖ := by
  let S := SurveyStatements.P4.bidualImage (𝕜 := ℂ) X
  obtain ⟨ψ, hψ, hψvanish, hψξ⟩ := closedSubmodule_exists_bounded_annihilator S
    (SurveyStatements.P4.isClosed_bidualImage (𝕜 := ℂ) (F := X)) hξ
  exact bidual_annihilator_kernel_norms ξ ψ hψ
    (fun x => hψvanish _ ⟨x, rfl⟩) hψξ

theorem nontrivial_weakCauchy_kernel_norms [CompleteSpace X]
    (s : ℕ → X) (hs : IsWeakCauchySequence s)
    (hnot : ¬ ∃ x : X, ∀ f : StrongDual ℂ X,
      Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) :
    ∃ q : ℝ, 0 < q ∧ ∀ x : X,
      ∃ f : StrongDual ℂ X, ‖f‖ ≤ 1 ∧ weakCauchyLimitBidual s hs f = 0 ∧
        q * ‖x‖ ≤ ‖f x‖ := by
  apply noncanonical_bidual_kernel_norms
  exact mt (weakCauchy_weakly_convergent_iff_bidual_mem_range s hs).mpr hnot

end SurveyStatements.P1
