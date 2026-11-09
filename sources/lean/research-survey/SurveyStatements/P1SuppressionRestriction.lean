import SurveyStatements.P1SuppressionWitnesses

/-! Converting suppression on an infinite set into the same property on
any injective sequence taking values in that set. Finite zero coefficients
are removed explicitly before the finitely-supported formulation is used. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def finiteSetCoefficients (F : Finset ℕ) (a : ℕ → ℂ) : ℕ →₀ ℂ :=
  Finsupp.onFinset F (fun i => if i ∈ F then a i else 0) (by
    intro i hi
    by_contra hiF
    exact hi (if_neg hiF))

@[simp] theorem finiteSetCoefficients_apply (F : Finset ℕ) (a : ℕ → ℂ) (i : ℕ) :
    finiteSetCoefficients F a i = if i ∈ F then a i else 0 := rfl

theorem HasUnitModulusSuppressionOn.sum_bound {e : ℕ → X} {K : ℝ} {M : Set ℕ}
    (h : HasUnitModulusSuppressionOn e K M) (F : Finset ℕ) (hF : (F : Set ℕ) ⊆ M)
    (a : ℕ → ℂ) (ha : ∀ i ∈ F, a i = 0 ∨ ‖a i‖ = 1)
    (S : Finset ℕ) (hSF : S ⊆ F) :
    ‖∑ i ∈ S, a i • e i‖ ≤ K * ‖∑ i ∈ F, a i • e i‖ := by
  let b := finiteSetCoefficients F a
  have hbF : b.support ⊆ F := Finsupp.support_onFinset_subset
  have hb (i : ℕ) (hi : i ∈ F) : b i = a i := by
    simp only [b, finiteSetCoefficients_apply, if_pos hi]
  have hbunit : ∀ i ∈ b.support, ‖b i‖ = 1 := by
    intro i hi
    have hiF := hbF hi
    have hinz : a i ≠ 0 := by simpa only [hb i hiF] using Finsupp.mem_support_iff.mp hi
    simpa only [hb i hiF] using (ha i hiF).resolve_left hinz
  have hcombo : Finsupp.linearCombination ℂ e b = ∑ i ∈ F, a i • e i := by
    rw [Finsupp.linearCombination_apply_of_mem_supported ℂ hbF]
    exact Finset.sum_congr rfl (fun i hi => by rw [hb i hi])
  have hproj : (∑ i ∈ S ∩ b.support, b i • e i) = ∑ i ∈ S, a i • e i := by
    calc
      _ = ∑ i ∈ S, b i • e i := by
        apply Finset.sum_subset (Finset.inter_subset_left)
        intro i hi hin
        have hinb : i ∉ b.support := fun hmem => hin (Finset.mem_inter.mpr ⟨hi, hmem⟩)
        simp only [Finsupp.notMem_support_iff.mp hinb, zero_smul]
      _ = _ := Finset.sum_congr rfl (fun i hi => by rw [hb i (hSF hi)])
  have hbound := h b (fun i hi => hF (hbF hi)) hbunit (S ∩ b.support)
    Finset.inter_subset_right
  rwa [hproj, hcombo] at hbound

theorem HasUnitModulusSuppressionOn.subsequence {e : ℕ → X} {K : ℝ} {M : Set ℕ}
    (h : HasUnitModulusSuppressionOn e K M) (ν : ℕ → ℕ) (hν : Function.Injective ν)
    (hνM : ∀ i, ν i ∈ M) : HasUnitModulusSuppression (e ∘ ν) K := by
  intro F a ha S hSF
  let b := Function.extend ν a (fun _ => 0)
  have hb (i : ℕ) : b (ν i) = a i := hν.extend_apply _ _ i
  have hFM : ((F.image ν : Finset ℕ) : Set ℕ) ⊆ M := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hνM j
  have hflat : ∀ i ∈ F.image ν, b i = 0 ∨ ‖b i‖ = 1 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    simpa only [hb] using ha j hj
  have hbound := h.sum_bound (F.image ν) hFM b hflat (S.image ν)
    (Finset.image_subset_image hSF)
  rw [Finset.sum_image (fun i _ j _ hij => hν hij),
    Finset.sum_image (fun i _ j _ hij => hν hij)] at hbound
  simpa only [hb, Function.comp_apply] using hbound

end SurveyStatements.P1
