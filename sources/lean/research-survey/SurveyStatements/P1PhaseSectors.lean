import SurveyStatements.P1PhaseSectorEstimate
import SurveyStatements.P1Transfer
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A fixed finite cover of the phase circle and weighted selection of one
pair of sectors. Both the coefficient phases and functional-value phases
are controlled, so cross-evaluation of two selected witnesses is valid over
the complex field. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical

namespace SurveyStatements.P1

theorem exists_finite_unitScalar_sector_cover {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Finset ℂ, A.Nonempty ∧ (∀ α ∈ A, ‖α‖ = 1) ∧
      ∀ z : ℂ, ‖z‖ = 1 → ∃ α ∈ A, ‖z - α‖ < δ := by
  let U : {z : ℂ // z ∈ unitScalars} → Set ℂ := fun α => {z | ‖z - α.1‖ < δ}
  have hU : ∀ α, IsOpen (U α) := fun α =>
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  have hcover : unitScalars ⊆ ⋃ α, U α := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, by simpa [U] using hδ⟩
  obtain ⟨S, hS⟩ := isCompact_unitScalars.elim_finite_subcover U hU hcover
  let A := S.image Subtype.val
  have hA : ∀ z : ℂ, ‖z‖ = 1 → ∃ α ∈ A, ‖z - α‖ < δ := by
    intro z hz
    obtain ⟨α, hα, hzα⟩ := Set.mem_iUnion₂.mp (hS hz)
    exact ⟨α.1, Finset.mem_image.mpr ⟨α, hα, rfl⟩, hzα⟩
  obtain ⟨α, hα, _⟩ := hA 1 (by simp)
  refine ⟨A, ⟨α, hα⟩, ?_, hA⟩
  intro β hβ
  obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hβ
  exact γ.2

theorem exists_weighted_color_fiber {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : Finset ℕ) (c : ℕ → ι) (w : ℕ → ℝ) :
    ∃ j : ι, ∑ i ∈ F, w i ≤ (Fintype.card ι : ℝ) * ∑ i ∈ F with c i = j, w i := by
  classical
  by_contra! h
  have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty :
    (Finset.univ : Finset ι).Nonempty) (fun j _ => h j)
  rw [← Finset.mul_sum, Finset.sum_fiberwise F c w, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hlt
  exact (lt_irrefl _) hlt

theorem unitPhase_near_implies_value_near (b β : ℂ) (hβ : ‖β‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hb : b = 0 ∨ ‖unitNormalize b - β‖ ≤ δ) :
    ‖b - (‖b‖ : ℂ) * β‖ ≤ δ * ‖b‖ := by
  rcases hb with rfl | hb
  · simp
  · calc
      _ = ‖(‖b‖ : ℂ) • (unitNormalize b - β)‖ := by
        rw [smul_sub, norm_smul_unitNormalize]
        rfl
      _ = ‖b‖ * ‖unitNormalize b - β‖ := by
        rw [norm_smul]
        simp only [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg b)]
      _ ≤ ‖b‖ * δ := mul_le_mul_of_nonneg_left hb (norm_nonneg b)
      _ = _ := mul_comm _ _

theorem exists_complex_phase_sector_witness :
    ∃ A : Finset ℂ, A.Nonempty ∧ (∀ α ∈ A, ‖α‖ = 1) ∧
      ∃ D : ℕ, 0 < D ∧ ∀ F : Finset ℕ, ∀ a b : ℕ → ℂ,
      (∀ i ∈ F, ‖a i‖ = 1) → ∃ α β : ℂ, α ∈ A ∧ β ∈ A ∧
      ∃ S : Finset ℕ, S ⊆ F ∧
        (∑ i ∈ F, ‖b i‖) ≤ (D : ℝ) * ∑ i ∈ S, ‖b i‖ ∧
        (∀ i ∈ S, ‖a i - α‖ ≤ (1 / 4 : ℝ)) ∧
        ∀ i ∈ S, ‖b i - (‖b i‖ : ℂ) * β‖ ≤ (1 / 4 : ℝ) * ‖b i‖ := by
  classical
  obtain ⟨A, hAne, hAnorm, hAcover⟩ :=
    exists_finite_unitScalar_sector_cover (by norm_num : 0 < (1 / 4 : ℝ))
  let ι := {α : ℂ // α ∈ A}
  letI : Fintype ι := Fintype.ofFinset A (fun _ => Iff.rfl)
  letI : Nonempty ι := ⟨⟨hAne.choose, hAne.choose_spec⟩⟩
  let center (z : ℂ) : ι := if hz : ‖z‖ = 1 then
    ⟨(hAcover z hz).choose, (hAcover z hz).choose_spec.1⟩ else Classical.choice inferInstance
  have hcenter (z : ℂ) (hz : ‖z‖ = 1) : ‖z - (center z).1‖ ≤ (1 / 4 : ℝ) := by
    simpa only [center, dif_pos hz] using (hAcover z hz).choose_spec.2.le
  refine ⟨A, hAne, hAnorm, Fintype.card (ι × ι), Fintype.card_pos, ?_⟩
  intro F a b ha
  let c : ℕ → ι × ι := fun i => (center (a i), center (unitNormalize (b i)))
  obtain ⟨j, hj⟩ := exists_weighted_color_fiber F c (fun i => ‖b i‖)
  let S := F.filter (fun i => c i = j)
  refine ⟨j.1.1, j.2.1,
    j.1.2, j.2.2, S, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · convert hj using 1 <;> congr 2 <;> ext i <;> simp [S]
  · intro i hi
    obtain ⟨hiF, hij⟩ := Finset.mem_filter.mp hi
    have heq : center (a i) = j.1 := congrArg Prod.fst hij
    simpa only [heq] using hcenter (a i) (ha i hiF)
  · intro i hi
    obtain ⟨hiF, hij⟩ := Finset.mem_filter.mp hi
    apply unitPhase_near_implies_value_near _ _ (hAnorm _ j.2.2) (by norm_num)
    by_cases hbi : b i = 0
    · exact Or.inl hbi
    · apply Or.inr
      have heq : center (unitNormalize (b i)) = j.2 := congrArg Prod.snd hij
      simpa only [heq] using hcenter (unitNormalize (b i)) (norm_unitNormalize hbi)

end SurveyStatements.P1
