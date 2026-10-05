import Sigma.ComplexEstimates
import ThesisCommon.Analysis.NonseparatedCut

/-! Finite complex-valued tests can be encoded by their two real coordinates.
This proves the counting and cut-selection statements needed by the complex
modification of the simultaneous construction. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity
variable {D I : Type*}

def ComplexFinitelySeparated (ev : D → I → ℂ) (S : Set I) (M N : Set D) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ F : Finset I, (↑F : Set I) ⊆ S ∧
    ∀ m ∈ M, ∀ n ∈ N, ∃ i ∈ F, ε ≤ ‖ev m i - ev n i‖

def complexRealTest (ev : D → I → ℂ) (d : D) (t : Bool × I) : ℝ :=
  if t.1 then (ev d t.2).im else (ev d t.2).re

theorem complexRealTest_abs_le (ev : D → I → ℂ) (d : D) (t : Bool × I) :
    |complexRealTest ev d t| ≤ ‖ev d t.2‖ := by
  rcases t with ⟨b,i⟩
  cases b
  · exact Complex.abs_re_le_norm _
  · exact Complex.abs_im_le_norm _

theorem complexRealTest_sub_le (ev : D → I → ℂ) (m n : D) (t : Bool × I) :
    |complexRealTest ev m t - complexRealTest ev n t| ≤ ‖ev m t.2 - ev n t.2‖ := by
  rcases t with ⟨b,i⟩
  cases b
  · simpa [complexRealTest] using Complex.abs_re_le_norm (ev m i - ev n i)
  · simpa [complexRealTest] using Complex.abs_im_le_norm (ev m i - ev n i)

theorem complexFinitelySeparated_iff_real (ev : D → I → ℂ) (S : Set I) (M N : Set D) :
    ComplexFinitelySeparated ev S M N ↔
      FinitelySeparated (complexRealTest ev) (Set.univ ×ˢ S) M N := by
  classical
  constructor
  · rintro ⟨ε,hε,F,hF,hsep⟩
    refine ⟨ε/2,by linarith,Finset.univ.product F,?_,?_⟩
    · intro t ht
      exact ⟨Set.mem_univ _,hF (Finset.mem_product.mp ht).2⟩
    · intro m hm n hn
      obtain ⟨i,hi,hgap⟩ := hsep m hm n hn
      by_cases hr : ε/2 ≤ |(ev m i - ev n i).re|
      · exact ⟨(false,i),Finset.mem_product.mpr ⟨Finset.mem_univ _,hi⟩,hr⟩
      · have him : ε/2 ≤ |(ev m i - ev n i).im| := by
          have hb := Complex.norm_le_abs_re_add_abs_im (ev m i - ev n i)
          have hr' := lt_of_not_ge hr
          linarith
        exact ⟨(true,i),Finset.mem_product.mpr ⟨Finset.mem_univ _,hi⟩,him⟩
  · rintro ⟨ε,hε,F,hF,hsep⟩
    refine ⟨ε,hε,F.image Prod.snd,?_,?_⟩
    · intro i hi
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hi
      exact (hF ht).2
    · intro m hm n hn
      obtain ⟨t,ht,hgap⟩ := hsep m hm n hn
      exact ⟨t.2,Finset.mem_image.mpr ⟨t,ht,rfl⟩,
        hgap.trans (complexRealTest_sub_le ev m n t)⟩

theorem complexFinitelySeparated_univ_iff_real (ev : D → I → ℂ) (M N : Set D) :
    ComplexFinitelySeparated ev Set.univ M N ↔
      FinitelySeparated (complexRealTest ev) Set.univ M N := by
  simpa only [Set.univ_prod_univ] using complexFinitelySeparated_iff_real ev Set.univ M N

theorem complex_test_cardinal_lt {I : Type} (hI : #I < 𝔠) : #(Bool × I) < 𝔠 := by
  rw [Cardinal.mk_prod,Cardinal.mk_bool]
  simpa only [Cardinal.lift_id] using Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum
    ((Cardinal.nat_lt_aleph0 2).trans_le Cardinal.aleph0_le_continuum) hI

/-- The complex counting lemma keeps the same strict continuum bound. -/
theorem complex_separated_cuts_lt_continuum {D I : Type} (ev : D → I → ℂ)
    (hbound : ∀ d i, ‖ev d i‖ ≤ 1) (M : Set D) (hI : #I < 𝔠) :
    #{A : Set D // A ⊆ M ∧ ComplexFinitelySeparated ev Set.univ A (M \ A)} < 𝔠 := by
  have hreal := separated_cuts_lt_continuum (complexRealTest ev)
    (fun d t => (complexRealTest_abs_le ev d t).trans (hbound d t.2)) M
    (complex_test_cardinal_lt hI)
  simpa only [complexFinitelySeparated_univ_iff_real] using hreal

/-- Simultaneously retain both real and imaginary tests when choosing an
infinite nonseparated cut. -/
theorem complex_exists_infinite_nonseparated_cut {I : Type} (ev : ℕ → I → ℂ)
    (hbound : ∀ n i, ‖ev n i‖ ≤ 1) (hI : #I < 𝔠)
    (M D : Set ℕ) (hDM : D ⊆ M) (hD : D.Infinite) :
    ∃ A : Set ℕ, A ⊆ D ∧ A.Infinite ∧ (D \ A).Infinite ∧
      ¬ ComplexFinitelySeparated ev Set.univ A (M \ A) := by
  obtain ⟨A,hAD,hA,hdiff,hnsep⟩ := exists_infinite_nonseparated_cut (complexRealTest ev)
    (fun n t => (complexRealTest_abs_le ev n t).trans (hbound n t.2))
    (complex_test_cardinal_lt hI) M D hDM hD
  exact ⟨A,hAD,hA,hdiff,fun h => hnsep ((complexFinitelySeparated_univ_iff_real _ _ _).mp h)⟩

/-- A gap for one complex finite linear combination already separates a pair
by its finitely many generating tests. -/
theorem complexFinitelySeparated_of_sum_gap (ev : D → I → ℂ) (S : Set I) (M N : Set D)
    (F : Finset I) (hF : (↑F : Set I) ⊆ S) (c : I → ℂ) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ m ∈ M, ∀ n ∈ N,
      ε ≤ ‖(∑ i ∈ F, c i * ev m i) - ∑ i ∈ F, c i * ev n i‖) :
    ComplexFinitelySeparated ev S M N := by
  classical
  let A := ∑ i ∈ F, ‖c i‖
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let δ := ε / (A+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδε : δ*(A+1) = ε := div_mul_cancel₀ _ (by linarith : A+1 ≠ 0)
  refine ⟨δ,hδ,F,hF,?_⟩
  intro m hm n hn
  by_contra h
  push_neg at h
  have hsum : ‖(∑ i ∈ F, c i * ev m i) - ∑ i ∈ F, c i * ev n i‖ ≤ A*δ := by
    calc
      _ = ‖∑ i ∈ F, c i * (ev m i - ev n i)‖ := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ ∑ i ∈ F, ‖c i * (ev m i - ev n i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ F, ‖c i‖ * δ := Finset.sum_le_sum fun i hi => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (h i hi).le (norm_nonneg _)
      _ = A*δ := (Finset.sum_mul _ _ _).symm
  have hh := hgap m hm n hn
  nlinarith

end SigmaNonprimarity
