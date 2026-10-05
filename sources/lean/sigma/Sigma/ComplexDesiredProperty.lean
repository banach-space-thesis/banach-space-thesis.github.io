import Sigma.ComplexEstimates
import Mathlib.Analysis.Normed.Operator.Banach

/-! Complex norming sequences and the analytic contradiction in the Sigma
paper's unnumbered complex extension. The construction hypotheses of the last
theorem are explicit: it does not claim that the existing real construction
already enumerates complex norming sequences. -/
namespace SigmaNonprimarity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def IsComplexCNorming (e : ℕ → E →L[ℂ] ℂ) (c : ℝ) : Prop :=
  0 < c ∧ c ≤ 1 ∧ (∀ n, ‖e n‖ ≤ 1) ∧ ∀ x, c * ‖x‖ ≤ ⨆ n, ‖e n x‖

def IsComplexNorming (e : ℕ → E →L[ℂ] ℂ) : Prop := ∃ c, IsComplexCNorming e c

/-- Definition 5.2 of the cited complex extension, with the real norm embedded
in the complex scalar field in the required coordinate equality. -/
def ComplexDesiredProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ e : ℕ → E →L[ℂ] ℂ, IsComplexNorming e →
    ∃ f : E, ¬ ∃ g : E, ∀ n, e n g = (‖e n f‖ : ℂ)

theorem complex_evaluations_bddAbove (e : ℕ → E →L[ℂ] ℂ)
    (he : ∀ n, ‖e n‖ ≤ 1) (x : E) : BddAbove (Set.range fun n => ‖e n x‖) := by
  refine ⟨‖x‖, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact ((e n).le_opNorm x).trans (by
    simpa using mul_le_mul_of_nonneg_right (he n) (norm_nonneg x))

theorem complex_norming_separates_points {e : ℕ → E →L[ℂ] ℂ}
    (he : IsComplexNorming e) {x y : E} (h : ∀ n, e n x = e n y) : x = y := by
  rcases he with ⟨c,hc,_,_,hnorm⟩
  have hz : ∀ n, e n (x-y) = 0 := fun n => by simp [map_sub,h n]
  have hbound := hnorm (x-y)
  simp only [hz,norm_zero,ciSup_const] at hbound
  have : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem complex_select_large_evaluations {e : ℕ → E →L[ℂ] ℂ} {c : ℝ}
    (he : IsComplexCNorming e c) (f : ℕ → E) (hf : ∀ n, ‖f n‖ = 1) :
    ∃ k : ℕ → ℕ, ∀ n, c/2 < ‖e (k n) (f n)‖ := by
  classical
  have hex (n : ℕ) : ∃ k : ℕ, c/2 < ‖e k (f n)‖ := by
    have h := he.2.2.2 (f n)
    rw [hf n,mul_one] at h
    apply exists_lt_of_lt_ciSup
    exact lt_of_lt_of_le (by linarith [he.1]) h
  exact ⟨fun n => Classical.choose (hex n),fun n => Classical.choose_spec (hex n)⟩

theorem not_complexDesiredProperty_iff :
    ¬ ComplexDesiredProperty E ↔ ∃ e : ℕ → E →L[ℂ] ℂ,
      IsComplexNorming e ∧ ∀ f : E, ∃ g : E, ∀ n, e n g = (‖e n f‖ : ℂ) := by
  classical
  simp only [ComplexDesiredProperty,not_forall,not_exists,not_not,exists_prop]

/-- The complete complex analytic contradiction from the three selected levels.
The approximation permits every complex coefficient, and both forbidden cuts
are tested using distances of complex evaluations. -/
theorem complex_no_modulus_of_three_levels
    (e : ℕ → E →L[ℂ] ℂ) (he : ∀ n, ‖e n‖ ≤ 1)
    (f : E) (H : Submodule ℂ E) (J₀ J₁ J₂ : Set ℕ) (a : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (ha : 11*δ < ‖a‖)
    (hp : ∀ n ∈ J₂, ‖e n f - 2*a‖ < 3*δ)
    (hm : ∀ n ∈ J₁ \ J₂, ‖e n f - (-(2*a))‖ < 3*δ)
    (hz : ∀ n ∈ J₀ \ J₁, ‖e n f‖ < 3*δ)
    (hdense : ∀ g : E, ∃ (r : ℂ) (s : E), s ∈ H ∧ ‖g - (r • f + s)‖ < δ)
    (hsep₁ : ∀ s ∈ H, ¬ ComplexUniformGap (fun n => e n s) J₁ (J₀ \ J₁))
    (hsep₂ : ∀ s ∈ H, ¬ ComplexUniformGap (fun n => e n s) J₂ (J₁ \ J₂)) :
    ¬ ∃ g : E, ∀ n, e n g = (‖e n f‖ : ℂ) := by
  rintro ⟨g,hg⟩
  obtain ⟨r,s,hs,hgs⟩ := hdense g
  have happ (n : ℕ) : ‖(‖e n f‖ : ℂ) - (r * e n f + e n s)‖ < δ := by
    have hbound : ‖e n (g - (r • f + s))‖ ≤ ‖g - (r • f + s)‖ :=
      ((e n).le_opNorm _).trans (by
        simpa using mul_le_mul_of_nonneg_right (he n) (norm_nonneg (g-(r•f+s))))
    simpa only [map_sub,map_add,map_smul,hg,smul_eq_mul] using hbound.trans_lt hgs
  rcases complex_three_level_separation (fun n => e n f) (fun n => e n s)
    J₀ J₁ J₂ a δ r hδ ha hp hm hz happ with h | h
  · exact hsep₁ s hs h
  · exact hsep₂ s hs h

end SigmaNonprimarity
