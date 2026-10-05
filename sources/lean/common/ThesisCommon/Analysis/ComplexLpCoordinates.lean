import ThesisCommon.Analysis.L1Lattice
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Sequences

/-! Actual real coordinates and pointwise modulus of complex Lp. All maps
act on the genuine a.e. equivalence classes, for an arbitrary measure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

def complexLpRe (μ : Measure X) : Lp ℂ p μ →L[ℝ] Lp ℝ p μ :=
  Complex.reCLM.compLpL p μ

def complexLpIm (μ : Measure X) : Lp ℂ p μ →L[ℝ] Lp ℝ p μ :=
  Complex.imCLM.compLpL p μ

def complexLpOfReal (μ : Measure X) : Lp ℝ p μ →L[ℝ] Lp ℂ p μ :=
  Complex.ofRealCLM.compLpL p μ

def complexLpModulus (f : Lp ℂ p μ) : Lp ℝ p μ :=
  lipschitzWith_one_norm.compLp (norm_zero : ‖(0 : ℂ)‖ = 0) f

theorem complexLpRe_coe (f : Lp ℂ p μ) :
    complexLpRe μ f =ᵐ[μ] fun x => (f x).re := Complex.reCLM.coeFn_compLpL f

theorem complexLpIm_coe (f : Lp ℂ p μ) :
    complexLpIm μ f =ᵐ[μ] fun x => (f x).im := Complex.imCLM.coeFn_compLpL f

theorem complexLpOfReal_coe (f : Lp ℝ p μ) :
    complexLpOfReal μ f =ᵐ[μ] fun x => (f x : ℂ) := Complex.ofRealCLM.coeFn_compLpL f

theorem complexLpModulus_coe (f : Lp ℂ p μ) :
    complexLpModulus f =ᵐ[μ] fun x => ‖f x‖ :=
  lipschitzWith_one_norm.coeFn_compLp _ f

@[simp] theorem complexLpRe_ofReal (f : Lp ℝ p μ) :
    complexLpRe μ (complexLpOfReal μ f) = f := by
  apply Lp.ext
  filter_upwards [complexLpRe_coe (complexLpOfReal μ f), complexLpOfReal_coe f] with x h₁ h₂
  simp [h₁, h₂]

@[simp] theorem complexLpIm_ofReal (f : Lp ℝ p μ) :
    complexLpIm μ (complexLpOfReal μ f) = 0 := by
  apply Lp.ext
  filter_upwards [complexLpIm_coe (complexLpOfReal μ f), complexLpOfReal_coe f,
    Lp.coeFn_zero ℝ p μ] with x h₁ h₂ h₀
  rw [h₁, h₂, h₀]; rfl

theorem complexLp_decomposition (f : Lp ℂ p μ) :
    complexLpOfReal μ (complexLpRe μ f) +
      Complex.I • complexLpOfReal μ (complexLpIm μ f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (complexLpOfReal μ (complexLpRe μ f))
      (Complex.I • complexLpOfReal μ (complexLpIm μ f)),
    Lp.coeFn_smul Complex.I (complexLpOfReal μ (complexLpIm μ f)),
    complexLpOfReal_coe (complexLpRe μ f), complexLpOfReal_coe (complexLpIm μ f),
    complexLpRe_coe f, complexLpIm_coe f] with x ha hs hr hi hfr hfi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hs
  rw [ha, hs, hr, hi, hfr, hfi]
  apply Complex.ext <;> simp

theorem complexLp_ext {f g : Lp ℂ p μ}
    (hre : complexLpRe μ f = complexLpRe μ g)
    (him : complexLpIm μ f = complexLpIm μ g) : f = g := by
  rw [← complexLp_decomposition f, hre, him, complexLp_decomposition]

theorem norm_complexLpOfReal (f : Lp ℝ p μ) : ‖complexLpOfReal μ f‖ = ‖f‖ := by
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
  · filter_upwards [complexLpOfReal_coe f] with x hx
    simp [hx]
  · filter_upwards [complexLpOfReal_coe f] with x hx
    simp [hx]

theorem complexLpModulus_nonneg (f : Lp ℂ p μ) : 0 ≤ complexLpModulus f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [complexLpModulus_coe f] with x hx
  rw [hx]
  exact norm_nonneg _

theorem norm_complexLpModulus (f : Lp ℂ p μ) : ‖complexLpModulus f‖ = ‖f‖ := by
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
  · filter_upwards [complexLpModulus_coe f] with x hx
    simp [hx]
  · filter_upwards [complexLpModulus_coe f] with x hx
    simp [hx]

theorem continuous_complexLpModulus :
    Continuous (complexLpModulus : Lp ℂ p μ → Lp ℝ p μ) :=
  lipschitzWith_one_norm.continuous_compLp (norm_zero : ‖(0 : ℂ)‖ = 0)

theorem complexLpModulus_ofReal (f : Lp ℝ p μ) :
    complexLpModulus (complexLpOfReal μ f) = |f| := by
  apply Lp.ext
  filter_upwards [complexLpModulus_coe (complexLpOfReal μ f),
    complexLpOfReal_coe f, Lp.coeFn_abs f] with x hm hr ha
  simp only [hm, hr, ha, Complex.norm_real, Real.norm_eq_abs]

theorem complexLpModulus_add_le (f g : Lp ℂ p μ) :
    complexLpModulus (f + g) ≤ complexLpModulus f + complexLpModulus g := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [complexLpModulus_coe (f+g), complexLpModulus_coe f,
    complexLpModulus_coe g, Lp.coeFn_add f g,
    Lp.coeFn_add (complexLpModulus f) (complexLpModulus g)] with x hfg hf hg ha hb
  simp only [Pi.add_apply] at ha hb
  rw [hfg, ha, hb, hf, hg]
  exact norm_add_le _ _

theorem complexLpRe_smul (c : ℂ) (f : Lp ℂ p μ) :
    complexLpRe μ (c • f) = c.re • complexLpRe μ f - c.im • complexLpIm μ f := by
  apply Lp.ext
  filter_upwards [complexLpRe_coe (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_sub (c.re • complexLpRe μ f) (c.im • complexLpIm μ f),
    Lp.coeFn_smul c.re (complexLpRe μ f), Lp.coeFn_smul c.im (complexLpIm μ f),
    complexLpRe_coe f, complexLpIm_coe f] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at *
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  rfl

theorem complexLpIm_smul (c : ℂ) (f : Lp ℂ p μ) :
    complexLpIm μ (c • f) = c.re • complexLpIm μ f + c.im • complexLpRe μ f := by
  apply Lp.ext
  filter_upwards [complexLpIm_coe (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_add (c.re • complexLpIm μ f) (c.im • complexLpRe μ f),
    Lp.coeFn_smul c.re (complexLpIm μ f), Lp.coeFn_smul c.im (complexLpRe μ f),
    complexLpRe_coe f, complexLpIm_coe f] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at *
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  rfl

theorem complexLpRe_phase_le (f : Lp ℂ p μ) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    complexLpRe μ (c • f) ≤ complexLpModulus f := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [complexLpRe_coe (c • f), Lp.coeFn_smul c f,
    complexLpModulus_coe f] with x hr hs hm
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hr, hs, hm]
  exact ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans (by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc)

/-- Countably many constant phases suffice to recover the pointwise modulus
in the a.e. order. No simultaneous uncountable a.e. choice is used. -/
theorem complexLpModulus_isLUB (f : Lp ℂ p μ) :
    IsLUB {g | ∃ c : ℂ, ‖c‖ = 1 ∧ g = complexLpRe μ (c • f)} (complexLpModulus f) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨c,hc,rfl⟩
    exact complexLpRe_phase_le f c hc.le
  · intro g hg
    letI : SecondCountableTopology {c : ℂ // ‖c‖ = 1} :=
      TopologicalSpace.Subtype.secondCountableTopology {c : ℂ | ‖c‖ = 1}
    obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense {c : ℂ // ‖c‖ = 1}
    have hae : ∀ c ∈ s, ∀ᵐ x ∂μ, ((c : ℂ) * f x).re ≤ g x := by
      intro c hc
      have hle := (Lp.coeFn_le _ _).mpr (hg ⟨c.val,c.property,rfl⟩)
      filter_upwards [hle, complexLpRe_coe (c.val • f), Lp.coeFn_smul c.val f] with x hx hr hm
      simpa only [hr, hm, Pi.smul_apply, smul_eq_mul] using hx
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [(ae_ball_iff hs).mpr hae, complexLpModulus_coe f] with x hx hm
    rw [hm]
    have hall : ∀ c : {c : ℂ // ‖c‖ = 1}, ((c : ℂ) * f x).re ≤ g x := by
      have hclosed : IsClosed {c : {c : ℂ // ‖c‖ = 1} | ((c : ℂ) * f x).re ≤ g x} :=
        isClosed_le (Complex.continuous_re.comp (continuous_subtype_val.mul continuous_const))
          continuous_const
      have hsub := closure_minimal hx hclosed
      rw [hd.closure_eq] at hsub
      exact fun c => hsub (Set.mem_univ c)
    obtain ⟨c,hc,he⟩ := Complex.exists_norm_eq_mul_self (f x)
    have ht := hall ⟨c,hc⟩
    rw [← he] at ht
    exact ht

end ThesisCommon

