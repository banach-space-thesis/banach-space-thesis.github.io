import ThesisCommon.Analysis.L1Lattice
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Sequences

/-! Actual real coordinates and pointwise modulus of complex L1. All maps
act on the genuine a.e. equivalence classes, for an arbitrary measure. -/
noncomputable section
open MeasureTheory Filter Set
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def complexL1Re (μ : Measure X) : Lp ℂ 1 μ →L[ℝ] Lp ℝ 1 μ :=
  Complex.reCLM.compLpL 1 μ

def complexL1Im (μ : Measure X) : Lp ℂ 1 μ →L[ℝ] Lp ℝ 1 μ :=
  Complex.imCLM.compLpL 1 μ

def complexL1OfReal (μ : Measure X) : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 μ :=
  Complex.ofRealCLM.compLpL 1 μ

def complexL1Modulus (f : Lp ℂ 1 μ) : Lp ℝ 1 μ :=
  lipschitzWith_one_norm.compLp (norm_zero : ‖(0 : ℂ)‖ = 0) f

theorem complexL1Re_coe (f : Lp ℂ 1 μ) :
    complexL1Re μ f =ᵐ[μ] fun x => (f x).re := Complex.reCLM.coeFn_compLpL f

theorem complexL1Im_coe (f : Lp ℂ 1 μ) :
    complexL1Im μ f =ᵐ[μ] fun x => (f x).im := Complex.imCLM.coeFn_compLpL f

theorem complexL1OfReal_coe (f : Lp ℝ 1 μ) :
    complexL1OfReal μ f =ᵐ[μ] fun x => (f x : ℂ) := Complex.ofRealCLM.coeFn_compLpL f

theorem complexL1Modulus_coe (f : Lp ℂ 1 μ) :
    complexL1Modulus f =ᵐ[μ] fun x => ‖f x‖ :=
  lipschitzWith_one_norm.coeFn_compLp _ f

@[simp] theorem complexL1Re_ofReal (f : Lp ℝ 1 μ) :
    complexL1Re μ (complexL1OfReal μ f) = f := by
  apply Lp.ext
  filter_upwards [complexL1Re_coe (complexL1OfReal μ f), complexL1OfReal_coe f] with x h₁ h₂
  simp [h₁, h₂]

@[simp] theorem complexL1Im_ofReal (f : Lp ℝ 1 μ) :
    complexL1Im μ (complexL1OfReal μ f) = 0 := by
  apply Lp.ext
  filter_upwards [complexL1Im_coe (complexL1OfReal μ f), complexL1OfReal_coe f,
    Lp.coeFn_zero ℝ 1 μ] with x h₁ h₂ h₀
  rw [h₁, h₂, h₀]; rfl

theorem complexL1_decomposition (f : Lp ℂ 1 μ) :
    complexL1OfReal μ (complexL1Re μ f) +
      Complex.I • complexL1OfReal μ (complexL1Im μ f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (complexL1OfReal μ (complexL1Re μ f))
      (Complex.I • complexL1OfReal μ (complexL1Im μ f)),
    Lp.coeFn_smul Complex.I (complexL1OfReal μ (complexL1Im μ f)),
    complexL1OfReal_coe (complexL1Re μ f), complexL1OfReal_coe (complexL1Im μ f),
    complexL1Re_coe f, complexL1Im_coe f] with x ha hs hr hi hfr hfi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hs
  rw [ha, hs, hr, hi, hfr, hfi]
  apply Complex.ext <;> simp

theorem complexL1_ext {f g : Lp ℂ 1 μ}
    (hre : complexL1Re μ f = complexL1Re μ g)
    (him : complexL1Im μ f = complexL1Im μ g) : f = g := by
  rw [← complexL1_decomposition f, hre, him, complexL1_decomposition]

theorem norm_complexL1OfReal (f : Lp ℝ 1 μ) : ‖complexL1OfReal μ f‖ = ‖f‖ := by
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
  · filter_upwards [complexL1OfReal_coe f] with x hx
    simp [hx]
  · filter_upwards [complexL1OfReal_coe f] with x hx
    simp [hx]

theorem complexL1Modulus_nonneg (f : Lp ℂ 1 μ) : 0 ≤ complexL1Modulus f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [complexL1Modulus_coe f] with x hx
  rw [hx]
  exact norm_nonneg _

theorem norm_complexL1Modulus (f : Lp ℂ 1 μ) : ‖complexL1Modulus f‖ = ‖f‖ := by
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
  · filter_upwards [complexL1Modulus_coe f] with x hx
    simp [hx]
  · filter_upwards [complexL1Modulus_coe f] with x hx
    simp [hx]

theorem continuous_complexL1Modulus :
    Continuous (complexL1Modulus : Lp ℂ 1 μ → Lp ℝ 1 μ) :=
  lipschitzWith_one_norm.continuous_compLp (norm_zero : ‖(0 : ℂ)‖ = 0)

theorem complexL1Modulus_ofReal (f : Lp ℝ 1 μ) :
    complexL1Modulus (complexL1OfReal μ f) = |f| := by
  apply Lp.ext
  filter_upwards [complexL1Modulus_coe (complexL1OfReal μ f),
    complexL1OfReal_coe f, Lp.coeFn_abs f] with x hm hr ha
  simp only [hm, hr, ha, Complex.norm_real, Real.norm_eq_abs]

theorem complexL1Modulus_add_le (f g : Lp ℂ 1 μ) :
    complexL1Modulus (f + g) ≤ complexL1Modulus f + complexL1Modulus g := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [complexL1Modulus_coe (f+g), complexL1Modulus_coe f,
    complexL1Modulus_coe g, Lp.coeFn_add f g,
    Lp.coeFn_add (complexL1Modulus f) (complexL1Modulus g)] with x hfg hf hg ha hb
  simp only [Pi.add_apply] at ha hb
  rw [hfg, ha, hb, hf, hg]
  exact norm_add_le _ _

theorem complexL1Re_smul (c : ℂ) (f : Lp ℂ 1 μ) :
    complexL1Re μ (c • f) = c.re • complexL1Re μ f - c.im • complexL1Im μ f := by
  apply Lp.ext
  filter_upwards [complexL1Re_coe (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_sub (c.re • complexL1Re μ f) (c.im • complexL1Im μ f),
    Lp.coeFn_smul c.re (complexL1Re μ f), Lp.coeFn_smul c.im (complexL1Im μ f),
    complexL1Re_coe f, complexL1Im_coe f] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at *
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  rfl

theorem complexL1Im_smul (c : ℂ) (f : Lp ℂ 1 μ) :
    complexL1Im μ (c • f) = c.re • complexL1Im μ f + c.im • complexL1Re μ f := by
  apply Lp.ext
  filter_upwards [complexL1Im_coe (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_add (c.re • complexL1Im μ f) (c.im • complexL1Re μ f),
    Lp.coeFn_smul c.re (complexL1Im μ f), Lp.coeFn_smul c.im (complexL1Re μ f),
    complexL1Re_coe f, complexL1Im_coe f] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at *
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  rfl

theorem complexL1Re_phase_le (f : Lp ℂ 1 μ) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    complexL1Re μ (c • f) ≤ complexL1Modulus f := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [complexL1Re_coe (c • f), Lp.coeFn_smul c f,
    complexL1Modulus_coe f] with x hr hs hm
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hr, hs, hm]
  exact ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans (by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc)

/-- Countably many constant phases suffice to recover the pointwise modulus
in the a.e. order. No simultaneous uncountable a.e. choice is used. -/
theorem complexL1Modulus_isLUB (f : Lp ℂ 1 μ) :
    IsLUB {g | ∃ c : ℂ, ‖c‖ = 1 ∧ g = complexL1Re μ (c • f)} (complexL1Modulus f) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨c,hc,rfl⟩
    exact complexL1Re_phase_le f c hc.le
  · intro g hg
    letI : SecondCountableTopology {c : ℂ // ‖c‖ = 1} :=
      TopologicalSpace.Subtype.secondCountableTopology {c : ℂ | ‖c‖ = 1}
    obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense {c : ℂ // ‖c‖ = 1}
    have hae : ∀ c ∈ s, ∀ᵐ x ∂μ, ((c : ℂ) * f x).re ≤ g x := by
      intro c hc
      have hle := (Lp.coeFn_le _ _).mpr (hg ⟨c.val,c.property,rfl⟩)
      filter_upwards [hle, complexL1Re_coe (c.val • f), Lp.coeFn_smul c.val f] with x hx hr hm
      simpa only [hr, hm, Pi.smul_apply, smul_eq_mul] using hx
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [(ae_ball_iff hs).mpr hae, complexL1Modulus_coe f] with x hx hm
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

