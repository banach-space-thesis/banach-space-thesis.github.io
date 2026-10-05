import ThesisCommon.Analysis.ComplexL1Complexification
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! Domination of a complex L1 operator is determined by positive real
inputs. The extension to every complex input uses genuine L1 density. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem complexL1Modulus_smul (c : ℂ) (f : Lp ℂ 1 μ) :
    complexL1Modulus (c • f) = ‖c‖ • complexL1Modulus f := by
  apply Lp.ext
  filter_upwards [complexL1Modulus_coe (c • f), complexL1Modulus_coe f,
    Lp.coeFn_smul c f, Lp.coeFn_smul ‖c‖ (complexL1Modulus f)] with x h₁ h₂ h₃ h₄
  simp only [Pi.smul_apply, smul_eq_mul] at h₃ h₄
  rw [h₁,h₃,h₄,h₂,norm_mul]

theorem complexL1OfReal_indicatorConst {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    complexL1OfReal μ (indicatorConstLp 1 hs hμs (1 : ℝ)) =
      indicatorConstLp 1 hs hμs (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [complexL1OfReal_coe (indicatorConstLp 1 hs hμs (1 : ℝ)),
    (indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := (1 : ℝ))),
    (indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := (1 : ℂ)))] with x h₁ h₂ h₃
  rw [h₁,h₂,h₃]
  by_cases hx : x ∈ s <;> simp [hx]

theorem complexL1_indicatorConst_smul (c : ℂ) {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    indicatorConstLp 1 hs hμs c = c • complexL1OfReal μ (indicatorConstLp 1 hs hμs (1 : ℝ)) := by
  rw [complexL1OfReal_indicatorConst]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (indicatorConstLp 1 hs hμs (1 : ℂ)),
    (indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := c)),
    (indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := (1 : ℂ)))] with x h₁ h₂ h₃
  simp only [Pi.smul_apply, smul_eq_mul] at h₁
  rw [h₁,h₂,h₃]
  by_cases hx : x ∈ s <;> simp [hx]

theorem complexL1Modulus_add_of_disjoint {f g : X → ℂ}
    (hf : MemLp f 1 μ) (hg : MemLp g 1 μ) (hd : Disjoint (Function.support f) (Function.support g)) :
    complexL1Modulus (hf.toLp f + hg.toLp g) =
      complexL1Modulus (hf.toLp f) + complexL1Modulus (hg.toLp g) := by
  apply Lp.ext
  filter_upwards [complexL1Modulus_coe (hf.toLp f + hg.toLp g),
    complexL1Modulus_coe (hf.toLp f), complexL1Modulus_coe (hg.toLp g),
    Lp.coeFn_add (hf.toLp f) (hg.toLp g),
    Lp.coeFn_add (complexL1Modulus (hf.toLp f)) (complexL1Modulus (hg.toLp g)),
    hf.coeFn_toLp, hg.coeFn_toLp] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [Pi.add_apply] at h₄ h₅
  rw [h₁,h₄,h₅,h₂,h₃,h₆,h₇]
  by_cases hx : f x = 0
  · simp [hx]
  · have hy : g x = 0 := by
      by_contra hy
      exact Set.disjoint_left.mp hd hx hy
    simp [hy]

/-- Positive real tests suffice for the sharp pointwise domination of all
complex inputs. No representability or regularity assumption is present. -/
theorem complexL1_domination_of_nonneg (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (R : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hR : ∀ f, 0 ≤ f → complexL1Modulus (T (complexL1OfReal μ f)) ≤ R f)
    (f : Lp ℂ 1 μ) : complexL1Modulus (T f) ≤ R (complexL1Modulus f) := by
  apply Lp.induction (by simp : (1 : ENNReal) ≠ ∞)
    (fun f => complexL1Modulus (T f) ≤ R (complexL1Modulus f)) ?_ ?_ ?_ f
  · intro c s hs hμs
    change complexL1Modulus (T (indicatorConstLp 1 hs hμs.ne c)) ≤
      R (complexL1Modulus (indicatorConstLp 1 hs hμs.ne c))
    let u := indicatorConstLp 1 hs hμs.ne (1 : ℝ)
    have hu : 0 ≤ u := by
      apply (Lp.coeFn_nonneg _).mp
      filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ))] with x hx
      rw [hx]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
    rw [complexL1_indicatorConst_smul c hs hμs.ne, map_smul, complexL1Modulus_smul,
      complexL1Modulus_smul, complexL1Modulus_ofReal, abs_of_nonneg hu, map_smul]
    exact smul_le_smul_of_nonneg_left (hR u hu) (norm_nonneg c)
  · intro f g hf hg hd hTf hTg
    rw [map_add]
    calc
      complexL1Modulus (T (hf.toLp f) + T (hg.toLp g)) ≤
          complexL1Modulus (T (hf.toLp f)) + complexL1Modulus (T (hg.toLp g)) :=
        complexL1Modulus_add_le _ _
      _ ≤ R (complexL1Modulus (hf.toLp f)) + R (complexL1Modulus (hg.toLp g)) := add_le_add hTf hTg
      _ = R (complexL1Modulus (hf.toLp f + hg.toLp g)) := by
        rw [complexL1Modulus_add_of_disjoint hf hg hd,map_add]
  · exact isClosed_le (continuous_complexL1Modulus.comp T.continuous)
      (R.continuous.comp continuous_complexL1Modulus)

end ThesisCommon
