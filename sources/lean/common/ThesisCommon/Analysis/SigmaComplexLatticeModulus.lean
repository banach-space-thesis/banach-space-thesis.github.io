import ThesisCommon.Analysis.BanachLattice
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Module.Basic
import Mathlib.Tactic.Module

/-! Intrinsic complex lattice modulus and preservation by real lattice
homomorphisms. The modulus is specified by its least-upper-bound definition;
no representation by function spaces is assumed. -/
noncomputable section
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

def complexLatticePhase (x y : E) (c : ℂ) : E := c.re • x - c.im • y

def IsComplexLatticeModulus (x y m : E) : Prop :=
  IsLUB {v | ∃ c : ℂ, ‖c‖ ≤ 1 ∧ v = complexLatticePhase x y c} m

theorem complexLatticePhase_scalar_le (a b : ℝ) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    c.re*a-c.im*b ≤ ‖(⟨a,b⟩ : ℂ)‖ := by
  have h := (le_abs_self (c * (⟨a,b⟩ : ℂ)).re).trans (Complex.abs_re_le_norm _)
  change c.re*a-c.im*b ≤ _ at h
  exact h.trans (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hc)

theorem complexLatticePhase_scalar_attains (a b : ℝ) :
    ∃ c : ℂ, ‖c‖ ≤ 1 ∧ c.re*a-c.im*b = ‖(⟨a,b⟩ : ℂ)‖ := by
  obtain ⟨c,hc,he⟩ := Complex.exists_norm_eq_mul_self (⟨a,b⟩ : ℂ)
  refine ⟨c,hc.le,?_⟩
  exact (congrArg Complex.re he).symm

theorem real_smul_le_abs_of_abs_le_one (x : E) (r : ℝ) (hr : |r| ≤ 1) :
    r • x ≤ |x| := by
  have hp (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (z : E) : a • z ≤ |z| := by
    calc
      a • z ≤ a • |z| := smul_le_smul_of_nonneg_left (le_abs_self _) ha
      _ ≤ 1 • |z| := smul_le_smul_of_nonneg_right ha1 (abs_nonneg _)
      _ = |z| := one_smul _ _
  by_cases h : 0 ≤ r
  · exact hp r h ((le_abs_self _).trans hr) x
  · have hn : 0 ≤ -r := neg_nonneg.mpr (le_of_not_ge h)
    have ht := hp (-r) hn ((neg_le_abs _).trans hr) (-x)
    simpa only [neg_smul,smul_neg,neg_neg,abs_neg] using ht

theorem complexLatticePhase_le_abs_add (x y : E) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    complexLatticePhase x y c ≤ |x|+|y| := by
  rw [complexLatticePhase,sub_eq_add_neg,← neg_smul]
  exact add_le_add (real_smul_le_abs_of_abs_le_one x c.re ((Complex.abs_re_le_norm _).trans hc))
    (real_smul_le_abs_of_abs_le_one y (-c.im) (by simpa using (Complex.abs_im_le_norm c).trans hc))

theorem IsComplexLatticeModulus.phase_le {x y m : E}
    (h : IsComplexLatticeModulus x y m) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    complexLatticePhase x y c ≤ m := h.1 ⟨c,hc,rfl⟩

theorem IsComplexLatticeModulus.le_abs_add {x y m : E}
    (h : IsComplexLatticeModulus x y m) : m ≤ |x|+|y| := by
  apply h.2
  rintro _ ⟨c,hc,rfl⟩
  exact complexLatticePhase_le_abs_add x y c hc

theorem IsComplexLatticeModulus.nonneg {x y m : E}
    (h : IsComplexLatticeModulus x y m) : 0 ≤ m := by
  simpa [complexLatticePhase] using h.phase_le 0 (by simp)

theorem IsComplexLatticeModulus.abs_fst_le {x y m : E}
    (h : IsComplexLatticeModulus x y m) : |x| ≤ m := by
  apply sup_le
  · simpa [complexLatticePhase] using h.phase_le 1 (by simp)
  · simpa [complexLatticePhase] using h.phase_le (-1) (by simp)

theorem IsComplexLatticeModulus.abs_snd_le {x y m : E}
    (h : IsComplexLatticeModulus x y m) : |y| ≤ m := by
  apply sup_le
  · simpa [complexLatticePhase] using h.phase_le (-Complex.I) (by simp)
  · simpa [complexLatticePhase] using h.phase_le Complex.I (by simp)

theorem complexLatticeHom_monotone (φ : E →L[ℝ] ℝ)
    (hφ : ∀ x, φ |x| = |φ x|) : Monotone φ := by
  intro x y hxy
  have h := abs_nonneg (φ (y-x))
  rw [← hφ, abs_of_nonneg (sub_nonneg.mpr hxy), map_sub] at h
  exact sub_nonneg.mp h

/-- Complexification of an arbitrary bounded real lattice homomorphism
preserves the intrinsic complex modulus. -/
theorem IsComplexLatticeModulus.map_latticeHom {x y m : E}
    (h : IsComplexLatticeModulus x y m) (φ : E →L[ℝ] ℝ)
    (hφ : ∀ z, φ |z| = |φ z|) :
    φ m = ‖(⟨φ x,φ y⟩ : ℂ)‖ := by
  have hmono := complexLatticeHom_monotone φ hφ
  apply le_antisymm
  · by_cases hz : φ = 0
    · simp [hz]
    have hv : ∃ v : E, φ v ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hz (ContinuousLinearMap.ext hn)
    obtain ⟨v,hv⟩ := hv
    let u : E := |φ v|⁻¹ • |v|
    have hu : 0 ≤ u := smul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (abs_nonneg _)
    have hφu : φ u = 1 := by
      simp only [u,map_smul,smul_eq_mul,hφ]
      exact inv_mul_cancel₀ (abs_ne_zero.mpr hv)
    have hmajor : m ≤ ‖(⟨φ x,φ y⟩ : ℂ)‖ • u +
        (|x-(φ x) • u|+|y-(φ y) • u|) := by
      apply h.2
      rintro _ ⟨c,hc,rfl⟩
      calc
        complexLatticePhase x y c =
            (c.re * φ x-c.im * φ y) • u +
              complexLatticePhase (x-(φ x) • u) (y-(φ y) • u) c := by
                unfold complexLatticePhase
                module
        _ ≤ ‖(⟨φ x,φ y⟩ : ℂ)‖ • u + (|x-(φ x) • u|+|y-(φ y) • u|) :=
          add_le_add (smul_le_smul_of_nonneg_right (complexLatticePhase_scalar_le _ _ c hc) hu)
            (complexLatticePhase_le_abs_add _ _ c hc)
    have ht := hmono hmajor
    simpa only [map_add,map_smul,smul_eq_mul,hφ,hφu,map_sub,mul_one,sub_self,
      abs_zero,add_zero] using ht
  · obtain ⟨c,hc,he⟩ := complexLatticePhase_scalar_attains (φ x) (φ y)
    have ht := hmono (h.phase_le c hc)
    simpa only [complexLatticePhase,map_sub,map_smul,smul_eq_mul,he] using ht

end ThesisCommon

