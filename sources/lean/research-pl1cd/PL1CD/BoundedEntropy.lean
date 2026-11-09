import PL1CD.EntropyGap
import PL1CD.IntegralCauchySchwarz
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace PL1CD.Entropy

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integrable_continuous_comp_bounded (f : Ω → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ x, f x ∈ Set.Icc 0 C)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) : Integrable (fun x => ψ (f x)) μ := by
  obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) C)).image hψ).isBounded.exists_norm_le
  apply (MemLp.of_bound (p := 1) (hψ.measurable.comp hf).aestronglyMeasurable B
    (Eventually.of_forall (fun x => hB _ ⟨f x, hbound x, rfl⟩))).integrable (by norm_num)

theorem integrable_continuous_pair_bounded (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (C D : ℝ)
    (hboundf : ∀ x, f x ∈ Set.Icc 0 C) (hboundg : ∀ x, g x ∈ Set.Icc 0 D)
    (ψ : ℝ × ℝ → ℝ) (hψ : Continuous ψ) :
    Integrable (fun x => ψ (f x, g x)) μ := by
  obtain ⟨B, hB⟩ := (((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) C)).prod
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) D))).image hψ).isBounded.exists_norm_le
  apply (MemLp.of_bound (p := 1) (hψ.measurable.comp (hf.prodMk hg)).aestronglyMeasurable B
    (Eventually.of_forall (fun x => hB _ ⟨(f x, g x), ⟨hboundf x, hboundg x⟩, rfl⟩))).integrable
    (by norm_num)

def Phi (f : Ω → ℝ) : ℝ := ∫ x, phi (f x) ∂μ

theorem integral_hellinger_ge_l1_sq (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (C D : ℝ)
    (hboundf : ∀ x, f x ∈ Set.Icc 0 C) (hboundg : ∀ x, g x ∈ Set.Icc 0 D)
    (hmassf : ∫ x, f x ∂μ ≤ 1) (hmassg : ∫ x, g x ∂μ ≤ 1) :
    (∫ x, |f x - g x| ∂μ) ^ 2 ≤ 4 * ∫ x, (Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 ∂μ := by
  let u (x : Ω) := |Real.sqrt (f x) - Real.sqrt (g x)|
  let v (x : Ω) := Real.sqrt (f x) + Real.sqrt (g x)
  have hu : Integrable (fun x => u x ^ 2) μ := by
    apply integrable_continuous_pair_bounded μ f g hf hg C D hboundf hboundg
      (fun z => |Real.sqrt z.1 - Real.sqrt z.2| ^ 2)
    exact ((Real.continuous_sqrt.comp continuous_fst).sub
      (Real.continuous_sqrt.comp continuous_snd)).abs.pow 2
  have hv : Integrable (fun x => v x ^ 2) μ := by
    apply integrable_continuous_pair_bounded μ f g hf hg C D hboundf hboundg
      (fun z => (Real.sqrt z.1 + Real.sqrt z.2) ^ 2)
    exact ((Real.continuous_sqrt.comp continuous_fst).add
      (Real.continuous_sqrt.comp continuous_snd)).pow 2
  have huv : Integrable (fun x => u x * v x) μ := by
    apply integrable_continuous_pair_bounded μ f g hf hg C D hboundf hboundg
      (fun z => |Real.sqrt z.1 - Real.sqrt z.2| * (Real.sqrt z.1 + Real.sqrt z.2))
    exact (((Real.continuous_sqrt.comp continuous_fst).sub
      (Real.continuous_sqrt.comp continuous_snd)).abs).mul
      ((Real.continuous_sqrt.comp continuous_fst).add
        (Real.continuous_sqrt.comp continuous_snd))
  have hfg : (fun x => u x * v x) = fun x => |f x - g x| := by
    funext x
    dsimp [u, v]
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (hboundf x).1, Real.sq_sqrt (hboundg x).1]
  have hif := integrable_continuous_comp_bounded μ f hf C hboundf id continuous_id
  have hig := integrable_continuous_comp_bounded μ g hg D hboundg id continuous_id
  change Integrable f μ at hif
  change Integrable g μ at hig
  have hmass : (∫ x, v x ^ 2 ∂μ) ≤ 4 := by
    calc
      _ ≤ ∫ x, 2 * f x + 2 * g x ∂μ := by
        apply integral_mono hv ((hif.const_mul 2).add (hig.const_mul 2))
        intro x
        dsimp [v]
        nlinarith [Real.sq_sqrt (hboundf x).1, Real.sq_sqrt (hboundg x).1,
          sq_nonneg (Real.sqrt (f x) - Real.sqrt (g x))]
      _ = 2 * (∫ x, f x ∂μ) + 2 * ∫ x, g x ∂μ := by
        rw [integral_add (hif.const_mul (2 : ℝ)) (hig.const_mul (2 : ℝ)),
          integral_const_mul, integral_const_mul]
      _ ≤ 4 := by linarith
  have hcs := integral_mul_sq_le μ u v hu hv huv
  rw [hfg] at hcs
  have hu_eq : (fun x => u x ^ 2) =
      fun x => (Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 := by
    funext x
    exact sq_abs _
  rw [hu_eq] at hcs
  exact hcs.trans (by
    have hi : 0 ≤ ∫ x, (Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg _)
    nlinarith)

theorem averaged_Phi_gap {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → Ω → ℝ) (g : Ω → ℝ) (hf : ∀ i, Measurable (f i)) (hg : Measurable g)
    (C : ℝ) (hboundf : ∀ i x, f i x ∈ Set.Icc 0 C)
    (hboundg : ∀ x, g x ∈ Set.Icc 0 C)
    (hmean : ∀ x, ∑ i, f i x = (Fintype.card ι : ℝ) * g x)
    (hmassf : ∀ i, ∫ x, f i x ∂μ ≤ 1) (hmassg : ∫ x, g x ∂μ ≤ 1) :
    (Fintype.card ι : ℝ)⁻¹ * (∑ i, Phi μ (f i)) - Phi μ g ≥
      (4 * (Fintype.card ι : ℝ))⁻¹ * ∑ i, (∫ x, |f i x - g x| ∂μ) ^ 2 := by
  classical
  have hphi (i : ι) : Integrable (fun x => phi (f i x)) μ :=
    integrable_continuous_comp_bounded μ (f i) (hf i) C (hboundf i)
      phi Real.continuous_mul_log
  have hphig : Integrable (fun x => phi (g x)) μ :=
    integrable_continuous_comp_bounded μ g hg C hboundg phi Real.continuous_mul_log
  have hroot (i : ι) : Integrable (fun x => (Real.sqrt (f i x) - Real.sqrt (g x)) ^ 2) μ := by
    apply integrable_continuous_pair_bounded μ (f i) g (hf i) hg C C (hboundf i) hboundg
      (fun z => (Real.sqrt z.1 - Real.sqrt z.2) ^ 2)
    exact ((Real.continuous_sqrt.comp continuous_fst).sub
      (Real.continuous_sqrt.comp continuous_snd)).pow 2
  have hpoint := integral_mono
    ((integrable_finsetSum Finset.univ (fun i _ => hroot i)).const_mul (Fintype.card ι : ℝ)⁻¹)
    (((integrable_finsetSum Finset.univ (fun i _ => hphi i)).const_mul
      (Fintype.card ι : ℝ)⁻¹).sub hphig)
    (fun x => average_hellinger_le_phi_gap (fun i => f i x)
      (fun i => (hboundf i x).1) (g x) (hmean x))
  simp only [Pi.sub_apply] at hpoint
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hroot i),
    integral_sub ((integrable_finsetSum Finset.univ (fun i _ => hphi i)).const_mul
      (Fintype.card ι : ℝ)⁻¹) hphig,
    integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hphi i)] at hpoint
  have hl1 : ∑ i, (∫ x, |f i x - g x| ∂μ) ^ 2 ≤
      4 * ∑ i, ∫ x, (Real.sqrt (f i x) - Real.sqrt (g x)) ^ 2 ∂μ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => integral_hellinger_ge_l1_sq μ (f i) g
      (hf i) hg C C (hboundf i) hboundg (hmassf i) hmassg)
  have hscaled := mul_le_mul_of_nonneg_left hl1
    (show 0 ≤ (4 * (Fintype.card ι : ℝ))⁻¹ by positivity)
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have halgebra : (4 * (Fintype.card ι : ℝ))⁻¹ * (4 *
      ∑ i, ∫ x, (Real.sqrt (f i x) - Real.sqrt (g x)) ^ 2 ∂μ) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ x, (Real.sqrt (f i x) - Real.sqrt (g x)) ^ 2 ∂μ := by
    field_simp
  rw [halgebra] at hscaled
  exact hscaled.trans hpoint

end PL1CD.Entropy
