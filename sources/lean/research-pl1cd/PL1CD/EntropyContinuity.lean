import PL1CD.BoundedEntropy
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace PL1CD.Entropy

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem Phi_tendsto_of_bounded_L1 (f : ℕ → Lp ℝ 1 μ) (g : Lp ℝ 1 μ)
    (C : ℝ) (hbound : ∀ n, ∀ᵐ x ∂μ, f n x ∈ Set.Icc 0 C)
    (hfg : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => Phi μ (f n)) atTop (𝓝 (Phi μ g)) := by
  have hphi : Continuous phi := Real.continuous_mul_log
  obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) C)).image hphi).isBounded.exists_norm_le
  by_contra hnot
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hnot
  obtain ⟨u, hu, hbad⟩ := extraction_of_frequently_atTop hfreq
  have him : TendstoInMeasure μ (fun n => f (u n)) atTop g :=
    tendstoInMeasure_of_tendsto_Lp (hfg.comp hu.tendsto_atTop)
  obtain ⟨v, _, hae⟩ := him.exists_seq_tendsto_ae
  have hlimit : ∀ᵐ x ∂μ, Tendsto (fun n => phi (f (u (v n)) x)) atTop (𝓝 (phi (g x))) := by
    filter_upwards [hae] with x hx
    exact (hphi.tendsto (g x)).comp hx
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Ω => B)
    (fun n => hphi.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (f (u (v n)))))
    (integrable_const B)
    (fun n => (hbound (u (v n))).mono (fun x hx => hB _ ⟨f (u (v n)) x, hx, rfl⟩)) hlimit
  change Tendsto (fun n => Phi μ (f (u (v n)))) atTop (𝓝 (Phi μ g)) at ht
  obtain ⟨n, hn⟩ := (ht.eventually_mem hs).exists
  exact hbad (v n) hn

end PL1CD.Entropy
