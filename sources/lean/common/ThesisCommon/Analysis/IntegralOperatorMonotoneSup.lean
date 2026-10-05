import ThesisCommon.Analysis.IntegralKernelMonotoneLimit
import ThesisCommon.Analysis.IntegralKernelSigmaFiniteBound
import ThesisCommon.Analysis.IntegralKernelSigmaFiniteOrder
import ThesisCommon.Analysis.L1OperatorCountableSup

/-! Increasing positive integral operators have integral operator suprema.
The proof constructs a genuine finite almost-everywhere kernel and uses
monotone convergence on every positive L1 input. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SFinite ν]

theorem exists_integral_kernel_of_monotone_sup
    (K : ℕ → (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)) (k : ℕ → X × Y → ℝ)
    (hk : ∀ n, IsIntegralKernel (k n) (K n)) (hpos : ∀ n, 0 ≤ K n) (hmono : Monotone K)
    {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : IsLUB (range K) S) :
    ∃ r : X × Y → ℝ, IsIntegralKernel r S ∧ (∀ z, 0 ≤ r z) ∧
      ∀ᵐ z ∂μ.prod ν, (∀ n, k n z ≤ r z) ∧
        Tendsto (fun n => k n z) atTop (𝓝 (r z)) := by
  have hKS : ∀ n, K n ≤ S := fun n => hS.1 ⟨n, rfl⟩
  have hSpos : 0 ≤ S := (hpos 0).trans (hKS 0)
  have hkpos : ∀ n, ∀ᵐ z ∂μ.prod ν, 0 ≤ k n z :=
    fun n => (hk n).nonneg_ae_of_positive_sigmaFinite (hpos n)
  have hkmono : ∀ n, k n ≤ᵐ[μ.prod ν] k (n + 1) := fun n =>
    ((hk n).le_iff_kernel_le_sigmaFinite (hk (n + 1))).mp (hmono (Nat.le_succ n))
  have hbounds : ∀ n, HasKernelBound μ ν (k n) ‖S‖ := by
    intro n
    apply (hk n).hasKernelBound_sigmaFinite.mono_const
    apply norm_le_norm_of_abs_le_abs
    simpa only [abs_of_nonneg (hpos n), abs_of_nonneg hSpos] using hKS n
  obtain ⟨r, hrm, hrpos, hrbound, hrlimit⟩ := exists_monotone_kernel_limit k
    (fun n => (hk n).measurable) hkpos hkmono (norm_nonneg S) hbounds
  let H := integralKernelOperator hrm hrbound
  have hH : IsIntegralKernel r H := isIntegralKernel_integralKernelOperator hrm hrbound
  have hKH : ∀ n, K n ≤ H := fun n =>
    ((hk n).le_iff_kernel_le_sigmaFinite hH).mpr (hrlimit.mono fun _ hz => hz.1 n)
  have hSH : S ≤ H := hS.2 (by rintro _ ⟨n, rfl⟩; exact hKH n)
  have hHS : H ≤ S := by
    intro f hf
    have hlimsections := Measure.ae_ae_of_ae_prod
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hrlimit)
    have hmonsections := Measure.ae_ae_of_ae_prod
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (ae_all_iff.mpr hkmono))
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hH.represents f, hH.integrable_section f,
      ae_all_iff.mpr (fun n => (hk n).integrable_section f),
      ae_all_iff.mpr (fun n => (hk n).represents f),
      ae_all_iff.mpr (fun n => (Lp.coeFn_le _ _).mpr (hKS n f hf)),
      hlimsections, hmonsections] with y hHy hri hki hky hle hlim hmon
    rw [hHy]
    have hm : ∀ᵐ x ∂μ, Monotone (fun n => k n (x, y) * f x) := by
      filter_upwards [hmon, (Lp.coeFn_nonneg f).mpr hf] with x hx hfx
      exact monotone_nat_of_le_succ fun n => mul_le_mul_of_nonneg_right (hx n) hfx
    have ht : ∀ᵐ x ∂μ, Tendsto (fun n => k n (x, y) * f x) atTop (𝓝 (r (x, y) * f x)) :=
      hlim.mono fun x hx => hx.2.mul_const (f x)
    apply le_of_tendsto' (integral_tendsto_of_tendsto_of_monotone hki hri hm ht)
    intro n
    rw [← hky n]
    exact hle n
  have heq : H = S := le_antisymm hHS hSH
  exact ⟨r, heq ▸ hH, hrpos, hrlimit⟩

theorem IsIntegralOperator.of_monotone_sup
    {K : ℕ → (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)} (hK : ∀ n, IsIntegralOperator (K n))
    (hpos : ∀ n, 0 ≤ K n) (hmono : Monotone K)
    {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : IsLUB (range K) S) : IsIntegralOperator S := by
  choose k hk using hK
  obtain ⟨r, hr, _⟩ := exists_integral_kernel_of_monotone_sup K k hk hpos hmono hS
  exact ⟨r, hr⟩

omit [SigmaFinite μ] in
theorem IsIntegralOperator.of_directed_sup [IsFiniteMeasure μ]
    {s : Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)} (hs : s.Nonempty)
    (hI : ∀ T ∈ s, IsIntegralOperator T) (hpos : ∀ T ∈ s, 0 ≤ T)
    (hdir : DirectedOn (· ≤ ·) s) {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : IsLUB s S) :
    IsIntegralOperator S := by
  obtain ⟨v, hvm, hvs, hvS⟩ := lOneOperator_directed_countable_sup hs hpos hdir hS
  exact IsIntegralOperator.of_monotone_sup (fun n => hI _ (hvs n))
    (fun n => hpos _ (hvs n)) hvm hvS

end ThesisCommon
