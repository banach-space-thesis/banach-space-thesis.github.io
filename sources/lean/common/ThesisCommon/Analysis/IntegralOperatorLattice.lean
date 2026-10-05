import ThesisCommon.Analysis.L1OperatorLattice
import ThesisCommon.Analysis.IntegralOperatorSigmaFiniteIdeal

/-! The actual integral-operator subspace is a lattice ideal in real
sigma-finite L1 operators. Its finite lattice operations have max/min kernels. -/
noncomputable section
open MeasureTheory Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {k h : X × Y → ℝ} {K H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

theorem IsIntegralKernel.neg (hk : IsIntegralKernel k K) :
    IsIntegralKernel (fun z => -k z) (-K) := by
  simpa only [neg_one_smul, neg_one_mul] using hk.smul (-1)

theorem IsIntegralOperator.neg (hK : IsIntegralOperator K) : IsIntegralOperator (-K) := by
  obtain ⟨k, hk⟩ := hK
  exact ⟨_, hk.neg⟩

variable [SFinite μ] [SFinite ν]

theorem IsIntegralKernel.sup (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H) :
    IsIntegralKernel (fun z => max (k z) (h z)) (K ⊔ H) := by
  have hformula : IsIntegralKernel (fun z => (1 / 2 : ℝ) * (k z + h z + |k z - h z|)) (K ⊔ H) :=
    ((hk.add hh).add (hk.sub hh).modulus).smul (1 / 2)
  apply hformula.congr_ae (hk.measurable.max hh.measurable)
  exact Eventually.of_forall fun z => by
    dsimp only
    by_cases hz : k z ≤ h z
    · rw [max_eq_right hz, abs_of_nonpos (sub_nonpos.mpr hz)]
      ring
    · have hz' : h z ≤ k z := le_of_not_ge hz
      rw [max_eq_left hz', abs_of_nonneg (sub_nonneg.mpr hz')]
      ring

theorem IsIntegralOperator.sup (hK : IsIntegralOperator K) (hH : IsIntegralOperator H) :
    IsIntegralOperator (K ⊔ H) := by
  obtain ⟨k, hk⟩ := hK
  obtain ⟨h, hh⟩ := hH
  exact ⟨_, hk.sup hh⟩

theorem IsIntegralKernel.inf (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H) :
    IsIntegralKernel (fun z => min (k z) (h z)) (K ⊓ H) := by
  have hformula : IsIntegralKernel (fun z => -max (-k z) (-h z)) (K ⊓ H) :=
    (hk.neg.sup hh.neg).neg
  apply hformula.congr_ae (hk.measurable.min hh.measurable)
  exact Eventually.of_forall fun z => by
    dsimp only
    by_cases hz : k z ≤ h z
    · rw [min_eq_left hz, max_eq_left (neg_le_neg hz), neg_neg]
    · have hz' : h z ≤ k z := le_of_not_ge hz
      rw [min_eq_right hz', max_eq_right (neg_le_neg hz'), neg_neg]

theorem IsIntegralOperator.inf (hK : IsIntegralOperator K) (hH : IsIntegralOperator H) :
    IsIntegralOperator (K ⊓ H) := by
  obtain ⟨k, hk⟩ := hK
  obtain ⟨h, hh⟩ := hH
  exact ⟨_, hk.inf hh⟩

omit [SFinite ν] in
theorem IsIntegralOperator.abs (hK : IsIntegralOperator K) : IsIntegralOperator |K| := by
  obtain ⟨k, hk⟩ := hK
  rw [abs_lOneOperator_eq]
  exact ⟨_, hk.modulus⟩

omit [SFinite μ] [SFinite ν] in
theorem integralOperatorSubmodule_solid [SigmaFinite μ] [SigmaFinite ν]
    {S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hK : K ∈ integralOperatorSubmodule μ ν)
    (hSK : |S| ≤ |K|) : S ∈ integralOperatorSubmodule μ ν := by
  apply IsIntegralOperator.of_modulus_le_sigmaFinite hK
  rw [← abs_lOneOperator_eq, ← abs_lOneOperator_eq]
  exact hSK

end ThesisCommon
