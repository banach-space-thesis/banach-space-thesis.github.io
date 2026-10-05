import ThesisCommon.Analysis.IntegralOperatorSigmaFiniteIdeal
import ThesisCommon.Analysis.IntegralKernelSigmaFiniteOrder
import ThesisCommon.Analysis.IntegralOperatorLattice
import ThesisCommon.Analysis.L1OperatorCountableSup
import ThesisCommon.Analysis.IntegralOperatorBand
import ThesisCommon.Analysis.IntegralSingularModulus
import ThesisCommon.Analysis.BandOrderConvergence
import ThesisCommon.Analysis.BandProjectionModulus

/-! The real sigma-finite integral band and its constructed projection,
including the real statement of Theorem 3.15 and the unique decomposition. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

/-- Abramovich--Aliprantis Theorem 5.9, the finite-input positive ideal
step used in the background to the paper's Theorem 3.15. The kernel is
constructed from the dominated content, then identified on all L1 inputs. -/
theorem integral_positive_ideal_finite_input [IsFiniteMeasure μ] [SigmaFinite ν]
    {K S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} {k : X × Y → ℝ}
    (hk : IsIntegralKernel k K) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) :
    ∃ r : X × Y → ℝ, IsIntegralKernel r S ∧ (∀ z, 0 ≤ r z) ∧ r ≤ᵐ[μ.prod ν] k :=
  hk.exists_kernel_of_positive_le S hS hSK

/-- Signed solidity of the actual integral-operator subspace, for finite
input and sigma-finite output. The modulus is the previously constructed
bounded operator on the genuine real L1 spaces. -/
theorem integral_solid_finite_input [IsFiniteMeasure μ] [SigmaFinite ν]
    {K S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hK : IsIntegralOperator K)
    (hSK : ∀ f, 0 ≤ f → lOneOperatorModulus S f ≤ lOneOperatorModulus K f) :
    IsIntegralOperator S := hK.of_modulus_le hSK

/-- The real sigma-finite positive ideal theorem. The input measure change
is implemented by a proved surjective weighted L1 isometry. -/
theorem integral_positive_ideal [SigmaFinite μ] [SigmaFinite ν]
    {K S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} {k : X × Y → ℝ}
    (hk : IsIntegralKernel k K) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) :
    ∃ r : X × Y → ℝ, IsIntegralKernel r S ∧ (∀ z, 0 ≤ r z) ∧ r ≤ᵐ[μ.prod ν] k :=
  hk.exists_kernel_of_positive_le_sigmaFinite S hS hSK

/-- The real integral operators form a solid linear subspace in the full
sigma-finite scope used in Theorem 3.15. This is its ideal part only. -/
theorem integral_operator_solid [SigmaFinite μ] [SigmaFinite ν]
    {K S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hK : IsIntegralOperator K)
    (hSK : ∀ f, 0 ≤ f → lOneOperatorModulus S f ≤ lOneOperatorModulus K f) :
    IsIntegralOperator S := hK.of_modulus_le_sigmaFinite hSK

theorem integral_operator_le_iff_kernel_le_sigmaFinite [SigmaFinite μ] [SFinite ν]
    {K H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} {k h : X × Y → ℝ}
    (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H) :
    (∀ f, 0 ≤ f → K f ≤ H f) ↔ k ≤ᵐ[μ.prod ν] h := hk.le_iff_kernel_le_sigmaFinite hh

open scoped ThesisCommon.PositiveOperatorOrder

/-- The ambient Dedekind completeness used in Theorem 3.15, for the
actual positive-cone order on bounded real L1 operators. -/
theorem real_lOne_operator_dedekind_complete
    {s : Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)} (hs : s.Nonempty) (hbdd : BddAbove s) :
    ∃ T, IsLUB s T := lOneOperator_exists_isLUB hs hbdd

/-- The sequence selection in the proof of book Theorem 5.14, in the
finite-input reduction. Equality at one detects comparable operators,
so the sequence has the same operator supremum on every input. -/
theorem integral_band_countable_sequence_step [IsFiniteMeasure μ]
    {s : Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)} (hs : s.Nonempty) (hpos : ∀ T ∈ s, 0 ≤ T)
    (hdir : DirectedOn (· ≤ ·) s) {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : IsLUB s S) :
    ∃ v : ℕ → (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν), Monotone v ∧ (∀ n, v n ∈ s) ∧ IsLUB (Set.range v) S :=
  lOneOperator_directed_countable_sup hs hpos hdir hS

theorem integral_kernel_lattice_formulas [SFinite μ] [SFinite ν]
    {K H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} {k h : X × Y → ℝ}
    (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H) :
    IsIntegralKernel (fun z => max (k z) (h z)) (K ⊔ H) ∧
      IsIntegralKernel (fun z => min (k z) (h z)) (K ⊓ H) := ⟨hk.sup hh, hk.inf hh⟩

theorem integral_submodule_lattice_ideal [SigmaFinite μ] [SigmaFinite ν]
    {S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hK : K ∈ integralOperatorSubmodule μ ν)
    (hSK : |S| ≤ |K|) : S ∈ integralOperatorSubmodule μ ν := integralOperatorSubmodule_solid hK hSK

theorem integral_operator_order_closed [SigmaFinite μ] [SFinite ν]
    {s : Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)} (hs : s.Nonempty)
    (hI : ∀ T ∈ s, IsIntegralOperator T) (hpos : ∀ T ∈ s, 0 ≤ T)
    (hdir : DirectedOn (· ≤ ·) s) {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : IsLUB s S) :
    IsIntegralOperator S := IsIntegralOperator.of_directed_sup_sigmaFinite hs hI hpos hdir hS

/-- Theorem 3.15 over the real L1 spaces used in the integral-kernel
development. Regularity is actual positive decomposition; the integral
space is a proved order-closed ideal, the projection is continuous and
contractive, and the complementary subspace is exactly lattice singularity.
The complex extension is a separate obligation. -/
def Theorem_3_15_real (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν] : Prop :=
  (∀ T : Lp ℝ 1 μ →ₗ[ℝ] Lp ℝ 1 ν, Continuous T ↔ IsRegularLinearMap T) ∧
  IsOrderClosedIdeal (integralOperatorSubmodule μ ν) ∧
  (∃ P : (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) →L[ℝ] (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν),
    LinearMap.IsProj (integralOperatorSubmodule μ ν) P.toLinearMap ∧
    0 ≤ P ∧ P ≤ ContinuousLinearMap.id ℝ _ ∧ ‖P‖ ≤ 1) ∧
  IsCompl (integralOperatorSubmodule μ ν) (singularOperatorSubmodule μ ν) ∧
  (∀ S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν,
    S ∈ singularOperatorSubmodule μ ν ↔ ∀ K, IsIntegralOperator K → |S| ⊓ |K| = 0) ∧
  (∀ (α : Type*) (l : Filter α) (f : α → (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν))
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν), OrderConverges f l T →
      (∀ᶠ i in l, IsIntegralOperator (f i)) → IsIntegralOperator T)

theorem theorem_3_15_real_proof (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν] :
    Theorem_3_15_real μ ν := by
  refine ⟨lOne_linearMap_continuous_iff_regular, integralOperatorOrderClosedIdeal,
    ⟨integralBandProjection, integralOperatorOrderClosedIdeal.bandProjection_isProj,
      integralBandProjection_nonneg, integralBandProjection_le_id, norm_integralBandProjection_le_one⟩,
    integral_singular_isCompl, mem_singularOperatorSubmodule, ?_⟩
  intro α l f T hconv hf
  exact integralOperatorOrderClosedIdeal.mem_of_orderConverges hf hconv

theorem integral_singular_decomposition_unique [SigmaFinite μ] [SigmaFinite ν]
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ∃! p : (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) × (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν),
      IsIntegralOperator p.1 ∧ IsSingularOperator p.2 ∧ T = p.1 + p.2 :=
  exists_unique_integral_singular_decomposition T

/-- The equivalent signed-modulus criterion stated after Theorem 3.15. -/
theorem singular_iff_signed_modulus (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsSingularOperator S ↔ ∀ K, IsIntegralOperator K → |S - K| = |S + K| :=
  isSingularOperator_iff_abs_sub_eq_abs_add S

theorem integral_projection_preserves_modulus [SigmaFinite μ] [SigmaFinite ν]
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    integralBandProjection |T| = |integralBandProjection T| :=
  integralOperatorOrderClosedIdeal.bandProjection_abs T

theorem integral_singular_modulus_formula [SigmaFinite μ] [SigmaFinite ν]
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    |T| = |T - integralBandProjection T| + |integralBandProjection T| :=
  integral_singular_modulus_decomposition T

end PEMS
