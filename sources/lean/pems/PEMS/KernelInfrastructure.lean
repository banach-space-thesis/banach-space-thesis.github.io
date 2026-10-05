import ThesisCommon.Analysis.IntegralKernelPositive
import ThesisCommon.Analysis.IntegralKernelModulus
import ThesisCommon.Analysis.IntegralKernelOrder
import ThesisCommon.Analysis.IntegralKernelDomination
import ThesisCommon.Analysis.MeasureAlgebraLimits
import ThesisCommon.Analysis.StandardMeasureRepresentation
import ThesisCommon.Analysis.LpMeasureCoding
import ThesisCommon.Analysis.IntegralKernelCoding
import ThesisCommon.Analysis.LpCodingOrder

/-! Supporting results for Theorem 1.1, in the paper's dependency order.
Theorem 3.7 and signed Proposition 3.14 are proved outright.
The Lemma 4.3 result below is its superlevel-transport step,
not the full integral/singular operator transport theorem. -/
noncomputable section
open MeasureTheory Filter Topology ThesisCommon
namespace PEMS
variable {X : Type*} [MeasurableSpace X]

/-- Theorem 3.7 (th: separablefinite-to-borel), Section 3: a finite measure
space with countably generated sigma algebra has a measure-algebra isomorphism
to a finite Borel measure on a compact metric space. No point-separation or
nonatomicity assumption is added. StandardFiniteMeasureSpace bundles exactly
the topology, metric, Borel sigma algebra and finite measure of the witness. -/
def Theorem_3_7 (μ : Measure X) [IsFiniteMeasure μ] [MeasurableSpace.CountablyGenerated X] : Prop :=
  ∃ S : StandardFiniteMeasureSpace, Nonempty (MeasureAlgebraIso μ S.measure)

/-- The cited representation theorem is supplied by explicit Cantor coding,
with atoms included automatically; it is not imported as an assumed fact. -/
theorem theorem_3_7_proof (μ : Measure X) [IsFiniteMeasure μ]
    [MeasurableSpace.CountablyGenerated X] : Theorem_3_7 μ :=
  exists_standardFiniteMeasureSpace X μ

/-- The representation witness also carries the actual L¹ isometry used in
the subsequent reduction. This follows by measurable factorization through
the same Cantor coding, including when the original sigma algebra does not
separate points. -/
theorem theorem_3_7_with_lOne (𝕜 : Type*) [RCLike 𝕜] (μ : Measure X)
    [IsFiniteMeasure μ] [MeasurableSpace.CountablyGenerated X] :
    ∃ S : StandardFiniteMeasureSpace, Nonempty (MeasureAlgebraIso μ S.measure) ∧
      Nonempty (Lp 𝕜 1 S.measure ≃ₗᵢ[𝕜] Lp 𝕜 1 μ) :=
  ⟨cantorMeasureModel X μ, ⟨cantorMeasureAlgebraIso X μ⟩, ⟨cantorLOneEquiv 𝕜 X μ⟩⟩

/-- In the real setting, the same L¹ isometry preserves the actual lattice
supremum. This is the lattice representation used after Theorem 3.7. -/
theorem theorem_3_7_with_lattice (μ : Measure X) [IsFiniteMeasure μ]
    [MeasurableSpace.CountablyGenerated X] :
    ∃ S : StandardFiniteMeasureSpace, Nonempty (MeasureAlgebraIso μ S.measure) ∧
      ∃ e : Lp ℝ 1 S.measure ≃ₗᵢ[ℝ] Lp ℝ 1 μ,
        ∀ u v, e (u ⊔ v) = e u ⊔ e v := by
  refine ⟨cantorMeasureModel X μ, ⟨cantorMeasureAlgebraIso X μ⟩, cantorLOneEquiv ℝ X μ, ?_⟩
  exact lpComapEquiv_sup μ (MeasurableSpace.mapNatBool X)
    (MeasurableSpace.measurable_mapNatBool X) (comap_mapNatBool X) 1

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

/-- Proposition 3.14 (prop: KernelinL1), Section 3: the measurable real kernel
of an integral operator between finite L¹ spaces is integrable on the product.
This target retains signed kernels; positivity is not added to its statement. -/
def Proposition_3_14 [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (k : X × Y → ℝ) : Prop :=
  IsIntegralKernel k K → Integrable k (μ.prod ν)

/-- The original signed Proposition 3.14, following the paper's proof:
the actual modulus has kernel |k|, then testing at one and applying Tonelli
gives product integrability. No countable-generation hypothesis is added. -/
theorem proposition_3_14_proof [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (k : X × Y → ℝ) :
    Proposition_3_14 K k := fun hk => hk.integrable

/-- The earlier positive special case remains available. -/
theorem proposition_3_14_of_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (k : X × Y → ℝ) (hpos : ∀ z, 0 ≤ k z) :
    Proposition_3_14 K k := fun hk => integrable_kernel_of_nonneg hk hpos

/-- Remark 3.12's absolute-kernel assertion for sigma-finite input spaces.
The shared theorem even permits an arbitrary output measure. -/
theorem integral_modulus_kernel [SigmaFinite μ]
    (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (k : X × Y → ℝ) (hk : IsIntegralKernel k K) :
    IsIntegralKernel (fun z => |k z|) (lOneOperatorModulus K) := hk.modulus

/-- Definition 3.13 has a bounded real truncation with the stated kernel and
norm at most ||K||, including for signed kernels, in the finite-input setting. -/
theorem exists_truncated_integral_operator [IsFiniteMeasure μ] [SFinite ν]
    (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (k : X × Y → ℝ) (hk : IsIntegralKernel k K) (r : ℝ) :
    ∃ Kr : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν, IsIntegralKernel (truncatedKernel r k) Kr ∧ ‖Kr‖ ≤ ‖K‖ :=
  ⟨hk.truncatedOperator r, hk.truncatedOperator_represents r, hk.norm_truncatedOperator_le r⟩

/-- Kernel order in the finite-measure reduction: comparison of operators
on nonnegative inputs is precisely product-a.e. comparison of kernels. -/
theorem integral_operator_le_iff_kernel_le [IsFiniteMeasure μ] [SFinite ν]
    {K H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} {k h : X × Y → ℝ}
    (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H) :
    (∀ f, 0 ≤ f → K f ≤ H f) ↔ k ≤ᵐ[μ.prod ν] h := hk.le_iff_kernel_le hh

/-- The corrected superlevel-set step in Lemma 4.3. The hypotheses here are
the approximating simple-function superlevel identities and the two ae limits.
The proof retains the ≥ cutoff convention, including nonnull level sets. The
full lattice/operator transport conclusions are separate open obligations. -/
theorem lemma_4_3_closed_superlevel_step (Φ : MeasureAlgebraIso μ ν)
    (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (g : ℕ → Y → ℝ) (hg : ∀ n, Measurable (g n))
    (f₀ : X → ℝ) (hf₀ : Measurable f₀) (g₀ : Y → ℝ) (hg₀ : Measurable g₀)
    (hflim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hglim : ∀ᵐ y ∂ν, Tendsto (fun n => g n y) atTop (𝓝 (g₀ y)))
    (htransport : ∀ n (q : ℚ),
      Φ.toEquiv (MeasureAlgebra.superlevel μ (f n) (hf n) q) =
        MeasureAlgebra.superlevel ν (g n) (hg n) q) (c : ℝ) :
    Φ.toEquiv (MeasureAlgebra.closedSuperlevel μ f₀ hf₀ c) =
      MeasureAlgebra.closedSuperlevel ν g₀ hg₀ c :=
  Φ.map_closedSuperlevel_of_ae_tendsto f hf g hg f₀ hf₀ g₀ hg₀ hflim hglim htransport c

end PEMS
