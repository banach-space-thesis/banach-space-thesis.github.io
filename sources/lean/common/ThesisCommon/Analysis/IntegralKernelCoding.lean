import ThesisCommon.Analysis.LpMeasureCoding
import ThesisCommon.Analysis.IntegralKernelDomination
import ThesisCommon.Analysis.OperatorIsometryTransport

/-! Transport of actual integral kernels through measurable codings.
This is used for the standard-space reduction in PEMS Lemma 4.3. It does not
assume a pointwise inverse, a kernel representation theorem, or positivity. -/
noncomputable section
open MeasureTheory Filter Set
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y A B : Type*}
variable [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable [mA : MeasurableSpace A] [mB : MeasurableSpace B]

def pullbackKernel (a : X → A) (b : Y → B) (k : A × B → 𝕜) : X × Y → 𝕜 :=
  fun z => k (a z.1, b z.2)

theorem measurable_pullbackKernel {a : X → A} {b : Y → B} {k : A × B → 𝕜}
    (ha : Measurable a) (hb : Measurable b) (hk : Measurable k) :
    Measurable (pullbackKernel a b k) :=
  hk.comp ((ha.comp measurable_fst).prodMk (hb.comp measurable_snd))

omit [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSpace B] in
theorem pullbackKernel_truncatedKernel (a : X → A) (b : Y → B)
    (k : A × B → 𝕜) (r : ℝ) :
    pullbackKernel a b (truncatedKernel r k) = truncatedKernel r (pullbackKernel a b k) := by
  classical
  funext z
  by_cases h : r ≤ ‖k (a z.1, b z.2)‖ <;> simp [pullbackKernel, truncatedKernel, h]

/-- Every measurable kernel factors through a pair of sigma-algebra codings.
This is an actual jointly measurable kernel on the product of the coded spaces. -/
theorem exists_pullbackKernel (a : X → A) (b : Y → B)
    (hagen : mA.comap a = mX) (hbgen : mB.comap b = mY)
    (k : X × Y → 𝕜) (hk : Measurable k) :
    ∃ l : A × B → 𝕜, Measurable l ∧ k = pullbackKernel a b l := by
  have hgen : (mA.prod mB).comap (Prod.map a b) = mX.prod mY := by
    rw [MeasurableSpace.comap_prodMap, hagen, hbgen]
  have hmeas : StronglyMeasurable[(mA.prod mB).comap (Prod.map a b)] k := by
    rw [hgen]
    exact hk.stronglyMeasurable
  obtain ⟨l, hl, heq⟩ := hmeas.exists_eq_measurable_comp
  exact ⟨l, hl.measurable, heq⟩

variable (μ : Measure X) (ν : Measure Y)
variable (a : X → A) (ha : Measurable a) (hagen : mA.comap a = mX)
variable (b : Y → B) (hb : Measurable b) (hbgen : mB.comap b = mY)

/-- Conjugation by the constructed L¹ isometries, on actual bounded operators. -/
def lpTransportOperator (K : Lp 𝕜 1 (μ.map a) →L[𝕜] Lp 𝕜 1 (ν.map b)) :
    Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν :=
  operatorTransport (𝕜 := 𝕜) (lpComapEquiv μ a ha hagen 1) (lpComapEquiv ν b hb hbgen 1) K

theorem lpTransportOperator_apply (K : Lp 𝕜 1 (μ.map a) →L[𝕜] Lp 𝕜 1 (ν.map b))
    (u : Lp 𝕜 1 μ) :
    lpTransportOperator μ ν a ha hagen b hb hbgen K u =
      lpComapEquiv ν b hb hbgen 1 (K ((lpComapEquiv μ a ha hagen 1).symm u)) := rfl

theorem norm_lpTransportOperator (K : Lp 𝕜 1 (μ.map a) →L[𝕜] Lp 𝕜 1 (ν.map b)) :
    ‖lpTransportOperator μ ν a ha hagen b hb hbgen K‖ = ‖K‖ :=
  norm_operatorTransport (𝕜 := 𝕜) (lpComapEquiv μ a ha hagen 1) (lpComapEquiv ν b hb hbgen 1) K

theorem weaklyCompact_lpTransportOperator_iff
    (K : Lp 𝕜 1 (μ.map a) →L[𝕜] Lp 𝕜 1 (ν.map b)) :
    IsWeaklyCompactOperator (lpTransportOperator μ ν a ha hagen b hb hbgen K) ↔
      IsWeaklyCompactOperator K :=
  weaklyCompact_operatorTransport_iff (𝕜 := 𝕜) (lpComapEquiv μ a ha hagen 1) (lpComapEquiv ν b hb hbgen 1) K

theorem weakEssentialNorm_lpTransportOperator
    (K : Lp 𝕜 1 (μ.map a) →L[𝕜] Lp 𝕜 1 (ν.map b)) :
    weakEssentialNorm (lpTransportOperator μ ν a ha hagen b hb hbgen K) = weakEssentialNorm K :=
  weakEssentialNorm_operatorTransport (𝕜 := 𝕜) (lpComapEquiv μ a ha hagen 1) (lpComapEquiv ν b hb hbgen 1) K

/-- Cutoff operators commute with transport, as required by the localization
formula. Every measurable set in the original sigma algebra is such a preimage. -/
theorem lpCutL_comp_lpTransportOperator
    (K : Lp 𝕜 1 (μ.map a) →L[𝕜] Lp 𝕜 1 (ν.map b)) (s : Set B) (hs : MeasurableSet s) :
    (lpCutL (b ⁻¹' s) (hb hs)).comp (lpTransportOperator μ ν a ha hagen b hb hbgen K) =
      lpTransportOperator μ ν a ha hagen b hb hbgen ((lpCutL s hs).comp K) := by
  apply ContinuousLinearMap.ext
  intro u
  exact (lpComapEquiv_cut ν b hb hbgen 1 s hs (K ((lpComapEquiv μ a ha hagen 1).symm u))).symm

theorem norm_lpCutL_comp_lpTransportOperator
    (K : Lp 𝕜 1 (μ.map a) →L[𝕜] Lp 𝕜 1 (ν.map b)) (s : Set B) (hs : MeasurableSet s) :
    ‖(lpCutL (b ⁻¹' s) (hb hs)).comp (lpTransportOperator μ ν a ha hagen b hb hbgen K)‖ =
      ‖(lpCutL s hs).comp K‖ := by
  rw [lpCutL_comp_lpTransportOperator, norm_lpTransportOperator]

/-- Integral representation is preserved by the coding maps. The proof uses
the change-of-variables formula and establishes section integrability as well
as the almost-everywhere formula, so no undefined-integral convention is used. -/
theorem IsIntegralKernel.lpTransport {k : A × B → 𝕜}
    {K : Lp 𝕜 1 (μ.map a) →L[𝕜] Lp 𝕜 1 (ν.map b)} (hk : IsIntegralKernel k K) :
    IsIntegralKernel (pullbackKernel a b k)
      (lpTransportOperator μ ν a ha hagen b hb hbgen K) := by
  refine ⟨measurable_pullbackKernel ha hb hk.measurable, ?_, ?_⟩
  · intro u
    let v := (lpComapEquiv μ a ha hagen 1).symm u
    have hu : u =ᵐ[μ] v ∘ a := by
      simpa [v] using lpComapEquiv_coe μ a ha hagen 1 v
    filter_upwards [ae_of_ae_map hb.aemeasurable (hk.integrable_section v)] with y hy
    apply ((integrable_map_measure hy.aestronglyMeasurable ha.aemeasurable).mp hy).congr
    filter_upwards [hu] with x hx
    simp only [Function.comp_apply] at hx ⊢
    simp only [pullbackKernel, hx]
  · intro u
    let v := (lpComapEquiv μ a ha hagen 1).symm u
    have hu : u =ᵐ[μ] v ∘ a := by
      simpa [v] using lpComapEquiv_coe μ a ha hagen 1 v
    filter_upwards [lpComapEquiv_coe ν b hb hbgen 1 (K v),
      ae_of_ae_map hb.aemeasurable (hk.represents v)] with y hy hky
    change (lpComapEquiv ν b hb hbgen 1 (K v)) y = _
    rw [hy, Function.comp_apply, hky]
    calc
      (∫ x, k (x, b y) * v x ∂μ.map a) = ∫ x, k (a x, b y) * v (a x) ∂μ :=
        integral_map_of_stronglyMeasurable ha
          ((hk.measurable.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.mul
            (Lp.stronglyMeasurable v))
      _ = ∫ x, pullbackKernel a b k (x, y) * u x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hu] with x hx
        simp only [Function.comp_apply] at hx
        simp only [pullbackKernel, hx]

/-- The converse transport also holds. Measurability of the set of integrable
sections and of the integral allows the a.e. statements to descend along the
pushforward measure, despite the coding map need not be injective. -/
theorem isIntegralKernel_lpTransport_iff [SFinite (μ.map a)] {k : A × B → 𝕜}
    (hk : Measurable k) (K : Lp 𝕜 1 (μ.map a) →L[𝕜] Lp 𝕜 1 (ν.map b)) :
    IsIntegralKernel (pullbackKernel a b k)
      (lpTransportOperator μ ν a ha hagen b hb hbgen K) ↔ IsIntegralKernel k K := by
  constructor
  · intro h
    refine ⟨hk, ?_, ?_⟩
    · intro u
      let w := lpComapEquiv μ a ha hagen 1 u
      have hw : w =ᵐ[μ] u ∘ a := lpComapEquiv_coe μ a ha hagen 1 u
      have hm : StronglyMeasurable (fun z : B × A => k (z.2, z.1) * u z.2) :=
        (hk.comp measurable_swap).stronglyMeasurable.mul
          ((Lp.stronglyMeasurable u).comp_measurable measurable_snd)
      apply (ae_map_iff hb.aemeasurable (measurableSet_integrable hm)).mpr
      filter_upwards [h.integrable_section w] with y hy
      apply (integrable_map_measure
        ((hk.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.mul
          (Lp.stronglyMeasurable u)).aestronglyMeasurable ha.aemeasurable).mpr
      apply hy.congr
      filter_upwards [hw] with x hx
      simp only [pullbackKernel, Function.comp_apply] at hx ⊢
      simp [hx]
    · intro u
      let w := lpComapEquiv μ a ha hagen 1 u
      have hw : w =ᵐ[μ] u ∘ a := lpComapEquiv_coe μ a ha hagen 1 u
      have hm : StronglyMeasurable (fun z : A × B => k z * u z.1) :=
        hk.stronglyMeasurable.mul ((Lp.stronglyMeasurable u).comp_measurable measurable_fst)
      apply (ae_map_iff hb.aemeasurable
        (measurableSet_eq_fun (Lp.stronglyMeasurable (K u)).measurable hm.integral_prod_left'.measurable)).mpr
      have hrepr := h.represents w
      have hoperator : lpTransportOperator μ ν a ha hagen b hb hbgen K w =
          lpComapEquiv ν b hb hbgen 1 (K u) := by
        simp [lpTransportOperator_apply, w]
      rw [hoperator] at hrepr
      filter_upwards [hrepr, lpComapEquiv_coe ν b hb hbgen 1 (K u)] with y hy hcoe
      simp only [Function.comp_apply] at hcoe
      rw [← hcoe, hy]
      calc
        (∫ x, pullbackKernel a b k (x, y) * w x ∂μ) =
            ∫ x, k (a x, b y) * u (a x) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hw] with x hx
          simp only [pullbackKernel, Function.comp_apply] at hx ⊢
          rw [hx]
        _ = ∫ x, k (x, b y) * u x ∂μ.map a :=
          (integral_map_of_stronglyMeasurable ha
            ((hk.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.mul
              (Lp.stronglyMeasurable u))).symm
  · exact fun h => h.lpTransport μ ν a ha hagen b hb hbgen

/-- The integral-operator class is preserved in both directions for the
constructed coding isometries. No kernel existence is assumed on the other side. -/
theorem isIntegralOperator_lpTransport_iff [SFinite (μ.map a)]
    (K : Lp 𝕜 1 (μ.map a) →L[𝕜] Lp 𝕜 1 (ν.map b)) :
    IsIntegralOperator (lpTransportOperator μ ν a ha hagen b hb hbgen K) ↔
      IsIntegralOperator K := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl, rfl⟩ := exists_pullbackKernel a b hagen hbgen k hk.measurable
    exact ⟨l, (isIntegralKernel_lpTransport_iff μ ν a ha hagen b hb hbgen hl K).mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨pullbackKernel a b k, hk.lpTransport μ ν a ha hagen b hb hbgen⟩

include ha hb in
/-- Pullback preserves the numerical column bound exactly. -/
theorem HasKernelBound.pullback {k : A × B → 𝕜} (hk : Measurable k) {C : ℝ}
    (hbound : HasKernelBound (μ.map a) (ν.map b) k C) :
    HasKernelBound μ ν (pullbackKernel a b k) C := by
  filter_upwards [ae_of_ae_map ha.aemeasurable hbound] with x hx
  have hi : Integrable (fun y => k (a x, b y)) ν :=
    (integrable_map_measure hx.1.aestronglyMeasurable hb.aemeasurable).mp hx.1
  refine ⟨hi, ?_⟩
  change (∫ y, ‖k (a x, b y)‖ ∂ν) ≤ C
  have heq : (∫ y, ‖k (a x, y)‖ ∂ν.map b) = ∫ y, ‖k (a x, b y)‖ ∂ν :=
    integral_map_of_stronglyMeasurable hb
      (hk.comp (measurable_const.prodMk measurable_id)).norm.stronglyMeasurable
  exact heq.symm.trans_le hx.2

section Finite
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The constructed integral operators, not just their kernel predicates,
commute with the coding isometries. -/
theorem integralKernelOperator_pullback {k : A × B → 𝕜} (hk : Measurable k) {C : ℝ}
    (hbound : HasKernelBound (μ.map a) (ν.map b) k C) :
    integralKernelOperator (measurable_pullbackKernel ha hb hk)
      (hbound.pullback μ ν a ha b hb hk) =
      lpTransportOperator μ ν a ha hagen b hb hbgen (integralKernelOperator hk hbound) :=
  (isIntegralKernel_integralKernelOperator _ _).unique
    ((isIntegralKernel_integralKernelOperator hk hbound).lpTransport μ ν a ha hagen b hb hbgen)

/-- The equality of truncated operators used by the standard-space reduction,
with the paper's ≥ convention at each threshold. -/
theorem truncatedKernelOperator_pullback {k : A × B → 𝕜} (hk : Measurable k) {C : ℝ}
    (hbound : HasKernelBound (μ.map a) (ν.map b) k C) (r : ℝ) :
    truncatedKernelOperator (measurable_pullbackKernel ha hb hk)
      (hbound.pullback μ ν a ha b hb hk) r =
      lpTransportOperator μ ν a ha hagen b hb hbgen (truncatedKernelOperator hk hbound r) := by
  apply (isIntegralKernel_truncatedKernelOperator _ _ _).unique
  have h := (isIntegralKernel_truncatedKernelOperator hk hbound r).lpTransport
    μ ν a ha hagen b hb hbgen
  rwa [pullbackKernel_truncatedKernel] at h

end Finite

end ThesisCommon
