import ThesisCommon.Analysis.IntegralKernelCoding

/-! Kernel transport through measure-preserving maps whose actual L1 pullbacks
are surjective isometries. Pointwise generation of the source sigma algebra
is not needed. The concrete isometries are constructed separately. -/
noncomputable section
open Set MeasureTheory Filter

namespace ThesisCommon
variable {X Y A B : Type*}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSpace B]
variable {μ : Measure X} {ν : Measure Y} {ρ : Measure A} {σ : Measure B}

theorem integral_eq_comp_of_measurePreserving {a : X → A}
    (ha : MeasurePreserving a μ ρ) {f : A → ℝ} (hf : StronglyMeasurable f) :
    (∫ x, f x ∂ρ) = ∫ x, f (a x) ∂μ := by
  rw [← ha.map_eq]
  exact integral_map_of_stronglyMeasurable ha.measurable hf

theorem ae_iff_comp_of_measurePreserving {a : X → A}
    (ha : MeasurePreserving a μ ρ) {p : A → Prop} (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂ρ, p x) ↔ ∀ᵐ x ∂μ, p (a x) := by
  rw [← ha.map_eq]
  exact ae_map_iff ha.measurable.aemeasurable hp

variable (a : X → A) (b : Y → B)
variable (ha : MeasurePreserving a μ ρ) (hb : MeasurePreserving b ν σ)
variable (eA : Lp ℝ 1 ρ ≃ₗᵢ[ℝ] Lp ℝ 1 μ) (eB : Lp ℝ 1 σ ≃ₗᵢ[ℝ] Lp ℝ 1 ν)
variable (hA : ∀ f, eA f =ᵐ[μ] f ∘ a) (hB : ∀ g, eB g =ᵐ[ν] g ∘ b)
include ha hb hA hB

theorem IsIntegralKernel.measurePreserving_transport {k : A × B → ℝ}
    {K : Lp ℝ 1 ρ →L[ℝ] Lp ℝ 1 σ} (hk : IsIntegralKernel k K) :
    IsIntegralKernel (pullbackKernel a b k) (operatorTransport eA eB K) := by
  refine ⟨measurable_pullbackKernel ha.measurable hb.measurable hk.measurable, ?_, ?_⟩
  · intro u
    let v := eA.symm u
    have hu : u =ᵐ[μ] v ∘ a := by simpa only [v, eA.apply_symm_apply] using hA v
    filter_upwards [hb.quasiMeasurePreserving.ae (hk.integrable_section v)] with y hy
    apply (ha.integrable_comp_of_integrable hy).congr
    filter_upwards [hu] with x hx
    simp only [Function.comp_apply, pullbackKernel] at hx ⊢
    rw [hx]
  · intro u
    let v := eA.symm u
    have hu : u =ᵐ[μ] v ∘ a := by simpa only [v, eA.apply_symm_apply] using hA v
    filter_upwards [hB (K v), hb.quasiMeasurePreserving.ae (hk.represents v)] with y hy hky
    change eB (K v) y = _
    rw [hy, Function.comp_apply, hky]
    calc
      (∫ x, k (x, b y) * v x ∂ρ) = ∫ x, k (a x, b y) * v (a x) ∂μ :=
        integral_eq_comp_of_measurePreserving ha
          ((hk.measurable.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.mul
            (Lp.stronglyMeasurable v))
      _ = ∫ x, pullbackKernel a b k (x, y) * u x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hu] with x hx
        simp only [Function.comp_apply] at hx
        simp only [pullbackKernel, hx]

/-- A represented measurable kernel descends through the same maps. The proof
checks measurable integrability sets and integral formulas, so it does not
rely on a convention assigning zero to undefined integrals. -/
theorem isIntegralKernel_measurePreserving_transport_iff [SFinite ρ]
    {k : A × B → ℝ} (hk : Measurable k) (K : Lp ℝ 1 ρ →L[ℝ] Lp ℝ 1 σ) :
    IsIntegralKernel (pullbackKernel a b k) (operatorTransport eA eB K) ↔
      IsIntegralKernel k K := by
  constructor
  · intro h
    refine ⟨hk, ?_, ?_⟩
    · intro u
      have hm : StronglyMeasurable (fun z : B × A => k (z.2, z.1) * u z.2) :=
        (hk.comp measurable_swap).stronglyMeasurable.mul
          ((Lp.stronglyMeasurable u).comp_measurable measurable_snd)
      apply (ae_iff_comp_of_measurePreserving hb (measurableSet_integrable hm)).mpr
      filter_upwards [h.integrable_section (eA u)] with y hy
      apply (ha.integrable_comp
        ((hk.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.mul
          (Lp.stronglyMeasurable u)).aestronglyMeasurable).mp
      apply hy.congr
      filter_upwards [hA u] with x hx
      simp only [pullbackKernel, Function.comp_apply] at hx ⊢
      rw [hx]
      rfl
    · intro u
      have hm : StronglyMeasurable (fun z : A × B => k z * u z.1) :=
        hk.stronglyMeasurable.mul ((Lp.stronglyMeasurable u).comp_measurable measurable_fst)
      apply (ae_iff_comp_of_measurePreserving hb
        (measurableSet_eq_fun (Lp.stronglyMeasurable (K u)).measurable
          hm.integral_prod_left'.measurable)).mpr
      have hrepr := h.represents (eA u)
      have hoperator : operatorTransport eA eB K (eA u) = eB (K u) := by
        simp [operatorTransport_apply]
      rw [hoperator] at hrepr
      filter_upwards [hrepr, hB (K u)] with y hy hcoe
      simp only [Function.comp_apply] at hcoe
      rw [← hcoe, hy]
      calc
        (∫ x, pullbackKernel a b k (x, y) * eA u x ∂μ) =
            ∫ x, k (a x, b y) * u (a x) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hA u] with x hx
          simp only [pullbackKernel, Function.comp_apply] at hx ⊢
          rw [hx]
        _ = ∫ x, k (x, b y) * u x ∂ρ :=
          (integral_eq_comp_of_measurePreserving ha
            ((hk.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.mul
              (Lp.stronglyMeasurable u))).symm
  · exact fun h => h.measurePreserving_transport a b ha hb eA eB hA hB

end ThesisCommon
