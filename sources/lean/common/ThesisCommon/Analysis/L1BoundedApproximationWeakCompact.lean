import ThesisCommon.Analysis.LpOneColumnsOperator
import ThesisCommon.Analysis.IntegralKernelWeakCompact
import ThesisCommon.Analysis.WeakCalkinNorm

/-! Uniform norm approximation of an L1 family by uniformly bounded
functions gives genuine relative weak compactness. The proof constructs
its ell-one column operator and approximates it through actual L2 spaces. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical
namespace ThesisCommon
variable {Y I : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsFiniteMeasure ν]

theorem exists_lTwo_lift_of_lOne_ae_bound (g : Lp ℝ 1 ν) {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ᵐ y ∂ν, ‖g y‖ ≤ C) :
    ∃ u : Lp ℝ 2 ν, lTwoToLOne ν u = g ∧ ‖u‖ ≤ lTwoFiniteMeasureConstant ν * C := by
  let hm : MemLp g 2 ν := MemLp.of_bound (Lp.memLp g).1 C hg
  let u := hm.toLp g
  have hu : u =ᵐ[ν] g := hm.coeFn_toLp
  refine ⟨u, ?_, ?_⟩
  · apply Lp.ext
    exact (lTwoToLOneFn_coe u).trans hu
  · have hb : ∀ᵐ y ∂ν, ‖u y‖ ≤ C := by
      filter_upwards [hu, hg] with y he hb
      simpa only [he] using hb
    have hn := Lp.norm_le_of_ae_bound hC hb
    simpa only [lTwoFiniteMeasureConstant, measureUnivNNReal,
      ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofNat, one_div, mul_comm] using hn

theorem weaklyCompact_lpOneColumnsOperator_of_bounded_approximations
    (f : I → Lp ℝ 1 ν) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ i, ‖f i‖ ≤ M)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (g : I → Lp ℝ 1 ν) (C : ℝ),
      0 ≤ C ∧ (∀ i, ∀ᵐ y ∂ν, ‖g i y‖ ≤ C) ∧ ∀ i, ‖f i - g i‖ ≤ ε) :
    IsWeaklyCompactOperator (lpOneColumnsOperator (𝕜 := ℝ) f M hM hf) := by
  let T := lpOneColumnsOperator (𝕜 := ℝ) f M hM hf
  apply (weakEssentialNorm_eq_zero_iff T).mp
  apply le_antisymm _ (weakEssentialNorm_nonneg T)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨g, C, hC, hg, herr⟩ := happrox ε hε
  choose u hueq hubound using fun i => exists_lTwo_lift_of_lOne_ae_bound (g i) hC (hg i)
  let D := lTwoFiniteMeasureConstant ν * C
  have hD : 0 ≤ D := mul_nonneg lTwoFiniteMeasureConstant_nonneg hC
  let U := lpOneColumnsOperator (𝕜 := ℝ) u D hD hubound
  let W := (lTwoToLOne ν).comp U
  have hW : IsWeaklyCompactOperator W := weaklyCompact_of_hilbert_factorization U (lTwoToLOne ν)
  have hnorm : ‖T - W‖ ≤ ε := by
    apply ellOne_norm_le_of_columns _ hε.le
    intro i
    simpa only [T, W, U, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      lpOneColumnsOperator_single, hueq] using herr i
  simpa only [zero_add] using (weakEssentialNorm_le T hW).trans hnorm

theorem isCompact_weakClosure_range_of_bounded_approximations
    (f : I → Lp ℝ 1 ν) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ i, ‖f i‖ ≤ M)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (g : I → Lp ℝ 1 ν) (C : ℝ),
      0 ≤ C ∧ (∀ i, ∀ᵐ y ∂ν, ‖g i y‖ ≤ C) ∧ ∀ i, ‖f i - g i‖ ≤ ε) :
    IsCompact (closure ((toWeakSpace ℝ (Lp ℝ 1 ν)) '' Set.range f)) := by
  letI : T2Space (WeakSpace ℝ (Lp ℝ 1 ν)) :=
    (isEmbedding_weakBidualInclusion (𝕜 := ℝ) (E := Lp ℝ 1 ν)).t2Space
  obtain ⟨K, hK, hTK⟩ :=
    weaklyCompact_lpOneColumnsOperator_of_bounded_approximations f M hM hf happrox
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  have hn : ‖(lp.single 1 i (1 : ℝ) : lp (fun _ : I => ℝ) 1)‖ ≤ 1 := by
    simp only [lp.norm_single (by norm_num : 0 < (1 : ENNReal)), norm_one, le_refl]
  simpa only [lpOneColumnsOperator_single] using hTK _ hn

end ThesisCommon
