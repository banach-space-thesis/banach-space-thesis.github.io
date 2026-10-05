import Posets.BlockScalarRows
import JFA.SeparableSubspace

noncomputable section
attribute [local instance] Classical.propDecidable
open ThesisCommon Filter Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type*} [PartialOrder P] [Countable P]
  {X : P → Type*} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)
  {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Column decay from a common nonseparable subspace and compatible embeddings
into a common superspace. Quotient norm measures distance from the separable remainders. -/
theorem blockScalarMatrix_zeroColumns
    (hZ : ¬ TopologicalSpace.SeparableSpace Z)
    (j : ∀ p, Z →ₗᵢ[𝕜] X p) (e : ∀ p, X p →ₗᵢ[𝕜] W) (k : Z →ₗᵢ[𝕜] W)
    (hj : ∀ s t, s ≤ t → ∀ z, ι s t (j s z) = j t z)
    (hk : ∀ s z, e s (j s z) = k z)
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) :
    ZeroColumnsOn 𝕜 (blockScalarMatrix h T) := by
  let R : P × P → Z →L[𝕜] W := fun p => (e p.1).toContinuousLinearMap.comp
    ((operatorBlock 𝕜 X X T p.1 p.2 - blockScalarMatrix h T p.1 p.2 • ι p.2 p.1).comp
      (j p.2).toContinuousLinearMap)
  have hR : ∀ p, HasSeparableRange 𝕜 Z W (R p) := fun p =>
    ((blockScalarMatrix_remainder h T p.1 p.2).comp_right
      (j p.2).toContinuousLinearMap).comp_left (e p.1).toContinuousLinearMap
  obtain ⟨Y, hclosed, hsep, hmem⟩ := JFA.exists_common_separable_subspace R hR
  have hex : ∃ z, k z ∉ Y := by
    by_contra! hall
    have hrange : HasSeparableRange 𝕜 Z W k.toContinuousLinearMap :=
      hsep.mono (by rintro _ ⟨z, rfl⟩; exact hall z)
    exact isometry_not_separable_range hZ k.toContinuousLinearMap k.isometry hrange
  obtain ⟨z, hz⟩ := hex
  letI : IsClosed (Y : Set W) := hclosed
  let q : W →L[𝕜] W ⧸ Y := Y.mkQ.mkContinuous 1
    (fun w => by simpa only [one_mul] using Submodule.Quotient.norm_mk_le Y w)
  have hqnorm (w : W) : ‖q w‖ ≤ ‖w‖ := Submodule.Quotient.norm_mk_le Y w
  have hqzero (w : W) (hw : w ∈ Y) : q w = 0 := (Submodule.Quotient.mk_eq_zero Y).mpr hw
  have hδ : 0 < ‖q (k z)‖ := norm_pos_iff.mpr
    (fun hzero => hz ((Submodule.Quotient.mk_eq_zero Y).mp hzero))
  intro t
  let y := T (sumInjection 𝕜 X t (j t z))
  have hbound (s : P) : ‖blockScalarMatrix h T s t‖ ≤ ‖q (k z)‖⁻¹ * ‖y.val s‖ := by
    by_cases hts : t ≤ s
    · have hzero := hqzero (R (s, t) z) (hmem (s, t) z)
      have heq : q (e s (operatorBlock 𝕜 X X T s t (j t z))) =
          blockScalarMatrix h T s t • q (k z) := by
        change q (e s (operatorBlock 𝕜 X X T s t (j t z) -
          blockScalarMatrix h T s t • ι t s (j t z))) = 0 at hzero
        rw [map_sub, map_smul, map_sub, map_smul, hj t s hts, hk s] at hzero
        exact sub_eq_zero.mp hzero
      have hn : ‖blockScalarMatrix h T s t‖ * ‖q (k z)‖ ≤ ‖y.val s‖ := by
        rw [← norm_smul, ← heq]
        exact (hqnorm _).trans (by
          rw [(e s).norm_map]
          rfl)
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hδ).mpr hn
    · rw [blockScalarMatrix_zero_off_order h T hts, norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hδ.le) (norm_nonneg _)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun s => norm_nonneg _) hbound
  simpa only [mul_zero] using y.property.const_mul ‖q (k z)‖⁻¹

end Posets
