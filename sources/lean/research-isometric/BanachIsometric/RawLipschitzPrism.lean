import BanachIsometric.RawLipschitzChains
import BanachIsometric.RawSingularPrismChain

/-! An actual Lipschitz homotopy's singular prism preserves Lipschitz support. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology NNReal unitInterval

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem exists_lipschitz_homotopyPrism {f₀ f₁ : C(X, Y)} (H : f₀.Homotopy f₁)
    {L : ℝ≥0} (hL : LipschitzWith L H.toContinuousMap) {n : ℕ}
    (i : Fin (n + 1)) (s : RawSingularSimplex X n) {M : ℝ≥0} (hM : LipschitzWith M s) :
    ∃ P : ℝ≥0, LipschitzWith P (homotopyPrism H i s) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_prism i
  have hf : LipschitzWith 1 (Prod.fst : unitInterval × Simplex n → unitInterval) := LipschitzWith.prod_fst
  have hs : LipschitzWith 1 (Prod.snd : unitInterval × Simplex n → Simplex n) := LipschitzWith.prod_snd
  have hprod := hf.prodMk (hM.comp hs)
  exact ⟨_, (hL.comp hprod).comp hK⟩

theorem rawPrism_preserves_lipschitz {f₀ f₁ : C(X, Y)} (H : f₀.Homotopy f₁)
    {L : ℝ≥0} (hL : LipschitzWith L H.toContinuousMap) (n : ℕ) :
    rawLipschitzCarrier X n ≤ (rawLipschitzCarrier Y (n + 1)).comap (rawPrism H n) := by
  conv_lhs => rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, ⟨M, hM⟩, rfl⟩
  change rawPrism H n (Finsupp.single s 1) ∈ rawLipschitzCarrier Y (n + 1)
  rw [rawPrism_single_one]
  apply Submodule.sum_mem
  intro i _
  exact (rawLipschitzCarrier Y (n + 1)).toAddSubgroup.zsmul_mem
    (Finsupp.single_mem_supported ℚ 1 (exists_lipschitz_homotopyPrism H hL i s hM)) _

end BanachIsometric.SingularPrism
