import BanachIsometric.RawSingularChains
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! Lipschitz singular chains are the supported submodule of the actual
continuous singular chains. The actual boundary and Lipschitz maps
preserve that support. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology NNReal unitInterval

theorem exists_lipschitz_simplexMap {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) :
    ∃ L : ℝ≥0, LipschitzWith L (simplexMap f) := by
  let A := (FunOnFinite.linearMap ℝ ℝ f).toContinuousLinearMap
  refine ⟨‖A‖₊ * 1, ?_⟩
  exact (A.lipschitz.comp (LipschitzWith.subtype_val _)).subtype_mk
    (fun x => (stdSimplex.map f x).property)

theorem exists_lipschitz_face {n : ℕ} (i : Fin (n + 2)) :
    ∃ L : ℝ≥0, LipschitzWith L (face i) :=
  exists_lipschitz_simplexMap i.succAbove

theorem simplexTime_lipschitz : LipschitzWith 1 simplexTime := by
  have h := (LipschitzWith.eval (1 : Fin 2) : LipschitzWith 1
    (Function.eval (1 : Fin 2) : (Fin 2 → ℝ) → ℝ)).comp
      (LipschitzWith.subtype_val (stdSimplex ℝ (Fin 2)))
  simpa only [mul_one] using h.subtype_mk (fun w => (simplexTime w).property)

theorem exists_lipschitz_prism {n : ℕ} (i : Fin (n + 1)) :
    ∃ L : ℝ≥0, LipschitzWith L (prism i) := by
  obtain ⟨L₀, h₀⟩ := exists_lipschitz_simplexMap (upper i)
  obtain ⟨L₁, h₁⟩ := exists_lipschitz_simplexMap i.predAbove
  exact ⟨_, (simplexTime_lipschitz.comp h₀).prodMk h₁⟩

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

def rawLipschitzCarrier (X : Type*) [PseudoMetricSpace X] (n : ℕ) :
    Submodule ℚ (RawRationalChains X n) :=
  Finsupp.supported ℚ ℚ {s | ∃ L : ℝ≥0, LipschitzWith L s}

theorem rawLipschitzCarrier_mem {n : ℕ} (c : RawRationalChains X n) :
    c ∈ rawLipschitzCarrier X n ↔ ∀ s ∈ c.support, ∃ L : ℝ≥0, LipschitzWith L s :=
  Finsupp.mem_supported ℚ c

theorem rawBoundary_preserves_lipschitz (n : ℕ) :
    rawLipschitzCarrier X (n + 1) ≤ (rawLipschitzCarrier X n).comap (rawBoundary n) := by
  conv_lhs => rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, ⟨L, hL⟩, rfl⟩
  change rawBoundary n (Finsupp.single s 1) ∈ rawLipschitzCarrier X n
  rw [rawBoundary_single]
  apply Submodule.sum_mem
  intro i _
  obtain ⟨M, hM⟩ := exists_lipschitz_face i
  exact (rawLipschitzCarrier X n).toAddSubgroup.zsmul_mem
    (Finsupp.single_mem_supported ℚ 1 ⟨L * M, hL.comp hM⟩) _

theorem rawChainMap_preserves_lipschitz (f : C(X, Y)) {L : ℝ≥0}
    (hL : LipschitzWith L f) (n : ℕ) :
    rawLipschitzCarrier X n ≤ (rawLipschitzCarrier Y n).comap (rawChainMap f n) := by
  conv_lhs => rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, ⟨M, hM⟩, rfl⟩
  change rawChainMap f n (Finsupp.single s 1) ∈ rawLipschitzCarrier Y n
  simp only [rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact Finsupp.single_mem_supported ℚ 1 ⟨L * M, hL.comp hM⟩

end BanachIsometric.SingularPrism
