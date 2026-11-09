import SurveyStatements.P5CaponLocalizedFiniteAction
import SurveyStatements.P5DyadicGridOperator

/-! The actual dyadic-grid multiplication operator acts by its square's
coefficient on every Haar tensor supported in that square. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem dyadicGridFunction_on_cell (n : ℕ) (a : Fin (2 ^ n) → 𝕜)
    (i₀ : Fin (2 ^ n)) {x : ℝ} (hx : x ∈ lpHaarCell n i₀) :
    dyadicGridFunction n a x = a i₀ := by
  unfold dyadicGridFunction
  rw [Finset.sum_eq_single i₀]
  · exact Set.indicator_of_mem hx _
  · intro i _ hi
    have hxi : x ∉ lpHaarCell n i :=
      (lpHaarLevelCells_disjoint n hi.symm).notMem_of_mem_left hx
    exact Set.indicator_of_notMem hxi _
  · intro hi
    exact (hi (Finset.mem_univ i₀)).elim

theorem dyadicHaar_zero_off_lpHaarCell (I : DyadicIndex) :
    ∀ᵐ x ∂unitIntervalMeasure, x ∉ lpHaarCell I.1 I.2 → dyadicHaar 𝕜 p I x = 0 := by
  rw [dyadicHaar_eq_support]
  simpa only [lpHaarCell_children] using
    (lpHaarVector_zero_off (𝕜 := 𝕜) (p := p) (μ := unitIntervalMeasure)
      (lpHaarCell (I.1 + 1) (2 * I.2.val))
      (lpHaarCell (I.1 + 1) (2 * I.2.val + 1)) measurableSet_Ioc measurableSet_Ioc)

theorem scalarDyadicGridOperator_of_local_support
    (n : ℕ) (a : Fin (2 ^ n) → 𝕜) (i₀ : Fin (2 ^ n))
    (f : Lp 𝕜 p unitIntervalMeasure)
    (hf : ∀ᵐ x ∂unitIntervalMeasure, x ∉ lpHaarCell n i₀ → f x = 0) :
    scalarDyadicGridOperator n a f = a i₀ • f := by
  apply Lp.ext
  filter_upwards [scalarDyadicGridOperator_ae n a f, hf, Lp.coeFn_smul (a i₀) f]
    with x hT hzero hsmul
  rw [hT, hsmul, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ lpHaarCell n i₀
  · rw [dyadicGridFunction_on_cell n a i₀ hx]
  · rw [hzero hx, mul_zero, mul_zero]

theorem scalarDyadicGridOperator_local_haar
    (n : ℕ) (a : Fin (2 ^ n) → 𝕜) (i₀ : Fin (2 ^ n)) (I : DyadicIndex)
    (hI : lpHaarCell I.1 I.2 ⊆ lpHaarCell n i₀) :
    scalarDyadicGridOperator n a (dyadicHaar 𝕜 p I) = a i₀ • dyadicHaar 𝕜 p I := by
  apply scalarDyadicGridOperator_of_local_support
  filter_upwards [dyadicHaar_zero_off_lpHaarCell (𝕜 := 𝕜) (p := p) I] with x hx
  intro hxi
  exact hx (fun hi => hxi (hI hi))

theorem mixedDyadicGridOperator_tensor_of_local_support
    (n m : ℕ) (a : Fin (2 ^ n) → Fin (2 ^ m) → 𝕜) (i₀ : Fin (2 ^ n))
    (g : Lp 𝕜 1 unitIntervalMeasure) (f : Lp 𝕜 p unitIntervalMeasure)
    (hf : ∀ᵐ x ∂unitIntervalMeasure, x ∉ lpHaarCell n i₀ → f x = 0) :
    mixedDyadicGridOperator n m a (tensorWith g f) =
      tensorWith (scalarDyadicGridOperator m (a i₀) g) f := by
  apply Lp.ext
  filter_upwards [mixedDyadicGridOperator_ae n m a (tensorWith g f),
    tensorWith_ae g f, tensorWith_ae (scalarDyadicGridOperator m (a i₀) g) f, hf]
    with x hT ht hright hzero
  rw [hT, hright]
  by_cases hx : x ∈ lpHaarCell n i₀
  · rw [Finset.sum_eq_single i₀]
    · rw [Set.indicator_of_mem hx, ht, map_smul]
    · intro i _ hi
      have hxi : x ∉ lpHaarCell n i :=
        (lpHaarLevelCells_disjoint n hi.symm).notMem_of_mem_left hx
      exact Set.indicator_of_notMem hxi _
    · intro hi
      exact (hi (Finset.mem_univ i₀)).elim
  · rw [hzero hx, zero_smul]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hxi : x ∈ lpHaarCell n i
    · rw [Set.indicator_of_mem hxi, ht, hzero hx, zero_smul, map_zero]
    · exact Set.indicator_of_notMem hxi _

theorem tensorWith_scalar_smul_left (c : 𝕜) (g : Lp 𝕜 1 unitIntervalMeasure)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    tensorWith (c • g) f = c • tensorWith g f := by
  apply Lp.ext
  filter_upwards [tensorWith_ae (c • g) f, tensorWith_ae g f,
    Lp.coeFn_smul c (tensorWith g f)] with x hleft hright hsmul
  rw [hleft, hsmul, Pi.smul_apply, hright]
  exact smul_comm _ _ _

theorem mixedDyadicGridOperator_local_productHaar
    (n m : ℕ) (a : Fin (2 ^ n) → Fin (2 ^ m) → 𝕜)
    (i₀ : Fin (2 ^ n)) (j₀ : Fin (2 ^ m)) (I J : DyadicIndex)
    (hI : lpHaarCell I.1 I.2 ⊆ lpHaarCell n i₀)
    (hJ : lpHaarCell J.1 J.2 ⊆ lpHaarCell m j₀) :
    mixedDyadicGridOperator n m a (productHaar 𝕜 p I J) =
      a i₀ j₀ • productHaar 𝕜 p I J := by
  unfold productHaar
  rw [mixedDyadicGridOperator_tensor_of_local_support n m a i₀]
  · rw [scalarDyadicGridOperator_local_haar m (a i₀) j₀ J hJ,
      tensorWith_scalar_smul_left]
  · filter_upwards [dyadicHaar_zero_off_lpHaarCell (𝕜 := 𝕜) (p := p) I] with x hx
    intro hxi
    exact hx (fun hi => hxi (hI hi))

theorem mixedDyadicGridOperator_embedded_local_image
    (m : ℕ) (a : Fin (2 ^ m) → Fin (2 ^ m) → 𝕜)
    (i₀ j₀ : Fin (2 ^ m)) (N : ℕ) :
    mixedDyadicGridOperator m m a
      (RealScalar.embedding 𝕜 p (caponLocalizedImage m i₀ j₀ p N)) =
      a i₀ j₀ • RealScalar.embedding 𝕜 p (caponLocalizedImage m i₀ j₀ p N) := by
  let F : MixedNorm ℝ p →L[ℝ] MixedNorm 𝕜 p :=
    ((mixedDyadicGridOperator m m a).restrictScalars ℝ).comp (RealScalar.embedding 𝕜 p)
  let G : MixedNorm ℝ p →L[ℝ] MixedNorm 𝕜 p :=
    ((a i₀ j₀ • (ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p))).restrictScalars ℝ).comp
      (RealScalar.embedding 𝕜 p)
  change F (caponLocalizedImage m i₀ j₀ p N) = G (caponLocalizedImage m i₀ j₀ p N)
  apply caponLocalizedImage_map_of_haar_agreement m i₀ j₀ F G
  intro I J _ hI _ hJ
  change mixedDyadicGridOperator m m a (RealScalar.embedding 𝕜 p (productHaar ℝ p I J)) =
    a i₀ j₀ • RealScalar.embedding 𝕜 p (productHaar ℝ p I J)
  simp only [RealScalar.embedding_productHaar]
  exact mixedDyadicGridOperator_local_productHaar m m a i₀ j₀ I J hI hJ

end SurveyStatements.P5
