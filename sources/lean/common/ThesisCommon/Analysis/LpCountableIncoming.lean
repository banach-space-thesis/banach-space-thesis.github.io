import ThesisCommon.Analysis.SublinearFibreSupport
import ThesisCommon.Analysis.EllOneThreshold
import ThesisCommon.Analysis.CountableCoordinateSupport
import ThesisCommon.Analysis.SeparableTotalDual

/-! Direct incoming support for actual arbitrary-index lp sums, 1 < p < ∞.
The scalar phase estimate uses the exact finite disjoint-sum power identity. -/
noncomputable section
open TopologicalSpace
open scoped ENNReal BigOperators
namespace ThesisCommon
attribute [local instance] Classical.decEq
variable {𝕜 Γ X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem lp_finite_single_norm_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    {n : ℕ} (e : Fin n ↪ Γ) (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ‖∑ i, (lp.single p (e i) (x i) : lp (fun _ : Γ => X) p)‖ ≤ (n : ℝ) ^ (1 / p.toReal) := by
  classical
  have hdis : ∀ i j : Fin n, i ≠ j → ∀ γ,
      (lp.single p (e i) (x i) : lp (fun _ : Γ => X) p) γ = 0 ∨
        (lp.single p (e j) (x j) : lp (fun _ : Γ => X) p) γ = 0 := by
    intro i j hij γ
    by_cases hγ : γ = e i
    · right
      exact lp.single_apply_ne (E := fun _ : Γ => X) p (e j) (x j)
        (fun h => hij (e.injective (hγ.symm.trans h)))
    · exact Or.inl (lp.single_apply_ne (E := fun _ : Γ => X) p (e i) (x i) hγ)
  have heq := lp_disjoint_sign_sum_rpow hp (fun i => lp.single p (e i) (x i)) hdis (fun _ => true)
  simp only [signedValue, if_true, lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))] at heq
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _) hp).mp
  rw [heq, ← Real.rpow_mul (Nat.cast_nonneg n), one_div_mul_cancel hp.ne', Real.rpow_one]
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) ^ p.toReal := Finset.sum_le_sum (fun i _ =>
      Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le)
    _ = n := by simp

theorem lp_single_growth (p : ℝ≥0∞) (hp : 1 < p.toReal)
    (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, M * (n : ℝ) ^ (1 / p.toReal) < n * ε := by
  obtain ⟨n, hn⟩ := exists_ellOne_power_threshold (M := M) hp (show 0 < 2 * ε by positivity)
  refine ⟨n, ?_⟩
  have h := ellOne_power_threshold hp hM hn
  convert h using 1
  ring

theorem lp_countable_incoming_fibres (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    (htotal : HasCountableTotalDual 𝕜 Y) (T : lp (fun _ : Γ => X) p →L[𝕜] Y) :
    {α | T.comp (lp.singleContinuousLinearMap (𝕜 := 𝕜) (p := p) (E := fun _ : Γ => X) α) ≠ 0}.Countable := by
  apply operator_countable_fibre_support
    (fun α => lp.singleContinuousLinearMap (𝕜 := 𝕜) (p := p) (E := fun _ : Γ => X) α)
    (fun n => (n : ℝ) ^ (1 / p.toReal)) ?_ (lp_single_growth p hp) htotal T
  intro n e x hx
  simpa only [lp.singleContinuousLinearMap_apply] using
    lp_finite_single_norm_bound p (zero_lt_one.trans hp) e x hx

/-- A relation records nonzero actual source-to-target coordinate maps. -/
def lpFibreRelation (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (α β : Γ) : Prop :=
  ((lpCoordinate (𝕜 := 𝕜) p β).comp T).comp
    (lp.singleContinuousLinearMap (𝕜 := 𝕜) (p := p) (E := fun _ : Γ => X) α) ≠ 0

theorem lpFibreRelation_outgoing_countable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    [SeparableSpace X] (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (α : Γ) :
    {β | lpFibreRelation p T α β}.Countable := by
  obtain ⟨S, hS, hT⟩ := lp_operator_countable_support hp
    (T.comp (lp.singleContinuousLinearMap (𝕜 := 𝕜) (p := p) (E := fun _ : Γ => X) α))
  apply hS.mono
  intro β hβ
  by_contra hβS
  apply hβ
  apply ContinuousLinearMap.ext
  intro x
  change T (lp.single p α x) β = 0
  by_contra hn
  exact hβS (hT x hn)

theorem lpFibreRelation_incoming_countable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    [SeparableSpace X] (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (β : Γ) :
    {α | lpFibreRelation p T α β}.Countable :=
  lp_countable_incoming_fibres p hp (hasCountableTotalDual_of_separable 𝕜 X)
    ((lpCoordinate p β).comp T)

theorem lpFibreRelation_zero (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) {α β : Γ}
    (h : ¬ lpFibreRelation p T α β) (x : X) : T (lp.single p α x) β = 0 :=
  DFunLike.congr_fun (not_not.mp h) x

end ThesisCommon
