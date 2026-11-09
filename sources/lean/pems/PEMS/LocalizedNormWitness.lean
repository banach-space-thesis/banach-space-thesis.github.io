import PEMS.ExactSection4B
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open MeasureTheory Set Filter Topology ThesisCommon
open scoped ENNReal

namespace PEMS

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

private theorem nontrivial_lOne_of_nonzero (hμ : StrictlyLocalizable μ) (hne : μ ≠ 0) :
    Nontrivial (LOne ℝ μ) := by
  have h : ∃ i : strictlyLocalizableParts hμ, μ i.val ≠ 0 := by
    by_contra! hall
    apply hne
    rw [← strictlyLocalizable_sum_restrict hμ]
    simp [fun i => Measure.restrict_eq_zero.mpr (hall i)]
  obtain ⟨i, hi⟩ := h
  let f := indicatorConstLp 1 (strictlyLocalizablePart_measurable hμ i)
    (strictlyLocalizablePart_finite hμ i).ne (1 : ℝ)
  have hf : ‖f‖ ≠ 0 := by
    rw [show ‖f‖ = _ from norm_indicatorConstLp (by norm_num) (by norm_num)]
    simpa using (ENNReal.toReal_pos hi (strictlyLocalizablePart_finite hμ i).ne).ne'
  exact ⟨⟨f, 0, fun he => hf (by simp [he])⟩⟩

private theorem norm_cut_sub_eq_union (A B : Set Y)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (f : LOne ℝ ν) :
    ‖lpCut A hA f - lpCut B hB f‖ = ‖lpCut (A ∪ B) (hA.union hB) f‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (lpCut A hA f) (lpCut B hB f),
    lpCut_coe A hA f, lpCut_coe B hB f, lpCut_coe (A ∪ B) (hA.union hB) f]
    with y hsub ha hb hu
  rw [hsub, Pi.sub_apply, ha, hb, hu]
  by_cases hy : y ∈ A
  · have hy' : y ∉ B := fun h => Set.disjoint_left.mp hd hy h
    simp [hy, hy']
  · by_cases hy' : y ∈ B <;> simp [hy, hy']

private abbrev FinitePart (ν : Measure Y) :=
  { A : Set Y // MeasurableSet A ∧ ν A < ⊤ }

private def signedCut (T : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (Λ Θ : FinitePart ν) (B : Set Y) (hB : MeasurableSet B) :
    LOne ℝ μ →L[ℝ] LOne ℝ ν :=
  (lpCutL (Λ.val \ Θ.val) (Λ.property.1.diff Θ.property.1) - lpCutL B hB).comp T

private structure WitnessStep (T : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (Θ P : FinitePart ν) (ε : ℝ) where
  next : FinitePart ν
  contains : P.val ∪ Θ.val ⊆ next.val
  small : Set Y
  small_measurable : MeasurableSet small
  small_subset : small ⊆ Θ.val
  small_measure : ν small < ENNReal.ofReal ε
  vector : LOne ℝ μ
  unit : ‖vector‖ = 1
  lower : alphaTheta T Θ.val - ε < ‖signedCut T next Θ small small_measurable vector‖
  upper : ‖signedCut T next Θ small small_measurable‖ < alphaTheta T Θ.val + ε

private theorem exists_witnessStep [Nontrivial (LOne ℝ μ)] (hν : StrictlyLocalizable ν)
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (Θ P : FinitePart ν) (ε : ℝ) (hε : 0 < ε) :
    Nonempty (WitnessStep T Θ P ε) := by
  have hΘ := Θ.property.1
  obtain ⟨_, ⟨δ₀, hδ₀, rfl⟩, hδ₀bound⟩ := exists_lt_of_csInf_lt
    (s := {r : ℝ | ∃ δ : ℝ, 0 < δ ∧ r = smallSetSup T Θ.val δ})
    ⟨_, 1, zero_lt_one, rfl⟩
    (show alphaTheta T Θ.val < alphaTheta T Θ.val + ε by linarith)
  let δ := min δ₀ ε
  have hδ : 0 < δ := lt_min hδ₀ hε
  have hlo : alphaTheta T Θ.val - ε / 2 < smallSetSup T Θ.val δ :=
    (by linarith : alphaTheta T Θ.val - ε / 2 < alphaTheta T Θ.val).trans_le
      (alphaTheta_le_smallSetSup T Θ.val hΘ hδ)
  obtain ⟨_, ⟨B, hB, hsub, hBδ, rfl⟩, hBlarge⟩ := exists_lt_of_lt_csSup
    (s := {q : ℝ | ∃ B : Set Y, MeasurableSet B ∧ B ⊆ Θ.val ∧
      ν B < ENNReal.ofReal δ ∧ q = cutOperatorNorm T (Θ.valᶜ ∪ B)})
    ⟨_, ∅, MeasurableSet.empty, empty_subset _, by simpa using ENNReal.ofReal_pos.mpr hδ, rfl⟩ hlo
  let U := (lpCutL (Θ.valᶜ ∪ B) (hΘ.compl.union hB)).comp T
  have hU : alphaTheta T Θ.val - ε / 2 < ‖U‖ := by
    simpa only [cutOperatorNorm_eq T _ (hΘ.compl.union hB)] using hBlarge
  rw [← U.sSup_sphere_eq_norm] at hU
  obtain ⟨_, ⟨f, hf, rfl⟩, hflarge⟩ := exists_lt_of_lt_csSup
    ((NormedSpace.sphere_nonempty.mpr (zero_le_one : (0 : ℝ) ≤ 1)).image _) hU
  have hf1 : ‖f‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hf
  obtain ⟨Λ, hΛ, hΛfin, hcontains, htail⟩ :=
    lemma_4_24_exact hν (T f) P.val Θ.val P.property.1 hΘ
      P.property.2 Θ.property.2 (ε / 2) (half_pos hε)
  let F : FinitePart ν := ⟨Λ, hΛ, hΛfin⟩
  let A := Λ \ Θ.val
  have hA : MeasurableSet A := hΛ.diff hΘ
  have hAB : Disjoint A B := Set.disjoint_left.mpr fun _ hA hB => hA.2 (hsub hB)
  have hCB : Disjoint Θ.valᶜ B := Set.disjoint_left.mpr fun _ hC hB => hC (hsub hB)
  have hdiff : ‖U f‖ - ‖signedCut T F Θ B hB f‖ < ε / 2 := by
    have hUadd : U f = lpCut Θ.valᶜ hΘ.compl (T f) + lpCut B hB (T f) := by
      apply Lp.ext
      filter_upwards [lpCut_coe (Θ.valᶜ ∪ B) (hΘ.compl.union hB) (T f),
        lpCut_coe Θ.valᶜ hΘ.compl (T f), lpCut_coe B hB (T f),
        Lp.coeFn_add (lpCut Θ.valᶜ hΘ.compl (T f)) (lpCut B hB (T f))]
        with y hU hC hB hadd
      change lpCut (Θ.valᶜ ∪ B) (hΘ.compl.union (by assumption)) (T f) y = _
      rw [hU, hadd, Pi.add_apply, hC, hB]
      exact congrFun (Set.indicator_union_of_disjoint hCB (T f)) y
    have hplus : ‖lpCut A hA (T f) + lpCut B hB (T f) - U f‖ < ε / 2 := by
      rw [hUadd, add_sub_add_right_eq_sub]
      exact htail
    have hnorm : ‖signedCut T F Θ B hB f‖ =
        ‖lpCut A hA (T f) + lpCut B hB (T f)‖ := by
      rw [show signedCut T F Θ B hB f = lpCut A hA (T f) - lpCut B hB (T f) from rfl,
        norm_cut_sub_eq_union A B hA hB hAB]
      congr 1
      apply Lp.ext
      filter_upwards [lpCut_coe (A ∪ B) (hA.union hB) (T f), lpCut_coe A hA (T f),
        lpCut_coe B hB (T f), Lp.coeFn_add (lpCut A hA (T f)) (lpCut B hB (T f))]
        with y hu ha hb hadd
      rw [hu, hadd, Pi.add_apply, ha, hb]
      exact congrFun (Set.indicator_union_of_disjoint hAB (T f)) y
    -- Only the norms need to be compared. The sign on the disjoint piece is immaterial.
    have hbound := norm_sub_norm_le (U f) (lpCut A hA (T f) + lpCut B hB (T f))
    rw [norm_sub_rev, ← hnorm] at hbound
    exact hbound.trans_lt hplus
  refine ⟨⟨F, hcontains, B, hB, hsub,
    hBδ.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _)), f, hf1, ?_, ?_⟩⟩
  · linarith
  · apply lt_of_le_of_lt _ hδ₀bound
    apply le_trans _ (cutOperatorNorm_le_smallSetSup T Θ.val hΘ hB hsub
      (hBδ.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))))
    apply le_trans _ (cutOperatorNorm_mono T (hA.union hB) (hΘ.compl.union hB)
      (Set.union_subset_union (Set.diff_subset_compl _ _) subset_rfl))
    rw [cutOperatorNorm_eq T _ (hA.union hB)]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro g
    change ‖lpCut A hA (T g) - lpCut B hB (T g)‖ ≤ _
    rw [norm_cut_sub_eq_union A B hA hB hAB]
    exact ((lpCutL (A ∪ B) (hA.union hB)).comp T).le_opNorm g

/-- The finite localizations and unit witnesses of Lemma 4.25. -/
theorem lemma_4_25_nonzero (hμ : StrictlyLocalizable μ) (hν : StrictlyLocalizable ν)
    (hne : μ ≠ 0) (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ Θ : ℕ → Set Y, ∃ hΘ : ∀ n, MeasurableSet (Θ n),
      Monotone Θ ∧ (∀ n, ν (Θ n) < ⊤) ∧
      ∃ B : ℕ → Set Y, ∃ hB : ∀ n, MeasurableSet (B n),
        (∀ n, B n ⊆ Θ n) ∧ Tendsto (fun n => ν (B n)) atTop (𝓝 0) ∧
        ∃ f : ℕ → LOne ℝ μ, (∀ n, ‖f n‖ = 1) ∧
          let U : ℕ → (LOne ℝ μ →L[ℝ] LOne ℝ ν) := fun n =>
            (lpCutL (Θ (n + 1) \ Θ n) ((hΘ (n + 1)).diff (hΘ n)) -
            lpCutL (B n) (hB n)).comp T
          Tendsto (fun n => ‖U n‖) atTop (𝓝 (localizedWeakNoncompactness T)) ∧
          Tendsto (fun n => ‖U n (f n)‖) atTop (𝓝 (localizedWeakNoncompactness T)) ∧
          Tendsto (fun n => alphaTheta T (Θ n)) atTop (𝓝 (localizedWeakNoncompactness T)) := by
  classical
  letI := nontrivial_lOne_of_nonzero hμ hne
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (n : ℕ) : ∃ P : FinitePart ν,
      alphaTheta T P.val < localizedWeakNoncompactness T + ε n := by
    obtain ⟨_, ⟨P, hP, hpfin, rfl⟩, hp⟩ := exists_lt_of_csInf_lt
      (s := {r : ℝ | ∃ P : Set Y, MeasurableSet P ∧ ν P < ⊤ ∧ r = alphaTheta T P})
      ⟨_, ∅, MeasurableSet.empty, by simp, rfl⟩
      (lt_add_of_pos_right _ (hε n))
    exact ⟨⟨P, hP, hpfin⟩, hp⟩
  choose P hP using hex
  let step (n : ℕ) (Θ : FinitePart ν) :=
    Classical.choice (exists_witnessStep hν T Θ (P (n+1)) (ε n) (hε n))
  let Θ : ℕ → FinitePart ν := Nat.rec (P 0) (fun n Θ => (step n Θ).next)
  let w (n : ℕ) := step n (Θ n)
  have hsub (n : ℕ) : (P n).val ⊆ (Θ n).val := by
    cases n with
    | zero => exact subset_rfl
    | succ n => exact subset_union_left.trans (w n).contains
  have hα (n : ℕ) : localizedWeakNoncompactness T ≤ alphaTheta T (Θ n).val ∧
      alphaTheta T (Θ n).val ≤ localizedWeakNoncompactness T + ε n :=
    ⟨localizedWeakNoncompactness_le_alphaTheta T (Θ n).property.1 (Θ n).property.2,
      (alphaTheta_antitone_localization T (P n).property.1 (Θ n).property.1
        (hsub n)).trans (hP n).le⟩
  have hαlim : Tendsto (fun n => alphaTheta T (Θ n).val) atTop
      (𝓝 (localizedWeakNoncompactness T)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using tendsto_const_nhds.add hεlim)
    exacts [fun n => (hα n).1, fun n => (hα n).2]
  have hBlim : Tendsto (fun n => ν (w n).small) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) by
        simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hεlim)
    exacts [fun _ => zero_le _, fun n => (w n).small_measure.le]
  refine ⟨fun n => (Θ n).val, fun n => (Θ n).property.1, monotone_nat_of_le_succ
    (fun n => subset_union_right.trans (w n).contains), fun n => (Θ n).property.2,
    fun n => (w n).small, fun n => (w n).small_measurable, fun n => (w n).small_subset,
    hBlim, fun n => (w n).vector, fun n => (w n).unit, ?_⟩
  let U n := signedCut T (Θ (n+1)) (Θ n) (w n).small (w n).small_measurable
  have hle n : ‖U n (w n).vector‖ ≤ ‖U n‖ := by
    simpa only [(w n).unit, mul_one] using (U n).le_opNorm (w n).vector
  have hlo : Tendsto (fun n => alphaTheta T (Θ n).val - ε n) atTop
      (𝓝 (localizedWeakNoncompactness T)) := by
    simpa using hαlim.sub hεlim
  have hhi : Tendsto (fun n => alphaTheta T (Θ n).val + ε n) atTop
      (𝓝 (localizedWeakNoncompactness T)) := by
    simpa using hαlim.add hεlim
  exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
      (fun n => (w n).lower.le.trans (hle n)) (fun n => (w n).upper.le),
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
      (fun n => (w n).lower.le) (fun n => (hle n).trans (w n).upper.le), hαlim⟩

end PEMS
