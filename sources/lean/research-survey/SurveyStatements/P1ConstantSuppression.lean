import SurveyStatements.P1FlatScalarObstruction
import SurveyStatements.P1SubsetSumCube
import SurveyStatements.P1C0FiniteExtension
import SurveyStatements.P1RamseyFusion

/-! The exact constant-modulus suppression property sufficient for the
toroidal separation argument, and its c0 consequence for the actual flat
coefficient obstruction. The infinite selection theorem is not assumed here. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def HasUnitModulusSuppression (e : ℕ → X) (K : ℝ) : Prop :=
  ∀ F : Finset ℕ, ∀ a : ℕ → ℂ,
    (∀ i ∈ F, a i = 0 ∨ ‖a i‖ = 1) → ∀ S : Finset ℕ, S ⊆ F →
      ‖∑ i ∈ S, a i • e i‖ ≤ K * ‖∑ i ∈ F, a i • e i‖

theorem HasUnitModulusSuppression.subsequence {e : ℕ → X} {K : ℝ}
    (h : HasUnitModulusSuppression e K) (ν : ℕ → ℕ) (hν : Function.Injective ν) :
    HasUnitModulusSuppression (e ∘ ν) K := by
  classical
  intro F a ha S hSF
  let b := Function.extend ν a (fun _ => 0)
  have hb (i : ℕ) : b (ν i) = a i := hν.extend_apply _ _ i
  have hflat : ∀ i ∈ F.image ν, b i = 0 ∨ ‖b i‖ = 1 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    simpa only [hb] using ha j hj
  have hs : S.image ν ⊆ F.image ν := Finset.image_subset_image hSF
  have hbound := h (F.image ν) b hflat (S.image ν) hs
  rw [Finset.sum_image (fun i _ j _ hij => hν hij),
    Finset.sum_image (fun i _ j _ hij => hν hij)] at hbound
  simpa only [hb, Function.comp_apply] using hbound

theorem orderedFlatBlockCoefficients_norm_one_of_ne_zero
    (m : ℕ → ℕ) (hm : StrictMono m) (b : ℕ → ℕ →₀ ℂ)
    (hsupport : ∀ n i, i ∈ (b n).support → m n ≤ i ∧ i < m (n + 1))
    (hflat : ∀ n, HasFlatCoefficients (b n))
    (α : ℕ → ℂ) (hα : ∀ n, α n ∈ unitScalars) (i : ℕ)
    (hi : orderedBlockCoefficients b α i ≠ 0) :
    ‖orderedBlockCoefficients b α i‖ = 1 := by
  classical
  have hex : ∃ n ∈ Finset.range (i + 1), i ∈ (b n).support := by
    by_contra h
    push_neg at h
    apply hi
    exact Finset.sum_eq_zero fun n hn => by simp [Finsupp.notMem_support_iff.mp (h n hn)]
  obtain ⟨n, _, hin⟩ := hex
  rw [orderedBlockCoefficients_on_support m hm b hsupport α hin, norm_mul]
  have hαn : ‖α n‖ = 1 := hα n
  have hbn : ‖b n i‖ = 1 := hflat n i hin
  simp only [hαn, hbn, mul_one]

theorem exists_bounded_unitModulus_flat_coefficients {e : ℕ → X}
    (he : IsAsymptoticallyMonotone e)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (hno : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ x : ℕ → X, (∀ n, x n ∈ sequenceClosedSpan e ∧ ‖x n‖ = 1) ∧
        ∀ n k, n ≠ k → 1 + ε < toroidalDistance (x n) (x k)) :
    ∃ a : ℕ → ℂ, (∀ n, a n = 0 ∨ ‖a n‖ = 1) ∧ HasBoundedPartialSums e a ∧
      ¬ Tendsto a atTop (𝓝 0) := by
  classical
  obtain ⟨m, b, α, hm, hflat, hblocks, hsupp, hα, _, hbound⟩ :=
    rapid_flatBlock_alternative he hno
  have hbnz : ∀ n, b n ≠ 0 := fun n hzero => (hblocks n).1 (by simp [hzero])
  refine ⟨orderedBlockCoefficients b α, ?_,
    orderedBlockCoefficients_bounded (by norm_num) hp m hm b hsupp α hbound,
    orderedFlatBlockCoefficients_not_tendsto_zero m hm b hsupp hflat hbnz α hα⟩
  intro n
  by_cases hn : orderedBlockCoefficients b α n = 0
  · exact Or.inl hn
  · exact Or.inr (orderedFlatBlockCoefficients_norm_one_of_ne_zero m hm b hsupp hflat α hα n hn)

theorem nonvanishing_coefficients_infinite_support (a : ℕ → ℂ)
    (hnot : ¬ Tendsto a atTop (𝓝 0)) : {i : ℕ | a i ≠ 0}.Infinite := by
  classical
  by_contra h
  have hfin : {i : ℕ | a i ≠ 0}.Finite := Set.not_infinite.mp h
  have hz : ∀ᶠ i in atTop, a i = 0 := by
    have hbound := hfin.bddAbove
    obtain ⟨N, hN⟩ := hbound
    filter_upwards [eventually_gt_atTop N] with i hi
    by_contra hne
    exact (not_le_of_gt hi) (hN hne)
  have heq : (fun _ : ℕ => (0 : ℂ)) =ᶠ[atTop] a := hz.mono (fun _ hi => hi.symm)
  exact hnot (tendsto_const_nhds.congr' heq)

theorem suppression_bounded_flat_subsetSums
    (e : ℕ → X) {K : ℝ} (hK : 0 ≤ K) (hsupp : HasUnitModulusSuppression e K)
    (a : ℕ → ℂ) (ha : ∀ i, a i = 0 ∨ ‖a i‖ = 1)
    {C : ℝ} (hC : ∀ N, ‖sequencePartialSum e a N‖ ≤ C)
    (ν : ℕ → ℕ) (hν : StrictMono ν) :
    ∀ S : Finset ℕ, ‖∑ j ∈ S, a (ν j) • e (ν j)‖ ≤ K * C := by
  classical
  intro S
  obtain ⟨M, hM⟩ := (S.image ν).exists_nat_subset_range
  have h := hsupp (Finset.range M) a (fun i _ => ha i) (S.image ν) hM
  rw [Finset.sum_image] at h
  · exact h.trans (mul_le_mul_of_nonneg_left (hC M) hK)
  · exact fun i _ j _ hij => hν.injective hij

def phaseSubsequenceCoefficients (a : ℕ → ℂ) (ν : ℕ → ℕ) (b : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  Finsupp.onFinset b.support (fun n => b n * a (ν n)) (by
    intro n hn
    exact Finsupp.mem_support_iff.mpr (fun h => hn (by
      change b n * a (ν n) = 0
      rw [h, zero_mul])))

@[simp] theorem phaseSubsequenceCoefficients_apply (a : ℕ → ℂ) (ν : ℕ → ℕ)
    (b : ℕ →₀ ℂ) (n : ℕ) : phaseSubsequenceCoefficients a ν b n = b n * a (ν n) := rfl

theorem phaseSubsequenceCoefficients_linearCombination
    (e : ℕ → X) (a : ℕ → ℂ) (ν : ℕ → ℕ) (b : ℕ →₀ ℂ) :
    Finsupp.linearCombination ℂ (e ∘ ν) (phaseSubsequenceCoefficients a ν b) =
      Finsupp.linearCombination ℂ (fun n => a (ν n) • e (ν n)) b := by
  classical
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ
    (show (phaseSubsequenceCoefficients a ν b).support ⊆ b.support from
      Finsupp.support_onFinset_subset), Finsupp.linearCombination_apply]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [phaseSubsequenceCoefficients_apply, Function.comp_apply, smul_smul]

theorem phased_subsequence_c0_lower_bound (e : ℕ → X) (he : ∀ n, ‖e n‖ = 1)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (a : ℕ → ℂ) (ν : ℕ → ℕ) (hν : StrictMono ν)
    (ha : ∀ n, ‖a (ν n)‖ = 1) (b : ℕ →₀ ℂ) :
    (1 / 4 : ℝ) * ‖c0Finsupp b‖ ≤
      ‖Finsupp.linearCombination ℂ (fun n => a (ν n) • e (ν n)) b‖ := by
  let w := phaseSubsequenceCoefficients a ν b
  let g := Finsupp.embDomain ⟨ν, hν.injective⟩ w
  have hcomb : Finsupp.linearCombination ℂ e g =
      Finsupp.linearCombination ℂ (fun n => a (ν n) • e (ν n)) b := by
    rw [Finsupp.linearCombination_embDomain]
    exact phaseSubsequenceCoefficients_linearCombination e a ν b
  have hpoint (n : ℕ) : ‖b n‖ ≤
      4 * ‖Finsupp.linearCombination ℂ (fun n => a (ν n) • e (ν n)) b‖ := by
    have h := uniform_partialSum_finsupp_coefficient_bound he (by norm_num) hp g (ν n)
    rw [hcomb] at h
    have hg : g (ν n) = b n * a (ν n) := Finsupp.embDomain_apply _ _ n
    rw [hg, norm_mul, ha n, mul_one] at h
    linarith
  have hnorm := norm_c0Finsupp_le
    (show 0 ≤ 4 * ‖Finsupp.linearCombination ℂ (fun n => a (ν n) • e (ν n)) b‖ by positivity)
    hpoint
  linarith

theorem unitModulusSuppression_toroidal_elton_odell [CompleteSpace X]
    (e : ℕ → X) (he : IsAsymptoticallyMonotone e)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    {K : ℝ} (hK : 0 ≤ K) (hsupp : HasUnitModulusSuppression e K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  classical
  by_contra hsep
  have hno : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ x : ℕ → X, (∀ n, x n ∈ sequenceClosedSpan e ∧ ‖x n‖ = 1) ∧
        ∀ n k, n ≠ k → 1 + ε < toroidalDistance (x n) (x k) := by
    intro ε hε
    rintro ⟨x, hx, hdist⟩
    apply hsep
    refine ⟨ε, hε, x, fun n => (hx n).2, ?_⟩
    intro n k hnk θ hθ
    exact (hdist n k hnk).le.trans (toroidalDistance_le_phase _ _ hθ)
  obtain ⟨a, ha, hbounded, hnot⟩ := exists_bounded_unitModulus_flat_coefficients he hp hno
  obtain ⟨C, hC⟩ := hbounded
  have hCnonneg : 0 ≤ C := by simpa [sequencePartialSum] using hC 0
  obtain ⟨ν, hν, hνa⟩ := infiniteSet_exists_strictMono_sequence
    {i : ℕ | a i ≠ 0} (nonvanishing_coefficients_infinite_support a hnot)
  have hνnorm (n : ℕ) : ‖a (ν n)‖ = 1 := (ha (ν n)).resolve_left (hνa n)
  let u : ℕ → X := fun n => a (ν n) • e (ν n)
  have hsub : ∀ S : Finset ℕ, ‖∑ n ∈ S, u n‖ ≤ K * C :=
    suppression_bounded_flat_subsetSums e hK hsupp a ha hC ν hν
  have hupper (b : ℕ →₀ ℂ) :
      ‖Finsupp.linearCombination ℂ u b‖ ≤ (4 * (K * C)) * ‖c0Finsupp b‖ := by
    rw [Finsupp.linearCombination_apply]
    exact finite_complex_subsetSum_cube_bound b.support u (norm_nonneg _)
      (fun S _ => hsub S) b (fun n _ => c0Finsupp_apply_norm_le b n)
  have hlower (b : ℕ →₀ ℂ) :
      (1 / 4 : ℝ) * ‖c0Finsupp b‖ ≤ ‖Finsupp.linearCombination ℂ u b‖ :=
    phased_subsequence_c0_lower_bound e he.2.1 hp a ν hν hνnorm b
  obtain ⟨T, _, _, hTlower⟩ := exists_c0_embedding_of_finite_coefficient_bounds u
    (by norm_num : 0 < (1 / 4 : ℝ)) (by positivity : 0 ≤ 4 * (K * C)) hlower hupper
  exact hsep (c0_embedding_toroidal_elton_odell T (by norm_num) hTlower)

end SurveyStatements.P1
