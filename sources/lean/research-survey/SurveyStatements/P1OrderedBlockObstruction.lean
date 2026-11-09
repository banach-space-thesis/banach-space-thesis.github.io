import SurveyStatements.P1FlatBlocks

/-!
Bounded completeness excludes uniformly bounded ordered phased block sums.
The argument expands sparse blocks into the original basis, including
partial sums ending inside a block.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Concatenate coefficients of successive blocks. Only the first `i+1`
blocks can have a nonzero coefficient at coordinate `i`. -/
def orderedBlockCoefficients (b : ℕ → ℕ →₀ ℂ) (α : ℕ → ℂ) (i : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (i + 1), α n * b n i

theorem orderedBlockCoefficients_eq_prefix
    (m : ℕ → ℕ) (hm : StrictMono m) (b : ℕ → ℕ →₀ ℂ)
    (hsupport : ∀ n i, i ∈ (b n).support → m n ≤ i ∧ i < m (n + 1))
    (α : ℕ → ℂ) {i N : ℕ} (hiN : i < m N) :
    orderedBlockCoefficients b α i = (∑ n ∈ Finset.range N, α n • b n) i := by
  classical
  have hzero {n : ℕ} (hn : N ≤ n) : b n i = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hi
    have hni := (hsupport n i hi).1
    have hmN : m N ≤ m n := hm.monotone hn
    omega
  have hzero' {n : ℕ} (hn : i + 1 ≤ n) : b n i = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hi
    have hni := (hsupport n i hi).1
    have hnle : n ≤ m n := hm.id_le n
    omega
  simp only [orderedBlockCoefficients, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  let K := max (i + 1) N
  have hleft : (∑ n ∈ Finset.range (i + 1), α n * b n i) =
      ∑ n ∈ Finset.range K, α n * b n i := by
    apply Finset.sum_subset (Finset.range_mono (Nat.le_max_left _ _))
    intro n hn hnnot
    have hn' : i + 1 ≤ n := by simpa using hnnot
    simp [hzero' hn']
  have hright : (∑ n ∈ Finset.range N, α n * b n i) =
      ∑ n ∈ Finset.range K, α n * b n i := by
    apply Finset.sum_subset (Finset.range_mono (Nat.le_max_right _ _))
    intro n hn hnnot
    have hn' : N ≤ n := by simpa using hnnot
    simp [hzero hn']
  exact hleft.trans hright.symm

theorem orderedBlockCoefficients_endpoint
    (e : ℕ → X) (m : ℕ → ℕ) (hm : StrictMono m) (b : ℕ → ℕ →₀ ℂ)
    (hsupport : ∀ n i, i ∈ (b n).support → m n ≤ i ∧ i < m (n + 1))
    (α : ℕ → ℂ) (N : ℕ) :
    sequencePartialSum e (orderedBlockCoefficients b α) (m N) =
      sequencePartialSum (fun n => Finsupp.linearCombination ℂ e (b n)) α N := by
  classical
  let c : ℕ →₀ ℂ := ∑ n ∈ Finset.range N, α n • b n
  have hsub : c.support ⊆ Finset.range (m N) := by
    intro i hi
    have hex : ∃ n ∈ Finset.range N, b n i ≠ 0 := by
      by_contra h
      push_neg at h
      have hzero : c i = 0 := by
        simp only [c, Finsupp.finset_sum_apply, Finsupp.smul_apply]
        exact Finset.sum_eq_zero fun n hn => by simp [h n hn]
      exact (Finsupp.mem_support_iff.mp hi) hzero
    obtain ⟨n, hn, hni⟩ := hex
    have hi' := (hsupport n i (Finsupp.mem_support_iff.mpr hni)).2
    have hmN := hm.monotone (Nat.succ_le_iff.mpr (Finset.mem_range.mp hn))
    exact Finset.mem_range.mpr (hi'.trans_le hmN)
  have hEq : sequencePartialSum e (orderedBlockCoefficients b α) (m N) =
      sequencePartialSum e c (m N) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [orderedBlockCoefficients_eq_prefix m hm b hsupport α (Finset.mem_range.mp hi)]
  rw [hEq, ← linearCombination_eq_partialSum e c hsub]
  simp only [c, map_sum, map_smul, sequencePartialSum]

/-- Concatenating successive blocks preserves boundedness of partial sums,
including those ending inside a block. -/
theorem orderedBlockCoefficients_bounded {e : ℕ → X} {c : ℝ} (hc : 0 < c)
    (hprojection : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      c * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (m : ℕ → ℕ) (hm : StrictMono m) (b : ℕ → ℕ →₀ ℂ)
    (hsupport : ∀ n i, i ∈ (b n).support → m n ≤ i ∧ i < m (n + 1))
    (α : ℕ → ℂ)
    (hbound : HasBoundedPartialSums (fun n => Finsupp.linearCombination ℂ e (b n)) α) :
    HasBoundedPartialSums e (orderedBlockCoefficients b α) := by
  obtain ⟨B, hB⟩ := hbound
  refine ⟨B / c, ?_⟩
  intro N
  let M := N + 1
  have hNM : N ≤ m M := (by dsimp [M]; omega : N ≤ M).trans (hm.id_le M)
  have hb := hprojection N (m M) hNM (orderedBlockCoefficients b α)
  rw [orderedBlockCoefficients_endpoint e m hm b hsupport α M] at hb
  exact (le_div_iff₀ hc).mpr (by nlinarith [hB M])

theorem orderedBlockCoefficients_on_support
    (m : ℕ → ℕ) (hm : StrictMono m) (b : ℕ → ℕ →₀ ℂ)
    (hsupport : ∀ n i, i ∈ (b n).support → m n ≤ i ∧ i < m (n + 1))
    (α : ℕ → ℂ) {n i : ℕ} (hi : i ∈ (b n).support) :
    orderedBlockCoefficients b α i = α n * b n i := by
  classical
  have hni : n < i + 1 := by
    have hnle : n ≤ m n := hm.id_le n
    have hi' := (hsupport n i hi).1
    omega
  apply Finset.sum_eq_single n
  · intro k hk hkn
    have hkzero : b k i = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hik
      have hnpos := hsupport n i hi
      have hkpos := hsupport k i hik
      rcases lt_or_gt_of_ne hkn with hkn' | hnk'
      · have hmkn : m (k + 1) ≤ m n := hm.monotone (by omega)
        omega
      · have hmnk : m (n + 1) ≤ m k := hm.monotone (by omega)
        omega
    simp [hkzero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hni))

theorem orderedBlockCoefficients_at_interval
    (m : ℕ → ℕ) (hm : StrictMono m) (b : ℕ → ℕ →₀ ℂ)
    (hsupport : ∀ n i, i ∈ (b n).support → m n ≤ i ∧ i < m (n + 1))
    (α : ℕ → ℂ) {n i : ℕ} (hi : m n ≤ i ∧ i < m (n + 1)) :
    orderedBlockCoefficients b α i = α n * b n i := by
  classical
  have hni : n < i + 1 := by
    have hnle : n ≤ m n := hm.id_le n
    omega
  apply Finset.sum_eq_single n
  · intro k hk hkn
    have hkzero : b k i = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hik
      have hkpos := hsupport k i hik
      rcases lt_or_gt_of_ne hkn with hkn' | hnk'
      · have hmkn : m (k + 1) ≤ m n := hm.monotone (by omega)
        omega
      · have hmnk : m (n + 1) ≤ m k := hm.monotone (by omega)
        omega
    simp [hkzero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hni))

theorem orderedFlatBlockCoefficients_norm_le_one
    (m : ℕ → ℕ) (hm : StrictMono m) (b : ℕ → ℕ →₀ ℂ)
    (hsupport : ∀ n i, i ∈ (b n).support → m n ≤ i ∧ i < m (n + 1))
    (hflat : ∀ n, HasFlatCoefficients (b n))
    (α : ℕ → ℂ) (hα : ∀ n, α n ∈ unitScalars) (i : ℕ) :
    ‖orderedBlockCoefficients b α i‖ ≤ 1 := by
  classical
  by_cases hzero : orderedBlockCoefficients b α i = 0
  · simp [hzero]
  · have hex : ∃ n ∈ Finset.range (i + 1), i ∈ (b n).support := by
      by_contra h
      push_neg at h
      apply hzero
      exact Finset.sum_eq_zero fun n hn => by simp [Finsupp.notMem_support_iff.mp (h n hn)]
    obtain ⟨n, _, hin⟩ := hex
    rw [orderedBlockCoefficients_on_support m hm b hsupport α hin, norm_mul]
    have hαn : ‖α n‖ = 1 := hα n
    have hbn : ‖b n i‖ = 1 := hflat n i hin
    simp [hαn, hbn]

/-- Flat nonzero successive blocks give infinitely many concatenated scalar
coefficients of modulus one. -/
theorem orderedFlatBlockCoefficients_not_tendsto_zero
    (m : ℕ → ℕ) (hm : StrictMono m) (b : ℕ → ℕ →₀ ℂ)
    (hsupport : ∀ n i, i ∈ (b n).support → m n ≤ i ∧ i < m (n + 1))
    (hflat : ∀ n, HasFlatCoefficients (b n)) (hbnz : ∀ n, b n ≠ 0)
    (α : ℕ → ℂ) (hα : ∀ n, α n ∈ unitScalars) :
    ¬ Tendsto (orderedBlockCoefficients b α) atTop (𝓝 0) := by
  classical
  have hnonempty : ∀ n, (b n).support.Nonempty := fun n =>
    Finset.nonempty_iff_ne_empty.mpr (fun h => hbnz n (Finsupp.support_eq_empty.mp h))
  choose i hi using hnonempty
  have hile : ∀ n, n ≤ i n := fun n => (hm.id_le n).trans (hsupport n (i n) (hi n)).1
  have hitop : Tendsto i atTop atTop := tendsto_atTop_mono hile tendsto_id
  intro hlim
  have hnormlim := (hlim.comp hitop).norm
  have hnorm : ∀ n, ‖orderedBlockCoefficients b α (i n)‖ = 1 := by
    intro n
    rw [orderedBlockCoefficients_on_support m hm b hsupport α (hi n), norm_mul]
    have hαn : ‖α n‖ = 1 := hα n
    have hbn : ‖b n (i n)‖ = 1 := hflat n (i n) (hi n)
    simp [hαn, hbn]
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, hnorm, norm_zero] using hnormlim
  have hfalse : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  norm_num at hfalse

/-- No preservation-of-bases assumption is needed: the original boundedly
complete sequence already excludes bounded sums of successive blocks whose
norms tend to one. -/
theorem boundedlyComplete_uniform_orderedBlock_obstruction
    {e : ℕ → X} (hcomplete : IsBoundedlyComplete e) {c : ℝ} (hc : 0 < c)
    (hprojection : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      c * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (m : ℕ → ℕ) (hm : StrictMono m) (b : ℕ → ℕ →₀ ℂ)
    (hsupport : ∀ n i, i ∈ (b n).support → m n ≤ i ∧ i < m (n + 1))
    (α : ℕ → ℂ) (hα : ∀ n, α n ∈ unitScalars)
    (hnorm : Tendsto (fun n => ‖Finsupp.linearCombination ℂ e (b n)‖) atTop (𝓝 1)) :
    ¬ HasBoundedPartialSums (fun n => Finsupp.linearCombination ℂ e (b n)) α := by
  classical
  rintro ⟨B, hB⟩
  let a := orderedBlockCoefficients b α
  have habound : HasBoundedPartialSums e a := by
    refine ⟨B / c, ?_⟩
    intro N
    let M := N + 1
    have hNM : N ≤ m M := (by dsimp [M]; omega : N ≤ M).trans (hm.id_le M)
    have hb := hprojection N (m M) hNM a
    rw [orderedBlockCoefficients_endpoint e m hm b hsupport α M] at hb
    exact (le_div_iff₀ hc).mpr (by nlinarith [hB M])
  obtain ⟨x, hx⟩ := hcomplete.2 a habound
  have hmTop : Tendsto m atTop atTop := hm.tendsto_atTop
  have hblocks : Tendsto
      (sequencePartialSum (fun n => Finsupp.linearCombination ℂ e (b n)) α)
      atTop (𝓝 x) := by
    convert hx.comp hmTop using 1
    ext N
    exact (orderedBlockCoefficients_endpoint e m hm b hsupport α N).symm
  exact phasedSeries_not_convergent hα hnorm ⟨x, hblocks⟩

end SurveyStatements.P1
