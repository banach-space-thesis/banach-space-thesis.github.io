import SurveyStatements.P1FlatBlocks
import SurveyStatements.P1RapidEstimates
import SurveyStatements.P1RapidCompactness
import SurveyStatements.P1RapidCovers
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The backward finite-length construction underlying the rapid flat-block
alternative, with sparse coefficient supports retained throughout.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The finite backward recursion constructs a flat sum with the prescribed
error at every starting level. -/
theorem rapid_finite_backward_choices
    (e : ℕ → X) (m : ℕ → ℕ) (hm : StrictMono m)
    (D : ℕ → Finset (ℕ →₀ ℂ)) (hD : ∀ j, (D j).Nonempty)
    (η γ ρ : ℕ → ℝ)
    (hη : ∀ j, 0 ≤ η j) (hγ : ∀ j, 0 ≤ γ j)
    (hρ : ∀ j, 0 ≤ ρ j) (hρ1 : ∀ j, ρ j < 1)
    (hηρ : ∀ j, η j ≤ ρ j) (hnext : ∀ j, ρ (j + 1) ≤ η j)
    (herror : ∀ j, 2 * η j + γ j + ρ (j + 1) ≤ ρ j)
    (hflat : ∀ j b, b ∈ D j → HasFlatCoefficients b)
    (hsupport : ∀ j b, b ∈ D j → ∀ i ∈ b.support, m j ≤ i ∧ i < m (j + 1))
    (hnorm : ∀ j b, b ∈ D j → |‖Finsupp.linearCombination ℂ e b‖ - 1| ≤ η j)
    (hprojection : ∀ j p q r : ℕ, m j ≤ p → p ≤ q → q ≤ r → ∀ a : ℕ → ℂ,
      ‖∑ i ∈ Finset.Icc p q, a i • e i‖ ≤
        (1 + γ j) * ‖∑ i ∈ Finset.Icc p r, a i • e i‖)
    (hcover : ∀ j : ℕ, ∀ z : ℕ →₀ ℂ, HasFlatCoefficients z →
      Finsupp.linearCombination ℂ e z ≠ 0 →
      (∀ i ∈ z.support, m j ≤ i) →
      |‖Finsupp.linearCombination ℂ e z‖ - 1| ≤ η j →
      ∃ b ∈ D j, ∃ θ ∈ unitScalars,
        ‖unitNormalize (Finsupp.linearCombination ℂ e b) -
          θ • unitNormalize (Finsupp.linearCombination ℂ e z)‖ ≤ 1 + η j) :
    ∀ k j : ℕ, ∃ b : ℕ → ℕ →₀ ℂ, ∃ α : ℕ → ℂ,
      (∀ n, b n ∈ D n) ∧ (∀ n, α n ∈ unitScalars) ∧
      HasFlatCoefficients (∑ n ∈ Finset.Ico j (j + k + 1), α n • b n) ∧
      |‖Finsupp.linearCombination ℂ e
        (∑ n ∈ Finset.Ico j (j + k + 1), α n • b n)‖ - 1| ≤ ρ j := by
  classical
  choose b₀ hb₀ using hD
  have hsumSupport (b : ℕ → ℕ →₀ ℂ) (α : ℕ → ℂ)
      (hb : ∀ n, b n ∈ D n) (j k : ℕ) :
      ∀ i ∈ (∑ n ∈ Finset.Ico j (j + k + 1), α n • b n).support,
        m j ≤ i ∧ i < m (j + k + 1) := by
    apply phased_coefficient_sum_support
    intro n hn i hi
    have hn' := Finset.mem_Ico.mp hn
    have hi' := hsupport n (b n) (hb n) i hi
    exact ⟨(hm.monotone hn'.1).trans hi'.1,
      hi'.2.trans_le (hm.monotone (by omega))⟩
  intro k
  induction k with
  | zero =>
      intro j
      refine ⟨b₀, fun _ => 1, hb₀, fun _ => by simp [unitScalars], ?_, ?_⟩
      · simpa using hflat j (b₀ j) (hb₀ j)
      · simpa using (hnorm j (b₀ j) (hb₀ j)).trans (hηρ j)
  | succ k ih =>
      intro j
      obtain ⟨b, α, hb, hα, hqflat, hqnorm⟩ := ih (j + 1)
      let z : ℕ →₀ ℂ := ∑ n ∈ Finset.Ico (j + 1) ((j + 1) + k + 1), α n • b n
      have hzflat : HasFlatCoefficients z := hqflat
      have hznorm : |‖Finsupp.linearCombination ℂ e z‖ - 1| ≤ ρ (j + 1) := hqnorm
      have hzvec : Finsupp.linearCombination ℂ e z ≠ 0 := by
        intro hz
        rw [hz, norm_zero] at hznorm
        norm_num at hznorm
        linarith [hρ1 (j + 1)]
      have hzsupport := hsumSupport b α hb (j + 1) k
      obtain ⟨d, hd, θ, hθ, hθcover⟩ := hcover j z hzflat hzvec
        (fun i hi => (hm.monotone (by omega : j ≤ j + 1)).trans (hzsupport i hi).1)
        (hznorm.trans (hnext j))
      have hdvec : Finsupp.linearCombination ℂ e d ≠ 0 := by
        intro hz
        have he := (hnorm j d hd).trans (hηρ j)
        rw [hz, norm_zero] at he
        norm_num at he
        linarith [hρ1 j]
      have hθneg : -θ ∈ unitScalars := by simpa [unitScalars] using hθ
      have hdis : Disjoint d.support z.support := by
        apply Finset.disjoint_left.mpr
        intro i hi hiz
        have hdi := (hsupport j d hd i hi).2
        have hzi := (hzsupport i hiz).1
        omega
      have hnewflat := flatCoefficients_sub_phase (hflat j d hd) hzflat hdis hθ
      have hproj : ‖Finsupp.linearCombination ℂ e d‖ ≤
          (1 + γ j) * ‖Finsupp.linearCombination ℂ e d -
            θ • Finsupp.linearCombination ℂ e z‖ := by
        have h := sparse_initial_projection_bound (hprojection j) d ((-θ) • z)
          (hm (by omega : j < j + 1)) (hsupport j d hd)
          (fun i hi => (hzsupport i (Finsupp.support_smul hi)).1)
        simpa only [neg_smul, ← sub_eq_add_neg, map_sub, map_smul] using h
      have hnewnorm : |‖Finsupp.linearCombination ℂ e (d - θ • z)‖ - 1| ≤ ρ j := by
        rw [map_sub, map_smul]
        exact (rapid_backward_error hdvec hzvec hθ (hη j) (hγ j) (hρ (j + 1))
          (hnorm j d hd) hznorm hθcover hproj).trans (herror j)
      let b' := Function.update b j d
      let α' := Function.update (fun n => -θ * α n) j 1
      have hb' : ∀ n, b' n ∈ D n := by
        intro n
        by_cases hn : n = j
        · subst n; simpa [b'] using hd
        · simpa [b', hn] using hb n
      have hα' : ∀ n, α' n ∈ unitScalars := by
        intro n
        by_cases hn : n = j
        · subst n; simp [α', unitScalars]
        · have hθn : ‖θ‖ = 1 := hθ
          have hαn : ‖α n‖ = 1 := hα n
          simp [α', hn, unitScalars, norm_mul, hθn, hαn]
      have hEq : (∑ n ∈ Finset.Ico j (j + (k + 1) + 1), α' n • b' n) = d - θ • z := by
        have hIco : Finset.Ico j (j + (k + 1) + 1) =
            insert j (Finset.Ico (j + 1) ((j + 1) + k + 1)) := by
          ext n
          simp only [Finset.mem_Ico, Finset.mem_insert]
          omega
        rw [hIco, Finset.sum_insert (by simp)]
        have htail : (∑ n ∈ Finset.Ico (j + 1) ((j + 1) + k + 1), α' n • b' n) =
            (-θ) • z := by
          rw [show (-θ) • z = ∑ n ∈ Finset.Ico (j + 1) ((j + 1) + k + 1),
            (-θ) • (α n • b n) from Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          have hnj : n ≠ j := by have := Finset.mem_Ico.mp hn; omega
          simp [b', α', hnj, smul_smul]
        rw [htail]
        simp [b', α', neg_smul, sub_eq_add_neg]
      exact ⟨b', α', hb', hα', by simpa only [hEq] using hnewflat,
        by simpa only [hEq] using hnewnorm⟩

/-- The finite recursion and compactness give infinitely many successive
choices with one common ordered partial-sum bound. -/
theorem rapid_infinite_choices_of_covers (e : ℕ → X) (η γ ρ : ℕ → ℝ)
    (coverData : RapidCoverData e η γ)
    (hη : ∀ j, 0 ≤ η j) (hγ : ∀ j, 0 ≤ γ j)
    (hρ : ∀ j, 0 ≤ ρ j) (hρ1 : ∀ j, ρ j < 1)
    (hηρ : ∀ j, η j ≤ ρ j) (hnext : ∀ j, ρ (j + 1) ≤ η j)
    (herror : ∀ j, 2 * η j + γ j + ρ (j + 1) ≤ ρ j) :
    ∃ b : ℕ → ℕ →₀ ℂ, ∃ α : ℕ → ℂ,
      (∀ j, b j ∈ coverData.families j) ∧ (∀ j, α j ∈ unitScalars) ∧
      ∀ N, ‖sequencePartialSum (fun j => Finsupp.linearCombination ℂ e (b j)) α N‖ ≤
        (1 + γ 0) * (1 + ρ 0) := by
  classical
  have hfinite := rapid_finite_backward_choices e coverData.m coverData.strictMono
    coverData.families coverData.nonempty η γ ρ hη hγ hρ hρ1 hηρ hnext herror
    coverData.flat coverData.support coverData.norm coverData.projection coverData.cover
  have hchoose : ∀ L : ℕ, ∃ b : ℕ → ℕ →₀ ℂ, ∃ α : ℕ → ℂ,
      (∀ j, b j ∈ coverData.families j) ∧ (∀ j, α j ∈ unitScalars) ∧
      |‖Finsupp.linearCombination ℂ e (∑ j ∈ Finset.range (L + 1), α j • b j)‖ - 1| ≤ ρ 0 := by
    intro L
    obtain ⟨b, α, hb, hα, _, hn⟩ := hfinite L 0
    exact ⟨b, α, hb, hα, by simpa using hn⟩
  choose b α hb hα hn using hchoose
  let v : ℕ → ℕ → X := fun L j => Finsupp.linearCombination ℂ e (b L j)
  let D : ℕ → Finset X := fun j => (coverData.families j).image (Finsupp.linearCombination ℂ e)
  have hv : ∀ L j, v L j ∈ D j := by
    intro L j
    exact Finset.mem_image.mpr ⟨b L j, hb L j, rfl⟩
  have hbound : ∀ L N, N ≤ L → ‖sequencePartialSum (v L) (α L) N‖ ≤
      (1 + γ 0) * (1 + ρ 0) := by
    intro L N hNL
    by_cases hNzero : N = 0
    · subst N
      simp only [sequencePartialSum, Finset.range_zero, Finset.sum_empty, norm_zero]
      exact mul_nonneg (by linarith [hγ 0]) (by linarith [hρ 0])
    let start := coverData.m 0
    let boundary := coverData.m N
    let p : ℕ →₀ ℂ := ∑ j ∈ Finset.range N, α L j • b L j
    let z : ℕ →₀ ℂ := ∑ j ∈ Finset.Ico N (L + 1), α L j • b L j
    have hp : ∀ i ∈ p.support, start ≤ i ∧ i < boundary := by
      apply phased_coefficient_sum_support
      intro j hj i hi
      have hjN := Finset.mem_range.mp hj
      have hi' := coverData.support j (b L j) (hb L j) i hi
      exact ⟨(coverData.strictMono.monotone (Nat.zero_le j)).trans hi'.1,
        hi'.2.trans_le (coverData.strictMono.monotone (by omega))⟩
    have hz : ∀ i ∈ z.support, boundary ≤ i := by
      have hzs : ∀ i ∈ z.support, boundary ≤ i ∧ i < coverData.m (L + 1) := by
        apply phased_coefficient_sum_support
        intro j hj i hi
        have hj' := Finset.mem_Ico.mp hj
        have hi' := coverData.support j (b L j) (hb L j) i hi
        exact ⟨(coverData.strictMono.monotone hj'.1).trans hi'.1,
          hi'.2.trans_le (coverData.strictMono.monotone (by omega))⟩
      exact fun i hi => (hzs i hi).1
    have hfull : p + z = ∑ j ∈ Finset.range (L + 1), α L j • b L j :=
      Finset.sum_range_add_sum_Ico _ (by omega)
    have hfullnorm : ‖Finsupp.linearCombination ℂ e (p + z)‖ ≤ 1 + ρ 0 := by
      rw [hfull]
      linarith [(abs_le.mp (hn L)).2]
    have hprojection := sparse_initial_projection_bound (coverData.projection 0) p z
      (coverData.strictMono (Nat.pos_of_ne_zero hNzero)) hp hz
    have hpeq : Finsupp.linearCombination ℂ e p = sequencePartialSum (v L) (α L) N := by
      simp only [p, map_sum, map_smul, sequencePartialSum, v]
    rw [hpeq] at hprojection
    exact hprojection.trans (mul_le_mul_of_nonneg_left hfullnorm (by linarith [hγ 0]))
  obtain ⟨d, β, hd, hβ, hβbound⟩ := finiteFamily_phase_compactness D v α hv hα hbound
  have hrep : ∀ j, ∃ c ∈ coverData.families j, Finsupp.linearCombination ℂ e c = d j :=
    fun j => Finset.mem_image.mp (hd j)
  choose c hc hceq using hrep
  exact ⟨c, β, hc, hβ, by simpa only [hceq] using hβbound⟩

/-- A fixed rapid positive error sequence. -/
def rapidEta (j : ℕ) : ℝ := (1 / 16 : ℝ) ^ (j + 2)

def rapidRho (j : ℕ) : ℝ := 4 * rapidEta j

theorem rapidEta_pos (j : ℕ) : 0 < rapidEta j := by
  exact pow_pos (by norm_num) _

theorem rapidEta_le (j : ℕ) : rapidEta j ≤ 1 / 256 := by
  have hp : (1 / 16 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  dsimp [rapidEta]
  rw [pow_add]
  norm_num
  nlinarith

theorem rapidEta_succ (j : ℕ) : rapidEta (j + 1) = rapidEta j / 16 := by
  dsimp [rapidEta]
  rw [show j + 1 + 2 = (j + 2) + 1 by omega, pow_succ]
  ring

theorem rapidEta_tendsto_zero : Tendsto rapidEta atTop (𝓝 0) := by
  have hp : Tendsto (fun j : ℕ => (1 / 16 : ℝ) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact hp.comp (tendsto_add_atTop_nat 2)

/-- The full rapid alternative, once the successive covers have been
constructed from failure of toroidal separation. -/
theorem rapid_flatBlocks_of_covers (e : ℕ → X)
    (coverData : RapidCoverData e rapidEta rapidEta) :
    ∃ b : ℕ → ℕ →₀ ℂ, ∃ α : ℕ → ℂ,
      (∀ j, b j ∈ coverData.families j) ∧ (∀ j, α j ∈ unitScalars) ∧
      (∀ j, IsFlatBlock e (Finsupp.linearCombination ℂ e (b j))) ∧
      Tendsto (fun j => ‖Finsupp.linearCombination ℂ e (b j)‖) atTop (𝓝 1) ∧
      HasBoundedPartialSums (fun j => Finsupp.linearCombination ℂ e (b j)) α := by
  have hηnonneg (j : ℕ) : 0 ≤ rapidEta j := (rapidEta_pos j).le
  have hρnonneg (j : ℕ) : 0 ≤ rapidRho j := by
    exact mul_nonneg (by norm_num) (hηnonneg j)
  have hρ1 (j : ℕ) : rapidRho j < 1 := by
    dsimp [rapidRho]
    linarith [rapidEta_le j]
  have hηρ (j : ℕ) : rapidEta j ≤ rapidRho j := by
    dsimp [rapidRho]
    linarith [rapidEta_pos j]
  have hnext (j : ℕ) : rapidRho (j + 1) ≤ rapidEta j := by
    rw [rapidRho, rapidEta_succ]
    linarith [rapidEta_pos j]
  have herror (j : ℕ) : 2 * rapidEta j + rapidEta j + rapidRho (j + 1) ≤ rapidRho j := by
    rw [rapidRho, rapidRho, rapidEta_succ]
    linarith [rapidEta_pos j]
  obtain ⟨b, α, hb, hα, hbound⟩ := rapid_infinite_choices_of_covers e rapidEta rapidEta
    rapidRho coverData hηnonneg hηnonneg hρnonneg hρ1 hηρ hnext herror
  have hflat (j : ℕ) : IsFlatBlock e (Finsupp.linearCombination ℂ e (b j)) := by
    apply flatCoefficients_isFlatBlock (coverData.flat j (b j) (hb j))
    intro hz
    have hn := coverData.norm j (b j) (hb j)
    rw [hz, norm_zero] at hn
    norm_num at hn
    linarith [rapidEta_le j]
  have hnorm : Tendsto (fun j => ‖Finsupp.linearCombination ℂ e (b j)‖) atTop (𝓝 1) := by
    have hd : Tendsto (fun j => ‖Finsupp.linearCombination ℂ e (b j)‖ - 1)
        atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun j => ?_) rapidEta_tendsto_zero
      simpa only [Real.norm_eq_abs] using coverData.norm j (b j) (hb j)
    simpa using hd.add_const 1
  exact ⟨b, α, hb, hα, hflat, hnorm,
    ⟨(1 + rapidEta 0) * (1 + rapidRho 0), hbound⟩⟩

/-- The source rapid flat-block alternative with all finite-cover hypotheses
discharged. Sparse coefficients retain the successive supports explicitly. -/
theorem rapid_flatBlock_alternative {e : ℕ → X} (he : IsAsymptoticallyMonotone e)
    (hno : ∀ ε : ℝ, 0 < ε →
      ¬ ∃ x : ℕ → X, (∀ n, x n ∈ sequenceClosedSpan e ∧ ‖x n‖ = 1) ∧
        ∀ n k, n ≠ k → 1 + ε < toroidalDistance (x n) (x k)) :
    ∃ m : ℕ → ℕ, ∃ b : ℕ → ℕ →₀ ℂ, ∃ α : ℕ → ℂ,
      StrictMono m ∧ (∀ j, HasFlatCoefficients (b j)) ∧
      (∀ j, IsFlatBlock e (Finsupp.linearCombination ℂ e (b j))) ∧
      (∀ j i, i ∈ (b j).support → m j ≤ i ∧ i < m (j + 1)) ∧
      (∀ j, α j ∈ unitScalars) ∧
      Tendsto (fun j => ‖Finsupp.linearCombination ℂ e (b j)‖) atTop (𝓝 1) ∧
      HasBoundedPartialSums (fun j => Finsupp.linearCombination ℂ e (b j)) α := by
  obtain ⟨coverData⟩ := exists_rapidCoverData e he rapidEta rapidEta
    rapidEta_pos rapidEta_pos hno
  obtain ⟨b, α, hb, hα, hflat, hnorm, hbound⟩ := rapid_flatBlocks_of_covers e coverData
  exact ⟨coverData.m, b, α, coverData.strictMono,
    fun j => coverData.flat j (b j) (hb j), hflat,
    fun j i hi => coverData.support j (b j) (hb j) i hi, hα, hnorm, hbound⟩

end SurveyStatements.P1
