import PL1.SchurApproximation
import PL1.DunfordPettis
import PL1.L1Masks
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Uniform integrability of weakly convergent scalar L1 sequences

The disjoint-set argument reduces the substantive compactness step to the
proved Schur theorem for scalar ell1.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace PL1.L1UniformIntegrability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A decreasing family carrying a fixed amount of some member of an
integrable sequence yields disjoint annuli carrying a fixed amount of a
subsequence. Each individual member must have vanishing mass on the family. -/
theorem exists_disjoint_annuli
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Integrable (f n) μ)
    (S : ℕ → Set Ω) (hS : ∀ N, MeasurableSet (S N)) (hanti : Antitone S)
    (hlim : ∀ n, Tendsto (fun N => ∫ x in S N, f n x ∂μ) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε)
    (hbad : ∀ N, ∃ n, ε ≤ ∫ x in S N, f n x ∂μ) :
    ∃ n : ℕ → ℕ, (∀ k, k ≤ n k) ∧ ∃ B : ℕ → Set Ω,
      (∀ k, MeasurableSet (B k)) ∧ Pairwise (fun k l => Disjoint (B k) (B l)) ∧
      ∀ k, ε / 2 < ∫ x in B k, f (n k) x ∂μ := by
  classical
  have hstep : ∀ N k : ℕ, ∃ M n P : ℕ,
      N ≤ M ∧ k ≤ n ∧ M < P ∧
      ε ≤ ∫ x in S M, f n x ∂μ ∧ (∫ x in S P, f n x ∂μ) < ε / 2 := by
    intro N k
    have hfinite : ∀ᶠ M in atTop, ∀ j ∈ Finset.range k,
        (∫ x in S M, f j x ∂μ) < ε := by
      apply (eventually_all_finset (Finset.range k)).mpr
      intro j _
      exact (hlim j).eventually_lt_const hε
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hfinite
    let M := max N M₀
    obtain ⟨n, hn⟩ := hbad M
    have hkn : k ≤ n := by
      by_contra h
      exact (not_lt_of_ge hn) (hM₀ M (le_max_right _ _) n (Finset.mem_range.mpr (by omega)))
    obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp ((hlim n).eventually_lt_const (half_pos hε))
    exact ⟨M, n, max (M + 1) P₀, le_max_left _ _, hkn,
      (Nat.lt_succ_self M).trans_le (le_max_left _ _), hn,
      hP₀ _ (le_max_right _ _)⟩
  choose a b c ha hb hc hlarge hsmall using hstep
  let cut : ℕ → ℕ := Nat.rec 0 (fun k N => c N k)
  have hcutstep : ∀ k, cut k < cut (k + 1) := by
    intro k
    exact (ha (cut k) k).trans_lt (hc (cut k) k)
  have hcut : StrictMono cut := strictMono_nat_of_lt_succ hcutstep
  let n : ℕ → ℕ := fun k => b (cut k) k
  let B : ℕ → Set Ω := fun k => S (a (cut k) k) \ S (cut (k + 1))
  refine ⟨n, (fun k => hb _ _), B, (fun k => (hS _).diff (hS _)), ?_, ?_⟩
  · intro k l hkl
    apply Set.disjoint_left.mpr
    intro x hxk hxl
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · apply hxk.2
      exact hanti ((hcut.monotone (Nat.succ_le_of_lt hlt)).trans (ha _ _)) hxl.1
    · apply hxl.2
      exact hanti ((hcut.monotone (Nat.succ_le_of_lt hgt)).trans (ha _ _)) hxk.1
  · intro k
    dsimp [B]
    rw [setIntegral_sdiff (hS _) (hf _).integrableOn (hanti (hc _ _).le)]
    have h₁ := hlarge (cut k) k
    have h₂ := hsmall (cut k) k
    change ε / 2 < (∫ x in S (a (cut k) k), f (b (cut k) k) x ∂μ) -
      ∫ x in S (c (cut k) k), f (b (cut k) k) x ∂μ
    linarith

section ScalarL1

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Uniform absolute continuity of the integral norms, in a real-valued form. -/
def UniformSmallSetMass (x : ℕ → Lp 𝕜 1 μ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
    ∀ n A, MeasurableSet A → μ A ≤ δ → (∫ a in A, ‖x n a‖ ∂μ) ≤ ε

/-- Failure of uniform absolute continuity supplies disjoint measurable sets
on which a subsequence retains a positive amount of integral norm. -/
theorem exists_disjoint_sets_of_not_uniformSmallSetMass
    {x : ℕ → Lp 𝕜 1 μ} (hbad : ¬ UniformSmallSetMass x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n : ℕ → ℕ, (∀ k, k ≤ n k) ∧
      ∃ B : ℕ → Set Ω, (∀ k, MeasurableSet (B k)) ∧
        Pairwise (fun k l => Disjoint (B k) (B l)) ∧
        ∀ k, ε < ∫ a in B k, ‖x (n k) a‖ ∂μ := by
  classical
  simp only [UniformSmallSetMass] at hbad
  push Not at hbad
  obtain ⟨ε, hε, hbad⟩ := hbad
  have hchoose : ∀ j : ℕ, ∃ n A, MeasurableSet A ∧
      μ A ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ∧ ε < ∫ a in A, ‖x n a‖ ∂μ := by
    intro j
    exact hbad _ (ENNReal.ofReal_pos.mpr (by positivity))
  choose n A hA hμA hmass using hchoose
  let S : ℕ → Set Ω := fun N => ⋃ j ≥ N, A j
  have hS : ∀ N, MeasurableSet (S N) := fun N => .iUnion fun j => .iUnion fun _ => hA j
  have hanti : Antitone S := by
    intro N M hNM
    exact iUnion₂_subset fun j hj => subset_iUnion₂_of_subset j (hNM.trans hj) (Subset.refl _)
  have hsum : ∑' j, μ (A j) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hμA)
    exact (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).tsum_ofReal_ne_top
  have hnull : μ (⋂ N, S N) = 0 := by
    have hh := measure_limsup_atTop_eq_zero hsum
    simpa only [limsup_eq_iInf_iSup_of_nat, Set.iSup_eq_iUnion, Set.iInf_eq_iInter, S] using hh
  have hlim : ∀ n, Tendsto (fun N => ∫ a in S N, ‖x n a‖ ∂μ) atTop (𝓝 0) := by
    intro n
    have h := tendsto_setIntegral_of_antitone hS hanti
      ⟨0, (L1.integrable_coeFn (x n)).norm.integrableOn⟩
    simpa only [setIntegral_measure_zero _ hnull] using h
  have hlarge : ∀ N, ∃ n, ε ≤ ∫ a in S N, ‖x n a‖ ∂μ := by
    intro N
    refine ⟨n N, (hmass N).le.trans ?_⟩
    apply setIntegral_mono_set (L1.integrable_coeFn _).norm.integrableOn
      (Eventually.of_forall fun _ => norm_nonneg _)
    exact Eventually.of_forall fun a ha => mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨le_rfl, ha⟩⟩
  obtain ⟨m, hm, B, hB, hdisj, hmassB⟩ :=
    exists_disjoint_annuli (fun n a => ‖x n a‖) (fun n => (L1.integrable_coeFn _).norm)
      S hS hanti hlim ε hε hlarge
  exact ⟨ε / 2, half_pos hε, m, hm, B, hB, hdisj, hmassB⟩

/-- Norming a sequence on disjoint measurable sets produces a single bounded
operator into the genuine scalar ell1 space. -/
theorem exists_disjoint_norming_operator (f : ℕ → Lp 𝕜 1 μ)
    (B : ℕ → Set Ω) (hB : ∀ k, MeasurableSet (B k))
    (hdisj : Pairwise (fun k l => Disjoint (B k) (B l))) :
    ∃ T : Lp 𝕜 1 μ →L[𝕜] Ell1 𝕜, ‖T‖ ≤ 1 ∧
      ∀ k, T (f k) k = (‖L1Masks.mask μ (B k) (hB k) (f k)‖ : 𝕜) := by
  classical
  choose ψ hψ hvalue using fun k =>
    exists_dual_vector'' 𝕜 (L1Masks.mask μ (B k) (hB k) (f k))
  let α : ℕ → Lp 𝕜 1 μ →L[𝕜] 𝕜 := fun k => (ψ k).comp (L1Masks.mask μ (B k) (hB k))
  have hsum : ∀ (g : Lp 𝕜 1 μ) (s : Finset ℕ), ∑ k ∈ s, ‖α k g‖ ≤ ‖g‖ := by
    intro g s
    apply le_trans _ (L1Masks.sum_norm_mask_le μ s B hB hdisj g)
    apply Finset.sum_le_sum
    intro k _
    change ‖ψ k (L1Masks.mask μ (B k) (hB k) g)‖ ≤ ‖L1Masks.mask μ (B k) (hB k) g‖
    exact ((ψ k).le_opNorm _).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hψ k) (norm_nonneg (L1Masks.mask μ (B k) (hB k) g)))
  let T₀ : Lp 𝕜 1 μ →ₗ[𝕜] Ell1 𝕜 :=
    { toFun := fun g => ⟨fun k => α k g, memℓp_gen' (by simpa using hsum g)⟩
      map_add' := by intro g h; ext k; exact (α k).map_add g h
      map_smul' := by intro c g; ext k; exact (α k).map_smul c g }
  have hT₀ : ∀ g, ‖T₀ g‖ ≤ 1 * ‖g‖ := by
    intro g
    rw [one_mul]
    apply lp.norm_le_of_forall_sum_le (by simp) (norm_nonneg g)
    intro s
    simpa only [T₀, LinearMap.coe_mk, AddHom.coe_mk, ENNReal.toReal_one, Real.rpow_one] using hsum g s
  let T := T₀.mkContinuous 1 hT₀
  refine ⟨T, ContinuousLinearMap.opNorm_le_bound _ zero_le_one hT₀, ?_⟩
  exact hvalue

/-- Weak convergence in scalar L1 implies uniform absolute continuity of the
integral norms. This holds for arbitrary measures, without a finiteness or
probability assumption. -/
theorem weaklyConverges_uniformSmallSetMass {x : ℕ → Lp 𝕜 1 μ} {a : Lp 𝕜 1 μ}
    (hx : WeaklyConverges 𝕜 (Lp 𝕜 1 μ) x a) : UniformSmallSetMass x := by
  by_contra hbad
  obtain ⟨ε, hε, n, hn, B, hB, hdisj, hmass⟩ :=
    exists_disjoint_sets_of_not_uniformSmallSetMass hbad
  obtain ⟨T, _, hvalue⟩ := exists_disjoint_norming_operator (fun k => x (n k)) B hB hdisj
  have hn_top : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have hTlim := (ell1_hasSchurProperty 𝕜 _ _ (hx.map T)).comp hn_top
  have hdiff : Tendsto (fun k => ‖T (x (n k)) - T a‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, Function.comp_def] using
      (hTlim.sub (tendsto_const_nhds (x := T a))).norm
  have hcoord : Tendsto (fun k => ‖T a k‖) atTop (𝓝 0) :=
    (L1Sum.summable_norm (T a)).tendsto_atTop_zero
  have hsumlim : Tendsto (fun k => ‖T (x (n k)) - T a‖ + ‖T a k‖) atTop (𝓝 0) := by
    simpa only [zero_add] using hdiff.add hcoord
  obtain ⟨k, hk⟩ := (hsumlim.eventually_lt_const hε).exists
  have hlower : ε < ‖T (x (n k)) k‖ := by
    rw [hvalue k, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), L1Masks.norm_mask]
    exact hmass k
  have hupper : ‖T (x (n k)) k‖ ≤ ‖T (x (n k)) - T a‖ + ‖T a k‖ := by
    calc
      ‖T (x (n k)) k‖ ≤ ‖T (x (n k)) k - T a k‖ + ‖T a k‖ := by
        simpa only [sub_add_cancel] using norm_add_le (T (x (n k)) k - T a k) (T a k)
      _ ≤ ‖T (x (n k)) - T a‖ + ‖T a k‖ := by
        apply add_le_add _ le_rfl
        exact lp.norm_apply_le_norm (by simp : (1 : ℝ≥0∞) ≠ 0) (T (x (n k)) - T a) k
  linarith

/-- The real-valued small-set criterion implies Mathlib's measure-theoretic
uniform integrability predicate. -/
theorem UniformSmallSetMass.unifIntegrable {x : ℕ → Lp 𝕜 1 μ}
    (hx : UniformSmallSetMass x) : UnifIntegrable (fun n => (x n : Ω → 𝕜)) 1 μ := by
  apply unifIntegrable_iff'.mpr
  intro ε hε
  by_cases htop : ε = ∞
  · subst ε
    exact ⟨1, by simp, fun _ _ _ _ => le_top⟩
  obtain ⟨δ, hδ, hbound⟩ := hx ε.toReal (ENNReal.toReal_pos hε.ne' htop)
  refine ⟨δ, hδ, fun n A hA hμA => ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (L1.integrable_coeFn (x n)).integrableOn]
  exact (ENNReal.ofReal_le_ofReal (hbound n A hA hμA)).trans_eq (ENNReal.ofReal_toReal htop)

/-- Weakly convergent scalar L1 sequences are uniformly integrable in
Mathlib's full sense: uniformly absolutely continuous integral norms and a
uniform L1 bound. The result applies to arbitrary measures and both fields. -/
theorem weaklyConverges_uniformIntegrable {x : ℕ → Lp 𝕜 1 μ} {a : Lp 𝕜 1 μ}
    (hx : WeaklyConverges 𝕜 (Lp 𝕜 1 μ) x a) :
    UniformIntegrable (fun n => (x n : Ω → 𝕜)) 1 μ := by
  obtain ⟨C, hC, hbound⟩ := hx.exists_pos_norm_bound
  refine ⟨fun n => (L1.integrable_coeFn (x n)).aestronglyMeasurable,
    (weaklyConverges_uniformSmallSetMass hx).unifIntegrable, ⟨⟨C, hC.le⟩, fun n => ?_⟩⟩
  rw [← Lp.enorm_def]
  exact ENNReal.coe_le_coe.mpr (hbound n)

end ScalarL1

end PL1.L1UniformIntegrability
