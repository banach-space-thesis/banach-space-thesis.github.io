import ThesisCommon.Analysis.GowersMaureyBlockTails
import ThesisCommon.Analysis.GowersMaureyRIS
import ThesisCommon.Analysis.GowersMaureyLogGrowth
import Mathlib.Data.Fintype.Basic

/-! Every infinite nonzero block sequence supplies actual rapidly increasing
sequences in its subspace. Sizes and supports are selected together. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem support_le_supportInterval_last (x : C00 𝕜) {n : ℕ}
    (hn : n ∈ x.support) : n ≤ (supportInterval x).last :=
  (Finset.mem_Icc.mp (support_subset_supportInterval x hn)).2

theorem supportInterval_card_le_of_support_le {x : C00 𝕜} {K : ℕ}
    (hx : ∀ n ∈ x.support, n ≤ K) : (supportInterval x).set.card ≤ K + 1 := by
  classical
  by_cases h : x.support.Nonempty
  · rw [supportInterval, dif_pos h]
    calc
      (Finset.Icc (x.support.min' h) (x.support.max' h)).card ≤
          (Finset.range (K + 1)).card := Finset.card_le_card (by
        intro n hn
        exact Finset.mem_range.mpr (by
          have := (Finset.mem_Icc.mp hn).2
          have := hx _ (Finset.max'_mem _ h)
          omega))
      _ = K + 1 := Finset.card_range _
  · simp [supportInterval, h]

theorem prefix_supportInterval_card_le {N : ℕ} {x : Fin N → C00 𝕜}
    (hx : Successive x) (hne : ∀ i, x i ≠ 0) (i : Fin N) (hi : 0 < i.val) :
    (supportInterval (prefixSum x i)).set.card ≤
      (supportInterval (x ⟨i.val - 1, by omega⟩)).last + 1 := by
  classical
  let k : Fin N := ⟨i.val - 1, by omega⟩
  apply supportInterval_card_le_of_support_le
  intro n hn
  obtain ⟨j, hj, hnj⟩ := Finsupp.mem_support_finset_sum n hn
  have hjlt : j < i := (Finset.mem_filter.mp hj).2
  have hjle : j ≤ k := by change j.val ≤ i.val - 1; have := Fin.lt_def.mp hjlt; omega
  rcases lt_or_eq_of_le hjle with hjk | rfl
  · obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr (hne k)
    exact (hx j k hjk n hnj t ht).le.trans (support_le_supportInterval_last (x k) ht)
  · exact support_le_supportInterval_last (x k) hnj

theorem exists_small_interval_block_sequence (D : ConstructionData 𝕜)
    (Y : Submodule ℝ (C00 𝕜)) (u : ℕ → C00 𝕜)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hY : ∀ i, u i ∈ Y) (hne : ∀ i, u i ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    ∃ n : ℕ → ℕ, ∃ x : ℕ → C00 𝕜,
      StrictMono n ∧ (∀ i, 0 < n i) ∧ (∀ i, A < n i) ∧
      (∀ i, x i ∈ Y) ∧ (∀ i, implicitNorm D (x i) = (1 + ε)⁻¹) ∧
      (∀ i, intervalNorm D (n i) (x i) ≤ 1) ∧
      (∀ i j, i < j → Before (x i) (x j)) ∧
      (∀ i j, i < j → ((supportInterval (x i)).last + 1 : ℝ) <
        ε * Real.sqrt (logarithmicWeight (n j))) := by
  classical
  let P (a : ℕ × C00 𝕜) := 0 < a.1 ∧ A < a.1 ∧ a.2 ∈ Y ∧
    implicitNorm D a.2 = (1 + ε)⁻¹ ∧ intervalNorm D a.1 a.2 ≤ 1
  let R (a b : ℕ × C00 𝕜) := a.1 < b.1 ∧ Before a.2 b.2 ∧
    ((supportInterval a.2).last + 1 : ℝ) < ε * Real.sqrt (logarithmicWeight b.1)
  have hg : Tendsto (fun n : ℕ => logarithmicWeight n) atTop atTop :=
    tendsto_logarithmicWeight_atTop.comp tendsto_natCast_atTop_atTop
  have hselect : ∀ s : Finset (ℕ × C00 𝕜), (∀ a ∈ s, P a) →
      ∃ b, P b ∧ ∀ a ∈ s, R a b := by
    intro s _
    let K := s.sup (fun a => (supportInterval a.2).last)
    have hall : ∀ᶠ n : ℕ in atTop, 0 < n ∧ s.sup Prod.fst < n ∧
        A < (n : ℝ) ∧ (((K : ℝ) + 1) / ε) ^ 2 < logarithmicWeight n := by
      filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (s.sup Prod.fst),
        (tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop A)),
        hg.eventually (eventually_gt_atTop ((((K : ℝ) + 1) / ε) ^ 2))] with n h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    obtain ⟨n, hnpos, hnsize, hnA, hnlog⟩ := hall.exists
    have hspace : (K : ℝ) + 1 < ε * Real.sqrt (logarithmicWeight n) := by
      have hdiv := (Real.lt_sqrt (div_nonneg (by positivity) hε.le)).mpr hnlog
      exact (div_lt_iff₀ hε).mp hdiv |>.trans_eq (mul_comm _ _)
    obtain ⟨x, hxY, hxafter, hxnorm, hxsmall⟩ :=
      exists_small_interval_vector_after D Y u hu hY hne K n hε
    refine ⟨(n, x), ⟨hnpos, hnA, hxY, hxnorm, hxsmall⟩, ?_⟩
    intro a ha
    have hK : (supportInterval a.2).last ≤ K :=
      Finset.le_sup (f := fun a : ℕ × C00 𝕜 => (supportInterval a.2).last) ha
    refine ⟨(Finset.le_sup (f := Prod.fst) ha).trans_lt hnsize,
      before_of_mem_afterCutoff (fun t ht => (support_le_supportInterval_last a.2 ht).trans hK) hxafter,
      ?_⟩
    have hKR : ((supportInterval a.2).last : ℝ) + 1 ≤ (K : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hK 1
    exact hKR.trans_lt hspace
  obtain ⟨v, hv, hvr⟩ := exists_seq_of_forall_finset_exists P R hselect
  exact ⟨fun i => (v i).1, fun i => (v i).2,
    fun i j hij => (hvr i j hij).1,
    fun i => (hv i).1, fun i => (hv i).2.1,
    fun i => (hv i).2.2.1, fun i => (hv i).2.2.2.1,
    fun i => (hv i).2.2.2.2, fun i j hij => (hvr i j hij).2.1,
    fun i j hij => (hvr i j hij).2.2⟩

theorem exists_RIS_in_block_subspace (D : ConstructionData 𝕜)
    (Y : Submodule ℝ (C00 𝕜)) (u : ℕ → C00 𝕜)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hY : ∀ i, u i ∈ Y) (hne : ∀ i, u i ≠ 0)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ x : Fin N → C00 𝕜, (∀ i, x i ∈ Y) ∧
      (∀ i, implicitNorm D (x i) = (1 + ε)⁻¹) ∧ IsRIS D ε x := by
  classical
  let A := (4 * N * Real.log 2) * ((2 : ℝ) ^ ((N : ℝ)^2 / ε^2) - 1)
  obtain ⟨n, x, hnmono, hnpos, hnlarge, hxY, hxnorm, hxsmall, hxsucc, hxspace⟩ :=
    exists_small_interval_block_sequence D Y u hu hY hne hε A
  let y (i : Fin N) := x i.val
  have hy : Successive y := fun i j hij => hxsucc _ _ hij
  have hyne (i : Fin N) : y i ≠ 0 := by
    intro hz
    have hh := hxnorm i.val
    change implicitNorm D (y i) = (1 + ε)⁻¹ at hh
    rw [hz, map_zero] at hh
    exact (inv_pos.mpr (show 0 < 1 + ε by linarith)).ne' hh.symm
  refine ⟨y, fun i => hxY i.val, fun i => hxnorm i.val, ⟨{
    epsilon_pos := hε
    epsilon_le_one := hε1
    successive := hy
    size := fun i => n i.val
    size_strict := fun i j hij => hnmono hij
    size_pos := fun i => hnpos i.val
    first_large := fun i => hnlarge i.val
    norm_bound := fun i => hxsmall i.val
    spacing := ?_
  }⟩⟩
  intro i hi
  have hcard := prefix_supportInterval_card_le hy hyne i hi
  have hspace := hxspace (i.val - 1) i.val (by omega)
  have hcardR : ((supportInterval (prefixSum y i)).set.card : ℝ) ≤
      ((supportInterval (x (i.val - 1))).last : ℝ) + 1 := by
    exact_mod_cast hcard
  exact hcardR.trans_lt hspace

end ThesisCommon.GowersMaurey
