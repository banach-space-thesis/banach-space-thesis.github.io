import ThesisCommon.Analysis.GowersMaureyRISConstruction

/-! Actual RIS subsequences of an already specified successive sequence.
The given vectors are retained, while their increasing interval parameters
and finite supports determine the recursive selection. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_RIS_subsequence (D : ConstructionData 𝕜)
    (u : ℕ → C00 𝕜) (q : ℕ → ℕ)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hne : ∀ i, u i ≠ 0) (hq : StrictMono q)
    (hbound : ∀ i, intervalNorm D (q i) (u i) ≤ 1)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ a : Fin N → ℕ, StrictMono a ∧ IsRIS D ε (fun i => u (a i)) := by
  classical
  let A := (4 * N * Real.log 2) * ((2 : ℝ)^((N : ℝ)^2 / ε^2) - 1)
  let P (i : ℕ) := 0 < q i ∧ A < (q i : ℝ)
  let R (i j : ℕ) := i < j ∧
    ((supportInterval (u i)).last + 1 : ℝ) < ε * Real.sqrt (logarithmicWeight (q j))
  have hg : Tendsto (fun i : ℕ => logarithmicWeight (q i)) atTop atTop :=
    tendsto_logarithmicWeight_atTop.comp (tendsto_natCast_atTop_atTop.comp hq.tendsto_atTop)
  have hselect : ∀ s : Finset ℕ, (∀ i ∈ s, P i) → ∃ j, P j ∧ ∀ i ∈ s, R i j := by
    intro s _
    let K := s.sup (fun i => (supportInterval (u i)).last)
    have hall : ∀ᶠ j : ℕ in atTop, s.sup id < j ∧ 0 < q j ∧ A < (q j : ℝ) ∧
        (((K : ℝ)+1)/ε)^2 < logarithmicWeight (q j) := by
      filter_upwards [eventually_gt_atTop (s.sup id),
        hq.tendsto_atTop.eventually (eventually_gt_atTop 0),
        (tendsto_natCast_atTop_atTop.comp hq.tendsto_atTop).eventually (eventually_gt_atTop A),
        hg.eventually (eventually_gt_atTop ((((K : ℝ)+1)/ε)^2))] with j h1 h2 h3 h4
      exact ⟨h1,h2,h3,h4⟩
    obtain ⟨j,hj,hqj,hAj,hlog⟩ := hall.exists
    have hspace : (K : ℝ)+1 < ε * Real.sqrt (logarithmicWeight (q j)) := by
      have hr := (Real.lt_sqrt (div_nonneg (by positivity) hε.le)).mpr hlog
      exact (div_lt_iff₀ hε).mp hr |>.trans_eq (mul_comm _ _)
    refine ⟨j,⟨hqj,hAj⟩,?_⟩
    intro i hi
    refine ⟨(Finset.le_sup (f := id) hi).trans_lt hj, ?_⟩
    have hK := Finset.le_sup (f := fun i => (supportInterval (u i)).last) hi
    have hKR : ((supportInterval (u i)).last : ℝ)+1 ≤ (K : ℝ)+1 := by
      exact_mod_cast Nat.add_le_add_right hK 1
    exact hKR.trans_lt hspace
  obtain ⟨a,ha,har⟩ := exists_seq_of_forall_finset_exists P R hselect
  have ham : StrictMono a := fun i j hij => (har i j hij).1
  let b (i : Fin N) := a i.val
  have hb : StrictMono b := fun i j hij => ham hij
  have hv : Successive (fun i : Fin N => u (b i)) := fun i j hij => hu _ _ (hb hij)
  refine ⟨b,hb,⟨{
    epsilon_pos := hε
    epsilon_le_one := hε1
    successive := hv
    size := fun i => q (b i)
    size_strict := hq.comp hb
    size_pos := fun i => (ha i.val).1
    first_large := fun i => (ha i.val).2
    norm_bound := fun i => hbound (b i)
    spacing := ?_
  }⟩⟩
  intro i hi
  have hcard := prefix_supportInterval_card_le hv (fun i => hne (b i)) i hi
  have hspace := (har (i.val-1) i.val (by omega)).2
  have hcardR : ((supportInterval (prefixSum (fun i : Fin N => u (b i)) i)).set.card : ℝ) ≤
      ((supportInterval (u (a (i.val-1)))).last : ℝ)+1 := by
    exact_mod_cast hcard
  exact hcardR.trans_lt hspace

end ThesisCommon.GowersMaurey
