import Sigma.AtomicSelection
import Sigma.ComplexEstimates
import ThesisCommon.Analysis.InfiniteSelection

/-! Complex atomic rows for the modified construction required in the Sigma
paper's complex extension. All variation bounds use complex modulus. -/
noncomputable section
open Set Filter Topology
namespace SigmaNonprimarity

def ComplexAdmissible (μ : ℕ → lp (fun _ : Point => ℂ) 1) : Prop :=
  (∀ n, ‖μ n‖ ≤ 1) ∧
  (∀ n k, μ n (k,false) = -μ n (k,true)) ∧
  (∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ ‖μ n (n,false)‖)

def complexMass (μ : lp (fun _ : Point => ℂ) 1) (s : Set Point) : ℂ := ∑' p : s, μ p

def complexFibreWeight (μ : lp (fun _ : Point => ℂ) 1) (n : ℕ) : ℝ :=
  ‖μ (n,false)‖ + ‖μ (n,true)‖

theorem complexFibreWeight_nonneg (μ : lp (fun _ : Point => ℂ) 1) (n : ℕ) :
    0 ≤ complexFibreWeight μ n := add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem complexFibreWeight_summable (μ : lp (fun _ : Point => ℂ) 1) :
    Summable (complexFibreWeight μ) := by
  simpa only [complexFibreWeight,tsum_bool] using (JLMS.ellOneOn_summable_norm μ).prod

theorem tsum_complexFibreWeight (μ : lp (fun _ : Point => ℂ) 1) :
    ∑' n, complexFibreWeight μ n = ‖μ‖ := by
  rw [JLMS.ellOneOn_norm_eq_tsum,(JLMS.ellOneOn_summable_norm μ).tsum_prod]
  simp only [tsum_bool,complexFibreWeight]

theorem complexFibreWeight_sum_le_norm (μ : lp (fun _ : Point => ℂ) 1) (F : Finset ℕ) :
    ∑ n ∈ F, complexFibreWeight μ n ≤ ‖μ‖ := by
  rw [← tsum_complexFibreWeight]
  exact (complexFibreWeight_summable μ).sum_le_tsum F (fun n _ => complexFibreWeight_nonneg μ n)

theorem complex_coordinate_le_norm (μ : lp (fun _ : Point => ℂ) 1) (n : ℕ) :
    ‖μ (n,false)‖ ≤ ‖μ‖ := by
  have h := complexFibreWeight_sum_le_norm μ {n}
  simp only [Finset.sum_singleton,complexFibreWeight] at h
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans h

theorem complex_atomic_summable (μ : lp (fun _ : Point => ℂ) 1) :
    Summable (fun p => μ p) := (JLMS.ellOneOn_summable_norm μ).of_norm

theorem complexMass_graphSplitter (μ : lp (fun _ : Point => ℂ) 1)
    (J : Set ℕ) (σ : ℕ → Bool) :
    complexMass μ (graphSplitter J σ) = ∑' n, J.indicator (fun k => μ (k,σ k)) n := by
  classical
  rw [complexMass,tsum_subtype,((complex_atomic_summable μ).indicator (graphSplitter J σ)).tsum_prod]
  apply tsum_congr
  intro n
  rw [tsum_bool]
  by_cases hn : n ∈ J <;> cases hσ : σ n <;>
    simp [Set.indicator_apply,graphSplitter,hn,hσ]

def complexSplitterRow (μ : lp (fun _ : Point => ℂ) 1) (J : Set ℕ) (σ : ℕ → Bool) : ℕ → ℂ :=
  J.indicator (fun n => μ (n,σ n) - μ (n,!(σ n)))

theorem complexMass_splitter_difference (μ : lp (fun _ : Point => ℂ) 1)
    (J : Set ℕ) (σ : ℕ → Bool) :
    complexMass μ (graphSplitter J σ) - complexMass μ (cylinder J \ graphSplitter J σ) =
      ∑' n, complexSplitterRow μ J σ n := by
  rw [graphSplitter_complement,complexMass_graphSplitter,complexMass_graphSplitter]
  have hs (τ : ℕ → Bool) : Summable (fun n => μ (n,τ n)) :=
    (complex_atomic_summable μ).comp_injective (fun _ _ h => congrArg Prod.fst h)
  rw [← ((hs σ).indicator J).tsum_sub ((hs (fun n => !(σ n))).indicator J)]
  apply tsum_congr
  intro n
  simp only [complexSplitterRow,Set.indicator_sub]

theorem complexSplitterRow_norm_le (μ : lp (fun _ : Point => ℂ) 1)
    (J : Set ℕ) (σ : ℕ → Bool) (n : ℕ) :
    ‖complexSplitterRow μ J σ n‖ ≤ complexFibreWeight μ n := by
  classical
  by_cases hn : n ∈ J
  · simp only [complexSplitterRow,Set.indicator_of_mem hn]
    cases hσ : σ n
    · simpa [hσ,complexFibreWeight] using norm_sub_le (μ (n,false)) (μ (n,true))
    · simpa [hσ,complexFibreWeight,add_comm] using norm_sub_le (μ (n,true)) (μ (n,false))
  · simp [complexSplitterRow,Set.indicator_of_notMem hn,complexFibreWeight_nonneg]

theorem complex_tsum_sub_le_offdiagonal (f : ℕ → ℂ) (w : ℕ → ℝ) (hw : Summable w)
    (hbound : ∀ k, ‖f k‖ ≤ w k) (J : Set ℕ)
    (hsupport : Function.support f ⊆ J) (n : ℕ) :
    ‖(∑' k, f k) - f n‖ ≤ ∑' k : ↥(J \ {n}), w k.val := by
  classical
  have hf : Summable f := hw.of_norm_bounded hbound
  let g : ℕ → ℂ := fun k => if k = n then 0 else f k
  have hg : Summable g := by
    have : g = ({n}ᶜ : Set ℕ).indicator f := by funext k; simp [g,Set.indicator_apply]
    rw [this]
    exact hf.indicator _
  have hgs : Function.support g ⊆ J \ {n} := by
    intro k hk
    have hkn : k ≠ n := by intro h; subst k; simpa [g] using hk
    have hkf : f k ≠ 0 := by simpa [g,hkn] using hk
    exact ⟨hsupport hkf,hkn⟩
  have heq : (∑' k, f k) - f n = ∑' k : ↥(J \ {n}), g k.val := by
    rw [tsum_subtype_eq_of_support_subset hgs,hf.tsum_eq_add_tsum_ite n]
    dsimp [g]
    ring
  rw [heq]
  have hgn : Summable (fun k : ↥(J \ {n}) => ‖g k.val‖) := (hg.subtype _).norm
  exact (norm_tsum_le_tsum_norm hgn).trans (hgn.tsum_le_tsum (fun k => by
    have hkn : k.val ≠ n := k.property.2
    simpa [g,hkn] using hbound k.val) (hw.subtype _))

theorem complexMass_splitter_offdiagonal (μ : lp (fun _ : Point => ℂ) 1)
    (J J₀ : Set ℕ) (hJ : J ⊆ J₀) (σ : ℕ → Bool) (n : ℕ) :
    ‖complexMass μ (graphSplitter J σ) - complexMass μ (cylinder J \ graphSplitter J σ) -
      complexSplitterRow μ J σ n‖ ≤ ∑' k : ↥(J₀ \ {n}), complexFibreWeight μ k.val := by
  rw [complexMass_splitter_difference]
  apply complex_tsum_sub_le_offdiagonal _ _ (complexFibreWeight_summable μ)
    (complexSplitterRow_norm_le μ J σ) J₀
  exact Set.support_indicator_subset.trans hJ

theorem complex_atomic_rosenthal_selection (μ : ℕ → lp (fun _ : Point => ℂ) 1)
    (hμ : ∀ n, ‖μ n‖ ≤ 1) (C : Set ℕ) (hC : C.Infinite) (δ : ℝ) (hδ : 0 < δ) :
    ∃ J₀ : Set ℕ, J₀ ⊆ C ∧ J₀.Infinite ∧
      ∀ n ∈ J₀, (∑' k : ↥(J₀ \ {n}), complexFibreWeight (μ n) k.val) < δ :=
  ThesisCommon.rosenthal_selection (fun n => complexFibreWeight (μ n))
    (fun n => complexFibreWeight_nonneg (μ n))
    (fun n F => (complexFibreWeight_sum_le_norm (μ n) F).trans (hμ n)) C hC δ hδ

/-- A bounded complex diagonal has an infinite nearly constant subsequence
with an infinite remainder, and its lower modulus bound survives the limit. -/
theorem complex_bounded_sequence_uniform_infinite_subset (u : ℕ → ℂ) (b : ℝ)
    (hb : ∀ n, b ≤ ‖u n‖ ∧ ‖u n‖ ≤ 1) (C : Set ℕ) (hC : C.Infinite)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (J : Set ℕ) (a : ℂ), J ⊆ C ∧ J.Infinite ∧ (C \ J).Infinite ∧
      b ≤ ‖a‖ ∧ ∀ n ∈ J, ‖u n - a‖ < δ := by
  obtain ⟨D,hDC,hD,hCD⟩ := ThesisCommon.infinite_coinfinite_subset C hC
  let q : ℕ → ℕ := fun n => (hD.natEmbedding D n).val
  have hq : Function.Injective q := Subtype.val_injective.comp (hD.natEmbedding D).injective
  have hv (n : ℕ) : u (q n) ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (hb (q n)).2
  obtain ⟨a,_,φ,hφ,hlim⟩ := (isCompact_closedBall (0 : ℂ) 1).tendsto_subseq hv
  have hnlim : Tendsto (fun n => ‖u (q (φ n))‖) atTop (𝓝 ‖a‖) :=
    (continuous_norm.tendsto a).comp hlim
  have ha : b ≤ ‖a‖ := ge_of_tendsto hnlim
    (Filter.Eventually.of_forall (fun n => (hb (q (φ n))).1))
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim δ hδ
  let r : ℕ → ℕ := fun n => q (φ (n+N))
  have hr : Function.Injective r := hq.comp (hφ.injective.comp (fun i j h => Nat.add_right_cancel h))
  have hrD : Set.range r ⊆ D := by
    rintro _ ⟨n,rfl⟩
    exact (hD.natEmbedding D _).property
  refine ⟨Set.range r,a,hrD.trans hDC,Set.infinite_range_of_injective hr,
    hCD.mono ?_,ha,?_⟩
  · intro n hn
    exact ⟨hn.1,fun h => hn.2 (hrD h)⟩
  · rintro _ ⟨n,rfl⟩
    simpa only [dist_eq_norm] using hN (n+N) (Nat.le_add_left N n)

end SigmaNonprimarity
