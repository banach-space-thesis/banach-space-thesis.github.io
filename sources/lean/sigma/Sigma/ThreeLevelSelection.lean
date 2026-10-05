import Sigma.AtomicSelection
import ThesisCommon.Analysis.InfiniteSelection

/-! Complete proof of Lemma 4.7, including all infinite-set and quantitative clauses. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set
namespace SigmaNonprimarity

def levelChoice (μ : ℕ → lp (fun _ : Point => ℝ) 1) (T : Set ℕ) (n : ℕ) : Bool :=
  if n ∈ T then (if 0 ≤ μ n (n, false) then false else true)
  else (if 0 ≤ μ n (n, false) then true else false)

theorem levelChoice_diagonal (μ : ℕ → lp (fun _ : Point => ℝ) 1)
    (hμ : ∀ n k, μ n (k, false) = -μ n (k, true)) (T : Set ℕ) (n : ℕ) :
    μ n (n, levelChoice μ T n) - μ n (n, !(levelChoice μ T n)) =
      if n ∈ T then 2 * |μ n (n, false)| else -(2 * |μ n (n, false)|) := by
  have hy : μ n (n, true) = -μ n (n, false) := by linarith [hμ n n]
  by_cases hn : n ∈ T <;> by_cases hx : 0 ≤ μ n (n, false)
  · simp [levelChoice, hn, hx, hy, abs_of_nonneg hx]; ring
  · simp [levelChoice, hn, hx, hy, abs_of_neg (lt_of_not_ge hx)]; ring
  · simp [levelChoice, hn, hx, hy, abs_of_nonneg hx]; ring
  · simp [levelChoice, hn, hx, hy, abs_of_neg (lt_of_not_ge hx)]; ring

/-- The estimate survives every further restriction of the splitting cylinder.
The orientation may be chosen for any subpartition of the retained indices. -/
theorem three_level_bounds_of_control (μ : ℕ → lp (fun _ : Point => ℝ) 1)
    (hμ : ∀ n k, μ n (k, false) = -μ n (k, true))
    (J₀ J₁ : Set ℕ) (hJ₁ : J₁ ⊆ J₀) (a δ : ℝ) (hδ : 0 < δ)
    (hsmall : ∀ n ∈ J₀, (∑' k : ↥(J₀ \ {n}), fibreWeight (μ n) k.val) < δ)
    (happ : ∀ n ∈ J₁, |(|μ n (n, false)|) - a| < δ)
    (K T : Set ℕ) (hK : K ⊆ J₁) (hT : T ⊆ K) :
    let Z := graphSplitter K (levelChoice μ T)
    (∀ n ∈ T, |mass (μ n) Z - mass (μ n) (cylinder K \ Z) - 2*a| < 3*δ) ∧
    (∀ n ∈ K \ T, |mass (μ n) Z - mass (μ n) (cylinder K \ Z) + 2*a| < 3*δ) ∧
    (∀ n ∈ J₀ \ K, |mass (μ n) Z - mass (μ n) (cylinder K \ Z)| < 3*δ) := by
  let σ := levelChoice μ T
  let Z := graphSplitter K σ
  let M : ℕ → ℝ := fun n => mass (μ n) Z - mass (μ n) (cylinder K \ Z)
  have herr (n : ℕ) (hn : n ∈ J₀) : |M n - splitterRow (μ n) K σ n| < δ :=
    (mass_splitter_offdiagonal (μ n) K J₀ (hK.trans hJ₁) σ n).trans_lt (hsmall n hn)
  have hdiag (n : ℕ) (hn : n ∈ K) :
      splitterRow (μ n) K σ n =
        if n ∈ T then 2 * |μ n (n, false)| else -(2 * |μ n (n, false)|) := by
    rw [splitterRow, Set.indicator_of_mem hn]
    exact levelChoice_diagonal μ hμ T n
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have he := herr n (hJ₁ (hK (hT hn)))
    rw [hdiag n (hT hn), if_pos hn] at he
    have hd := happ n (hK (hT hn))
    change |M n - 2*a| < 3*δ
    rw [abs_lt] at he hd ⊢
    constructor <;> linarith [he.1, he.2, hd.1, hd.2]
  · intro n hn
    have he := herr n (hJ₁ (hK hn.1))
    rw [hdiag n hn.1, if_neg hn.2] at he
    have hd := happ n (hK hn.1)
    change |M n + 2*a| < 3*δ
    rw [abs_lt] at he hd ⊢
    constructor <;> linarith [he.1, he.2, hd.1, hd.2]
  · intro n hn
    have he := herr n hn.1
    have hz : splitterRow (μ n) K σ n = 0 := Set.indicator_of_notMem hn.2 _
    rw [hz, sub_zero] at he
    exact he.trans (by linarith)

/-- Rosenthal control and diagonal approximation are retained as witnesses for
the subsequent choices in Remark 4.8 and the simultaneous recursion. -/
theorem three_level_selection_control (C : Set ℕ) (μ : ℕ → lp (fun _ : Point => ℝ) 1)
    (hC : C.Infinite) (hμ : Admissible μ) :
    ∃ (J₀ J₁ : Set ℕ) (a δ : ℝ), J₁ ⊆ J₀ ∧ J₀ ⊆ C ∧
      J₁.Infinite ∧ (J₀ \ J₁).Infinite ∧
      (⨅ n, |μ n (n, false)|) ≤ a ∧ 0 < δ ∧
      δ < (⨅ n, |μ n (n, false)|) / 11 ∧
      (∀ n ∈ J₀, (∑' k : ↥(J₀ \ {n}), fibreWeight (μ n) k.val) < δ) ∧
      (∀ n ∈ J₁, |(|μ n (n, false)|) - a| < δ) := by
  let b : ℝ := ⨅ n, |μ n (n, false)|
  have hb : 0 < b := (positive_diagonal_iff μ).mp hμ.2.2
  have hbb : BddBelow (Set.range fun n => |μ n (n, false)|) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact abs_nonneg _⟩
  let δ := b / 22
  have hδ : 0 < δ := div_pos hb (by norm_num)
  obtain ⟨J₀, hJ₀C, hJ₀, hsmall⟩ := atomic_rosenthal_selection μ hμ.1 C hC δ hδ
  obtain ⟨J₁, a, hJ₁J₀, hJ₁, hdiff, ha, happ⟩ :=
    ThesisCommon.bounded_sequence_uniform_infinite_subset
      (fun n => |μ n (n, false)|) b
      (fun n => ⟨ciInf_le hbb n, (abs_coordinate_le_norm (μ n) n).trans (hμ.1 n)⟩)
      J₀ hJ₀ δ hδ
  exact ⟨J₀, J₁, a, δ, hJ₁J₀, hJ₀C, hJ₁, hdiff, ha, hδ,
    by dsimp [δ]; linarith, hsmall, happ⟩

theorem three_level_selection : Lemma_4_7 := by
  classical
  intro C μ hC hμ
  obtain ⟨J₀, J₁, a, δ, hJ₁J₀, hJ₀C, hJ₁, hJ₀diff, ha, hδ, hδsmall, hsmall, happ⟩ :=
    three_level_selection_control C μ hC hμ
  obtain ⟨J₂, hJ₂J₁, hJ₂, hJ₁diff⟩ := ThesisCommon.infinite_coinfinite_subset J₁ hJ₁
  let σ := levelChoice μ J₂
  let Z := graphSplitter J₁ σ
  exact ⟨J₀, J₁, J₂, Z, a, δ, hJ₂J₁, hJ₁J₀, hJ₀C, hJ₂, hJ₁diff, hJ₀diff,
    graphSplitter_splits J₁ σ, ha, hδ, hδsmall,
    three_level_bounds_of_control μ hμ.2.1 J₀ J₁ hJ₁J₀ a δ hδ hsmall happ
      J₁ J₂ Set.Subset.rfl hJ₂J₁⟩

end SigmaNonprimarity
