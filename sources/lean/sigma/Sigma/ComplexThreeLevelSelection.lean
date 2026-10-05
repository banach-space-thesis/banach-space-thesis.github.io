import Sigma.ComplexAtomicSelection

/-! The full complex counterpart of Lemma 4.7 and its restriction-stability
property. This supplies the selection step for a complex construction, not
an identification of that construction with the already built real one. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set
namespace SigmaNonprimarity

theorem complex_positive_diagonal_iff (μ : ℕ → lp (fun _ : Point => ℂ) 1) :
    (∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ ‖μ n (n,false)‖) ↔
      0 < ⨅ n, ‖μ n (n,false)‖ := by
  have hb : BddBelow (Set.range fun n => ‖μ n (n,false)‖) :=
    ⟨0,by rintro _ ⟨n,rfl⟩; exact norm_nonneg _⟩
  constructor
  · rintro ⟨b,hb0,h⟩
    exact hb0.trans_le (le_ciInf h)
  · intro h
    exact ⟨_,h,fun n => ciInf_le hb n⟩

def complexLevelChoice (T : Set ℕ) (n : ℕ) : Bool := if n ∈ T then false else true

theorem complexLevelChoice_diagonal (μ : ℕ → lp (fun _ : Point => ℂ) 1)
    (hμ : ∀ n k, μ n (k,false) = -μ n (k,true)) (T : Set ℕ) (n : ℕ) :
    μ n (n,complexLevelChoice T n) - μ n (n,!(complexLevelChoice T n)) =
      if n ∈ T then 2*μ n (n,false) else -(2*μ n (n,false)) := by
  have hy : μ n (n,true) = -μ n (n,false) := by rw [hμ n n,neg_neg]
  by_cases hn : n ∈ T <;> simp [complexLevelChoice,hn,hy] <;> ring

/-- Both complex signed levels and the zero level persist after shrinking the
retained cylinder, for any further subpartition of its indices. -/
theorem complex_three_level_bounds_of_control (μ : ℕ → lp (fun _ : Point => ℂ) 1)
    (hμ : ∀ n k, μ n (k,false) = -μ n (k,true))
    (J₀ J₁ : Set ℕ) (hJ₁ : J₁ ⊆ J₀) (a : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ∀ n ∈ J₀, (∑' k : ↥(J₀ \ {n}), complexFibreWeight (μ n) k.val) < δ)
    (happ : ∀ n ∈ J₁, ‖μ n (n,false) - a‖ < δ)
    (K T : Set ℕ) (hK : K ⊆ J₁) (hT : T ⊆ K) :
    let Z := graphSplitter K (complexLevelChoice T)
    (∀ n ∈ T, ‖complexMass (μ n) Z - complexMass (μ n) (cylinder K \ Z) - 2*a‖ < 3*δ) ∧
    (∀ n ∈ K \ T, ‖complexMass (μ n) Z - complexMass (μ n) (cylinder K \ Z) + 2*a‖ < 3*δ) ∧
    (∀ n ∈ J₀ \ K, ‖complexMass (μ n) Z - complexMass (μ n) (cylinder K \ Z)‖ < 3*δ) := by
  let σ := complexLevelChoice T
  let Z := graphSplitter K σ
  let M : ℕ → ℂ := fun n => complexMass (μ n) Z - complexMass (μ n) (cylinder K \ Z)
  have herr (n : ℕ) (hn : n ∈ J₀) : ‖M n - complexSplitterRow (μ n) K σ n‖ < δ :=
    (complexMass_splitter_offdiagonal (μ n) K J₀ (hK.trans hJ₁) σ n).trans_lt (hsmall n hn)
  have hdiag (n : ℕ) (hn : n ∈ K) : complexSplitterRow (μ n) K σ n =
      if n ∈ T then 2*μ n (n,false) else -(2*μ n (n,false)) := by
    rw [complexSplitterRow,Set.indicator_of_mem hn]
    exact complexLevelChoice_diagonal μ hμ T n
  refine ⟨?_,?_,?_⟩
  · intro n hn
    have he := herr n (hJ₁ (hK (hT hn)))
    rw [hdiag n (hT hn),if_pos hn] at he
    have hd := happ n (hK (hT hn))
    change ‖M n - 2*a‖ < 3*δ
    have htri : ‖M n - 2*a‖ ≤ ‖M n - 2*μ n (n,false)‖ + 2*‖μ n (n,false)-a‖ := by
      calc
        _ = ‖(M n - 2*μ n (n,false)) + 2*(μ n (n,false)-a)‖ := by congr 1; ring
        _ ≤ ‖M n - 2*μ n (n,false)‖ + ‖2*(μ n (n,false)-a)‖ := norm_add_le _ _
        _ = _ := by simp [norm_mul]
    linarith
  · intro n hn
    have he := herr n (hJ₁ (hK hn.1))
    rw [hdiag n hn.1,if_neg hn.2] at he
    have hd := happ n (hK hn.1)
    change ‖M n + 2*a‖ < 3*δ
    have htri : ‖M n + 2*a‖ ≤ ‖M n - (-(2*μ n (n,false)))‖ + 2*‖μ n (n,false)-a‖ := by
      calc
        _ = ‖(M n - (-(2*μ n (n,false)))) + (-(2*(μ n (n,false)-a)))‖ := by congr 1; ring
        _ ≤ ‖M n - (-(2*μ n (n,false)))‖ + ‖-(2*(μ n (n,false)-a))‖ := norm_add_le _ _
        _ = _ := by simp [norm_mul]
    linarith
  · intro n hn
    have he := herr n hn.1
    have hz : complexSplitterRow (μ n) K σ n = 0 := Set.indicator_of_notMem hn.2 _
    rw [hz,sub_zero] at he
    exact he.trans (by linarith)

theorem complex_three_level_selection_control (C : Set ℕ)
    (μ : ℕ → lp (fun _ : Point => ℂ) 1) (hC : C.Infinite) (hμ : ComplexAdmissible μ) :
    ∃ (J₀ J₁ : Set ℕ) (a : ℂ) (δ : ℝ), J₁ ⊆ J₀ ∧ J₀ ⊆ C ∧
      J₁.Infinite ∧ (J₀ \ J₁).Infinite ∧
      (⨅ n, ‖μ n (n,false)‖) ≤ ‖a‖ ∧ 0 < δ ∧
      δ < (⨅ n, ‖μ n (n,false)‖) / 11 ∧
      (∀ n ∈ J₀, (∑' k : ↥(J₀ \ {n}), complexFibreWeight (μ n) k.val) < δ) ∧
      (∀ n ∈ J₁, ‖μ n (n,false) - a‖ < δ) := by
  let b : ℝ := ⨅ n, ‖μ n (n,false)‖
  have hb : 0 < b := (complex_positive_diagonal_iff μ).mp hμ.2.2
  have hbb : BddBelow (Set.range fun n => ‖μ n (n,false)‖) :=
    ⟨0,by rintro _ ⟨n,rfl⟩; exact norm_nonneg _⟩
  let δ := b / 22
  have hδ : 0 < δ := div_pos hb (by norm_num)
  obtain ⟨J₀,hJ₀C,hJ₀,hsmall⟩ := complex_atomic_rosenthal_selection μ hμ.1 C hC δ hδ
  obtain ⟨J₁,a,hJ₁J₀,hJ₁,hdiff,ha,happ⟩ :=
    complex_bounded_sequence_uniform_infinite_subset (fun n => μ n (n,false)) b
      (fun n => ⟨ciInf_le hbb n,(complex_coordinate_le_norm (μ n) n).trans (hμ.1 n)⟩)
      J₀ hJ₀ δ hδ
  exact ⟨J₀,J₁,a,δ,hJ₁J₀,hJ₀C,hJ₁,hdiff,ha,hδ,
    by dsimp [δ]; linarith,hsmall,happ⟩

/-- All nesting, infinite remainders, splitting and three-level estimates of
the complex Lemma 4.7, without assuming any transfinite construction. -/
theorem complex_three_level_selection (C : Set ℕ) (μ : ℕ → lp (fun _ : Point => ℂ) 1)
    (hC : C.Infinite) (hμ : ComplexAdmissible μ) :
    ∃ (J₀ J₁ J₂ : Set ℕ) (Z : Set Point) (a : ℂ) (δ : ℝ),
      J₂ ⊆ J₁ ∧ J₁ ⊆ J₀ ∧ J₀ ⊆ C ∧ J₂.Infinite ∧
      (J₁ \ J₂).Infinite ∧ (J₀ \ J₁).Infinite ∧ Splits J₁ Z ∧
      (⨅ n, ‖μ n (n,false)‖) ≤ ‖a‖ ∧ 0 < δ ∧
      δ < (⨅ n, ‖μ n (n,false)‖) / 11 ∧
      (∀ n ∈ J₂, ‖complexMass (μ n) Z - complexMass (μ n) (cylinder J₁ \ Z) - 2*a‖ < 3*δ) ∧
      (∀ n ∈ J₁ \ J₂, ‖complexMass (μ n) Z - complexMass (μ n) (cylinder J₁ \ Z) + 2*a‖ < 3*δ) ∧
      (∀ n ∈ J₀ \ J₁, ‖complexMass (μ n) Z - complexMass (μ n) (cylinder J₁ \ Z)‖ < 3*δ) := by
  obtain ⟨J₀,J₁,a,δ,hJ₁J₀,hJ₀C,hJ₁,hJ₀diff,ha,hδ,hδsmall,hsmall,happ⟩ :=
    complex_three_level_selection_control C μ hC hμ
  obtain ⟨J₂,hJ₂J₁,hJ₂,hJ₁diff⟩ := ThesisCommon.infinite_coinfinite_subset J₁ hJ₁
  exact ⟨J₀,J₁,J₂,graphSplitter J₁ (complexLevelChoice J₂),a,δ,
    hJ₂J₁,hJ₁J₀,hJ₀C,hJ₂,hJ₁diff,hJ₀diff,graphSplitter_splits _ _,ha,hδ,hδsmall,
    complex_three_level_bounds_of_control μ hμ.2.1 J₀ J₁ hJ₁J₀ a δ hδ hsmall happ
      J₁ J₂ Set.Subset.rfl hJ₂J₁⟩

end SigmaNonprimarity
