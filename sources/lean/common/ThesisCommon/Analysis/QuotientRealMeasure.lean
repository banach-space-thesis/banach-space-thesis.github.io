import ThesisCommon.Analysis.InfinityQuotientEvaluation
import ThesisCommon.Analysis.InfiniteSubsetStabilization

/-! Bounded finitely additive quotient-valued measures modulo finite sets,
and the local upper envelopes used in Drewnowski--Roberts Lemma 2.3. -/
noncomputable section
open Filter Set
namespace ThesisCommon

structure QuotientRealMeasure where
  value : Set ℕ → InfinityCZeroQuotient ℝ
  empty : value ∅ = 0
  union : ∀ A B, Disjoint A B → value (A ∪ B) = value A + value B
  remove_finite : ∀ A K, K.Finite → value (A \ K) = value A
  bound : ℝ
  norm_le : ∀ A, ‖value A‖ ≤ bound

namespace QuotientRealMeasure
instance : CoeFun QuotientRealMeasure (fun _ => Set ℕ → InfinityCZeroQuotient ℝ) := ⟨value⟩

def neg (μ : QuotientRealMeasure) : QuotientRealMeasure where
  value A := -μ A
  empty := by simp [μ.empty]
  union A B h := by simp [μ.union A B h, add_comm]
  remove_finite A K h := by rw [μ.remove_finite A K h]
  bound := μ.bound
  norm_le A := by simpa only [norm_neg] using μ.norm_le A

@[simp] theorem neg_apply (μ : QuotientRealMeasure) (A : Set ℕ) : μ.neg A = -μ A := rfl

def eval (μ : QuotientRealMeasure) (A : Set ℕ) (U : FreeNatUltrafilter) : ℝ :=
  infinityQuotientEval (𝕜 := ℝ) U (μ A)

@[simp] theorem eval_empty (μ : QuotientRealMeasure) (U : FreeNatUltrafilter) :
    μ.eval ∅ U = 0 := by simp [eval, μ.empty]

@[simp] theorem eval_neg (μ : QuotientRealMeasure) (A : Set ℕ) (U : FreeNatUltrafilter) :
    μ.neg.eval A U = -μ.eval A U := by simp [eval]

theorem eval_union (μ : QuotientRealMeasure) {A B : Set ℕ} (h : Disjoint A B)
    (U : FreeNatUltrafilter) : μ.eval (A ∪ B) U = μ.eval A U + μ.eval B U := by
  simp only [eval, μ.union A B h, map_add]

theorem eval_sdiff (μ : QuotientRealMeasure) {A B : Set ℕ} (h : B ⊆ A)
    (U : FreeNatUltrafilter) : μ.eval (A \ B) U = μ.eval A U - μ.eval B U := by
  have he := μ.eval_union (A := A \ B) (B := B) disjoint_sdiff_left U
  have hs : A \ B ∪ B = A := by
    ext n
    constructor
    · rintro (⟨hn, _⟩ | hn)
      · exact hn
      · exact h hn
    · intro hn
      by_cases hb : n ∈ B
      · exact Or.inr hb
      · exact Or.inl ⟨hn, hb⟩
  rw [hs] at he
  linarith

def localValues (μ : QuotientRealMeasure) (A : Set ℕ) : Set ℝ :=
  {r | ∃ F : Set ℕ, F ⊆ A ∧ ∃ U : FreeNatUltrafilter, A ∈ U ∧ μ.eval F U = r}

def upper (μ : QuotientRealMeasure) (A : Set ℕ) : ℝ := sSup (μ.localValues A)

theorem localValues_bddAbove (μ : QuotientRealMeasure) (A : Set ℕ) :
    BddAbove (μ.localValues A) := by
  refine ⟨μ.bound, ?_⟩
  rintro r ⟨F, _, U, _, rfl⟩
  exact (le_abs_self _).trans ((norm_infinityQuotientEval_apply_le U (μ F)).trans (μ.norm_le F))

theorem zero_mem_localValues (μ : QuotientRealMeasure) {A : Set ℕ} (hA : A.Infinite) :
    0 ∈ μ.localValues A := by
  obtain ⟨U, hU⟩ := FreeNatUltrafilter.exists_mem hA
  exact ⟨∅, empty_subset A, U, hU, μ.eval_empty U⟩

theorem upper_nonneg (μ : QuotientRealMeasure) {A : Set ℕ} (hA : A.Infinite) :
    0 ≤ μ.upper A := le_csSup (μ.localValues_bddAbove A) (μ.zero_mem_localValues hA)

theorem eval_le_upper (μ : QuotientRealMeasure) {F A : Set ℕ} (hFA : F ⊆ A)
    (U : FreeNatUltrafilter) (hU : A ∈ U) : μ.eval F U ≤ μ.upper A :=
  le_csSup (μ.localValues_bddAbove A) ⟨F, hFA, U, hU, rfl⟩

theorem upper_mono (μ : QuotientRealMeasure) {A B : Set ℕ} (hA : A.Infinite)
    (hAB : A ⊆ B) : μ.upper A ≤ μ.upper B := by
  apply csSup_le_csSup (μ.localValues_bddAbove B) ⟨0, μ.zero_mem_localValues hA⟩
  rintro r ⟨F, hF, U, hU, hr⟩
  exact ⟨F, hF.trans hAB, U, Filter.mem_of_superset hU hAB, hr⟩

theorem upper_remove_finite (μ : QuotientRealMeasure) (A K : Set ℕ) (hK : K.Finite) :
    μ.upper (A \ K) = μ.upper A := by
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨F, hF, U, hU, hr⟩
    exact ⟨F, hF.trans diff_subset, U, Filter.mem_of_superset hU diff_subset, hr⟩
  · rintro ⟨F, hF, U, hU, hr⟩
    refine ⟨F \ K, diff_subset_diff_left hF, U, ?_, ?_⟩
    · exact Filter.inter_mem hU (U.property hK.compl_mem_cofinite)
    · simpa only [eval, μ.remove_finite F K hK] using hr

theorem exists_eval_gt (μ : QuotientRealMeasure) {A : Set ℕ} (hA : A.Infinite)
    {a : ℝ} (ha : a < μ.upper A) :
    ∃ F : Set ℕ, F ⊆ A ∧ ∃ U : FreeNatUltrafilter, A ∈ U ∧ a < μ.eval F U := by
  obtain ⟨r, ⟨F, hF, U, hU, rfl⟩, hr⟩ :=
    exists_lt_of_lt_csSup ⟨0, μ.zero_mem_localValues hA⟩ ha
  exact ⟨F, hF, U, hU, hr⟩

theorem exists_stable_upper (μ : QuotientRealMeasure) {A : Set ℕ} (hA : A.Infinite) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
      ∀ C : Set ℕ, C.Infinite → C ⊆ B → μ.upper C = μ.upper B := by
  apply infinite_subset_stabilization_of_finite_removal μ.upper hA
  · intro E F hE _ _ _ hEF
    exact μ.upper_mono hE hEF
  · intro E _ _ K hK
    exact μ.upper_remove_finite E K hK
  · refine ⟨0, ?_⟩
    rintro r ⟨B, hB, _, rfl⟩
    exact μ.upper_nonneg hB

theorem localize (μ : QuotientRealMeasure) (F : Set ℕ) (U : FreeNatUltrafilter)
    {A : Set ℕ} (hA : A ∈ U) {a : ℝ} (ha : a < μ.eval F U) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧
      ∀ V : FreeNatUltrafilter, B ∈ V → a < μ.eval F V :=
  infinityQuotient_real_localize (μ F) U hA ha

end QuotientRealMeasure
end ThesisCommon
