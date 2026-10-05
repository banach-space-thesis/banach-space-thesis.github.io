import ThesisCommon.Analysis.GowersMaureyForms

/-! Rapidly increasing sequences for the actual constructed norm, and the
first RIS functional estimate (Gowers--Maurey, Section 2, Lemma 1).
The proof uses only the indicated size, norm and separation clauses; the
stronger first-size cutoff is retained in the genuine RIS definition. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def prefixSum {N : ℕ} (x : Fin N → C00 𝕜) (i : Fin N) : C00 𝕜 :=
  ∑ j ∈ Finset.univ.filter (· < i), x j

/-- Source RIS data specialised to f(t)=log₂(t+1). Its inverse is 2^t-1,
and its derivative at 1 is 1/(2 log 2). The first cutoff is required for
every size, equivalently for the first size because the sizes increase. -/
structure RISData (D : ConstructionData 𝕜) {N : ℕ} (ε : ℝ) (x : Fin N → C00 𝕜) where
  epsilon_pos : 0 < ε
  epsilon_le_one : ε ≤ 1
  successive : Successive x
  size : Fin N → ℕ
  size_strict : StrictMono size
  size_pos : ∀ i, 0 < size i
  first_large : ∀ i, (4 * N * Real.log 2) * ((2 : ℝ) ^ ((N : ℝ)^2 / ε^2) - 1) < size i
  norm_bound : ∀ i, intervalNorm D (size i) (x i) ≤ 1
  spacing : ∀ i, 0 < i.val →
    ((supportInterval (prefixSum x i)).set.card : ℝ) <
      ε * Real.sqrt (logarithmicWeight (size i))

def IsRIS (D : ConstructionData 𝕜) {N : ℕ} (ε : ℝ) (x : Fin N → C00 𝕜) : Prop :=
  Nonempty (RISData D ε x)

theorem logarithmicWeight_mono_nat {m n : ℕ} (h : m ≤ n) :
    logarithmicWeight m ≤ logarithmicWeight n := by
  unfold logarithmicWeight
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right h 1

theorem successive_partial_sum_coordinate_bound {N : ℕ} {x : Fin N → C00 𝕜}
    (hx : Successive x) (hbound : ∀ i n, ‖x i n‖ ≤ 1) (s : Finset (Fin N)) (n : ℕ) :
    ‖(∑ i ∈ s, x i) n‖ ≤ 1 := by
  classical
  rw [Finsupp.finset_sum_apply]
  by_cases hex : ∃ j ∈ s, x j n ≠ 0
  · obtain ⟨j, hj, hjn⟩ := hex
    rw [Finset.sum_eq_single j]
    · exact hbound j n
    · intro i _ hij
      by_contra hi
      exact Finset.disjoint_left.mp (hx.disjoint hij)
        (Finsupp.mem_support_iff.mpr hi) (Finsupp.mem_support_iff.mpr hjn)
    · exact fun h => False.elim (h hj)
  · have hz : ∀ j ∈ s, x j n = 0 := by simpa using hex
    simp [Finset.sum_eq_zero hz]

theorem mass_le_range_card {x : C00 𝕜} (hx : ∀ n, ‖x n‖ ≤ 1) :
    mass x ≤ ((supportInterval x).set.card : ℝ) := by
  rw [mass_eq]
  calc
    ∑ n ∈ x.support, ‖x n‖ ≤ ∑ _n ∈ x.support, (1 : ℝ) :=
      Finset.sum_le_sum fun n _ => hx n
    _ = (x.support.card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast Finset.card_le_card (support_subset_supportInterval x)

theorem sum_eq_prefix_add_middle_add_suffix {N : ℕ} (x : Fin N → C00 𝕜) (i : Fin N) :
    (∑ j, x j) = prefixSum x i + x i + ∑ j ∈ Finset.univ.filter (i < ·), x j := by
  classical
  calc
    _ = ∑ j, ((if j < i then x j else 0) + (if j = i then x j else 0) +
        (if i < j then x j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      rcases lt_trichotomy j i with h | rfl | h
      · simp [h, ne_of_lt h, not_lt.mpr h.le]
      · simp
      · simp [h, ne_of_gt h, not_lt.mpr h.le]
    _ = _ := by simp [prefixSum, Finset.sum_add_distrib, Finset.sum_filter]

theorem RISData.vector_norm_le_one {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (i : Fin N) : implicitNorm D (x i) ≤ 1 :=
  (implicitNorm_le_intervalNorm D (h.size_pos i) (x i)).trans (h.norm_bound i)

theorem RISData.prefix_mass_le {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (i : Fin N) :
    mass (prefixSum x i) ≤ ε * Real.sqrt (logarithmicWeight (h.size i)) := by
  by_cases hi : 0 < i.val
  · apply (mass_le_range_card _).trans (h.spacing i hi).le
    exact successive_partial_sum_coordinate_bound h.successive
      (fun j n => (coordinate_le_implicitNorm D (x j) n).trans (h.vector_norm_le_one j)) _
  · have hz : i.val = 0 := by omega
    have he : Finset.univ.filter (· < i) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hj
      have := Fin.lt_def.mp hj
      omega
    simp only [prefixSum, he, Finset.sum_empty, map_zero]
    exact mul_nonneg h.epsilon_pos.le (Real.sqrt_nonneg _)

/-- The source's Lemma 1 estimate. Only √f(k)≤weight is needed from g. -/
theorem RISData.form_bound {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) {k : ℕ} (hk : 2 ≤ k)
    {weight : ℝ} (hw : Real.sqrt (logarithmicWeight k) ≤ weight)
    {a : C00 𝕜} (ha : IsForm D k weight a) :
    ‖pairing a (∑ i, x i)‖ ≤ ε + 1 + (N : ℝ) / Real.sqrt (logarithmicWeight k) := by
  classical
  have hf : 0 < logarithmicWeight k := lt_of_lt_of_le zero_lt_one
    (one_le_logarithmicWeight (by omega))
  have hs : 0 < Real.sqrt (logarithmicWeight k) := Real.sqrt_pos.mpr hf
  have hwpos : 0 < weight := hs.trans_le hw
  have hinv : weight⁻¹ ≤ (Real.sqrt (logarithmicWeight k))⁻¹ := inv_le_inv₀ hwpos hs |>.2 hw
  have hlate : ∀ j, k ≤ h.size j → ‖pairing a (x j)‖ ≤ (Real.sqrt (logarithmicWeight k))⁻¹ := by
    intro j hj
    have hb := (intervalNorm_mono D hj (x j)).trans (h.norm_bound j)
    exact (ha.intervalNorm_bound hwpos _).trans
      ((mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hwpos.le)).trans (by simpa using hinv))
  let early := Finset.univ.filter (fun i => h.size i < k)
  by_cases he : early.Nonempty
  · let i := early.max' he
    have hi : i ∈ early := Finset.max'_mem _ he
    have hik : h.size i < k := (Finset.mem_filter.mp hi).2
    have hjlate : ∀ j, i < j → k ≤ h.size j := by
      intro j hij
      by_contra hj
      have hm : j ∈ early := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      exact (not_lt_of_ge (Finset.le_max' _ _ hm)) hij
    have hpref : ‖pairing a (prefixSum x i)‖ ≤ ε := by
      have hsmono : Real.sqrt (logarithmicWeight (h.size i)) ≤ weight :=
        (Real.sqrt_le_sqrt (logarithmicWeight_mono_nat hik.le)).trans hw
      calc
        _ ≤ weight⁻¹ * mass (prefixSum x i) := ha.mass_bound hwpos _
        _ ≤ weight⁻¹ * (ε * Real.sqrt (logarithmicWeight (h.size i))) :=
          mul_le_mul_of_nonneg_left (h.prefix_mass_le i) (inv_nonneg.mpr hwpos.le)
        _ ≤ weight⁻¹ * (ε * weight) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsmono h.epsilon_pos.le) (inv_nonneg.mpr hwpos.le)
        _ = ε := by field_simp
    have hmid : ‖pairing a (x i)‖ ≤ 1 := (ha.1 _).trans (h.vector_norm_le_one i)
    have htail : ‖pairing a (∑ j ∈ Finset.univ.filter (i < ·), x j)‖ ≤
        (N : ℝ) / Real.sqrt (logarithmicWeight k) := by
      rw [map_sum]
      calc
        _ ≤ ∑ j ∈ Finset.univ.filter (i < ·), ‖pairing a (x j)‖ := norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.univ.filter (i < ·), (Real.sqrt (logarithmicWeight k))⁻¹ :=
          Finset.sum_le_sum fun j hj => hlate j (hjlate j (Finset.mem_filter.mp hj).2)
        _ ≤ ∑ _j : Fin N, (Real.sqrt (logarithmicWeight k))⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => inv_nonneg.mpr hs.le)
        _ = _ := by simp [div_eq_mul_inv]
    rw [sum_eq_prefix_add_middle_add_suffix x i, map_add, map_add]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hpref hmid)) htail)
  · have hall : ∀ j, k ≤ h.size j := by
      intro j
      by_contra hj
      exact he ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    rw [map_sum]
    have hb : ‖∑ j, pairing a (x j)‖ ≤ (N : ℝ) / Real.sqrt (logarithmicWeight k) := by
      calc
        _ ≤ ∑ j, ‖pairing a (x j)‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin N, (Real.sqrt (logarithmicWeight k))⁻¹ :=
          Finset.sum_le_sum fun j _ => hlate j (hall j)
        _ = _ := by simp [div_eq_mul_inv]
    linarith [h.epsilon_pos]

end ThesisCommon.GowersMaurey
