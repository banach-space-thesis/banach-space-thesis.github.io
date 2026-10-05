import ThesisCommon.Analysis.GowersMaureyRISConstruction
import ThesisCommon.Analysis.GowersMaureyFormIntervals

/-! A fixed successive finite family whose vectors have all interval norms
at most one is an RIS for every positive epsilon at most one. The sizes
are genuinely chosen; the vectors are not replaced or approximated. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem isRIS_of_all_intervalNorm_le_one (D : ConstructionData 𝕜)
    {N : ℕ} {x : Fin N → C00 𝕜} (hx : Successive x)
    (hbound : ∀ i n, 0 < n → intervalNorm D n (x i) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : IsRIS D ε x := by
  classical
  let A := (4 * N * Real.log 2) * ((2 : ℝ)^((N : ℝ)^2 / ε^2) - 1)
  let K : ℕ := Finset.univ.sup (fun i : Fin N => (supportInterval (prefixSum x i)).set.card)
  have hg : Tendsto (fun n : ℕ => logarithmicWeight n) atTop atTop :=
    tendsto_logarithmicWeight_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop,
      ((K : ℝ) / ε)^2 < logarithmicWeight n :=
    hg.eventually (eventually_gt_atTop _)
  obtain ⟨B, hB⟩ := eventually_atTop.mp hevent
  obtain ⟨q, hq⟩ := exists_nat_gt (max A (B : ℝ))
  have hqA : A < (q : ℝ) := (le_max_left _ _).trans_lt hq
  have hqB : B < q := by exact_mod_cast ((le_max_right _ _).trans_lt hq)
  have hqp : 0 < q := by omega
  refine ⟨{
    epsilon_pos := hε
    epsilon_le_one := hε1
    successive := hx
    size := fun i => q + i.val
    size_strict := by intro i j hij; change q + i.val < q + j.val; exact Nat.add_lt_add_left hij q
    size_pos := fun i => by omega
    first_large := ?_
    norm_bound := fun i => hbound i _ (by omega)
    spacing := ?_
  }⟩
  · intro i
    change A < (q + i.val : ℕ)
    exact hqA.trans_le (by exact_mod_cast Nat.le_add_right q i.val)
  · intro i _
    have hlarge := hB (q + i.val) (by omega)
    have hroot := (Real.lt_sqrt (div_nonneg (by positivity : (0 : ℝ) ≤ K) hε.le)).mpr hlarge
    have hKε : (K : ℝ) < ε * Real.sqrt (logarithmicWeight ((q + i.val : ℕ) : ℝ)) := by
      have hh := (div_lt_iff₀ hε).mp hroot
      simpa only [mul_comm] using hh
    have hcard : (supportInterval (prefixSum x i)).set.card ≤ K :=
      Finset.le_sup (f := fun i : Fin N => (supportInterval (prefixSum x i)).set.card) (Finset.mem_univ i)
    exact (show ((supportInterval (prefixSum x i)).set.card : ℝ) ≤ K by exact_mod_cast hcard).trans_lt hKε

theorem intervalNorm_single_le (D : ConstructionData 𝕜) (N k : ℕ) (c : 𝕜) :
    intervalNorm D N (Finsupp.single k c) ≤ ‖c‖ := by
  classical
  rw [intervalNorm, Seminorm.sSup_apply (intervalSums_bddAbove D N)]
  apply ciSup_le
  rintro ⟨_, I, rfl⟩
  change intervalSum D I (Finsupp.single k c) ≤ _
  rw [intervalSum_apply]
  by_cases hex : ∃ i, k ∈ (I.interval i).set
  · obtain ⟨i, hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · simp only [restrict_single, if_pos hi, implicitNorm_single, le_refl]
    · intro j _ hji
      have hj : k ∉ (I.interval j).set := fun hj =>
        Finset.disjoint_left.mp (I.disjoint hji) hj hi
      simp only [restrict_single, if_neg hj, map_zero]
    · simp
  · have hz : ∀ i, k ∉ (I.interval i).set := by simpa only [not_exists] using hex
    have hh : (∑ i, implicitNorm D (restrict (I.interval i) (Finsupp.single k c))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp only [restrict_single, if_neg (hz i), map_zero]
    rw [hh]
    exact norm_nonneg c

theorem isRIS_single (D : ConstructionData 𝕜) {N : ℕ} {a : Fin N → ℕ}
    (ha : StrictMono a) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IsRIS D ε (fun i => Finsupp.single (a i) (1 : 𝕜)) := by
  apply isRIS_of_all_intervalNorm_le_one D ?_ ?_ hε hε1
  · intro i j hij s hs t ht
    simp only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hs ht
    simpa only [hs, ht] using ha hij
  · intro i n _
    simpa only [norm_one] using intervalNorm_single_le D n (a i) (1 : 𝕜)

end ThesisCommon.GowersMaurey
