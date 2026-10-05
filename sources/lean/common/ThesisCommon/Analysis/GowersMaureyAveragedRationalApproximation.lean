import ThesisCommon.Analysis.GowersMaureyDualRationalApproximation

/-! Arbitrarily close Gaussian-rational averaged functionals, with exactly the
same averaging parameter and with support contained in the original support.
The proof approximates contracted divided blocks and verifies their dual-unit
inequality, rather than assuming rational density of the averaged class. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem Successive.support_subset_real_smul_sum {N : ℕ} {z : Fin N → C00 𝕜}
    (hz : Successive z) {r : ℝ} (hr : r ≠ 0) (i : Fin N) :
    (z i).support ⊆ (r • ∑ j, z j).support := by
  classical
  intro n hn
  have he : (∑ j, z j) n = z i n := by
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · intro j _ hji
      apply Finsupp.notMem_support_iff.mp
      intro hj
      exact Finset.disjoint_left.mp (hz.disjoint hji) hj hn
    · simp
  apply Finsupp.mem_support_iff.mpr
  rw [Finsupp.smul_apply, he]
  exact smul_ne_zero hr (Finsupp.mem_support_iff.mp hn)

theorem AveragedFunctional.exists_rational_near {D : ConstructionData 𝕜}
    {N : ℕ} {a : C00 𝕜} (ha : AveragedFunctional (implicitNorm D) N a)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : C00 𝕜, AveragedFunctional (implicitNorm D) N b ∧
      RationalUnitSequence b ∧ b.support ⊆ a.support ∧ mass (b-a) < δ := by
  classical
  obtain ⟨hN,z,hz,hu,he⟩ := ha
  let f : ℝ := logarithmicWeight N
  have hf : 0 < f := zero_lt_one.trans_le (one_le_logarithmicWeight hN)
  change a = f⁻¹ • ∑ i, z i at he
  obtain ⟨m,hm⟩ := ((tendsto_codingContraction_seminorm_error (mass (𝕜 := 𝕜)) a).eventually
    (gt_mem_nhds (show (0 : ℝ) < δ/2 by positivity))).exists
  let q : ℝ := codingContraction m
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    exact_mod_cast (codingContraction_pos m).le
  have hq1 : q < 1 := by
    dsimp only [q]
    exact_mod_cast codingContraction_lt_one m
  have hqerr : mass (q • a-a) < δ/2 := by
    simpa only [q, RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.ofReal_ratCast] using hm
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let η : ℝ := δ / (2 * N)
  have hη : 0 < η := div_pos hδ (mul_pos (by norm_num) hNreal)
  choose g hg hgs hgerr hgu using fun i =>
    exists_rational_divided_dualUnit_near D (hu i) hq0 hq1 hf hη
  let b : C00 𝕜 := ∑ i, g i
  have hbavg : AveragedFunctional (implicitNorm D) N b := by
    refine ⟨hN,fun i => f • g i,?_,hgu,?_⟩
    · intro i j hij s hs t ht
      exact hz i j hij s (hgs i (Finsupp.support_smul hs))
        t (hgs j (Finsupp.support_smul ht))
    · change b = f⁻¹ • ∑ i, f • g i
      rw [← Finset.smul_sum, smul_smul, inv_mul_cancel₀ hf.ne', one_smul]
  refine ⟨b,hbavg,⟨?_,?_⟩,?_,?_⟩
  · intro n
    change RationalCoordinate ((∑ i, g i) n)
    rw [Finsupp.finset_sum_apply]
    exact RationalCoordinate.sum _ _ (fun i _ => hg i n)
  · intro n
    simpa [implicitNorm_single] using hbavg.dualUnit (Finsupp.single n 1)
  · have hza (i : Fin N) : (z i).support ⊆ a.support := by
      rw [he]
      exact hz.support_subset_real_smul_sum (inv_ne_zero hf.ne') i
    intro n hn
    by_contra hna
    have hg0 (i : Fin N) : g i n = 0 := Finsupp.notMem_support_iff.mp
      (fun hi => hna (hza i (hgs i hi)))
    exact Finsupp.mem_support_iff.mp hn (by simp [b, Finsupp.finset_sum_apply, hg0])
  · have hd : b - q • a = ∑ i, (g i - (q/f) • z i) := by
      rw [Finset.sum_sub_distrib, ← Finset.smul_sum, he, smul_smul]
      simp only [div_eq_mul_inv, b]
    have herror : mass (b-q • a) ≤ δ/2 := by
      rw [hd]
      calc
        _ ≤ ∑ i, mass (g i - (q/f) • z i) := seminorm_sum_le _ _ _
        _ ≤ ∑ _ : Fin N, η := Finset.sum_le_sum (fun i _ => (hgerr i).le)
        _ = δ/2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, η]
          field_simp
    have he' : b-a = (b-q • a)+(q • a-a) := by abel
    rw [he']
    exact (map_add_le_add mass _ _).trans_lt (by linarith)

theorem mass_pos_of_ne_zero {a : C00 𝕜} (ha : a ≠ 0) : 0 < mass a := by
  by_contra h
  have hm : mass a = 0 := le_antisymm (le_of_not_gt h) (apply_nonneg _ _)
  apply ha
  ext n
  exact norm_eq_zero.mp (le_antisymm ((coordinate_le_mass a n).trans_eq hm) (norm_nonneg _))

theorem AveragedFunctional.exists_nonzero_rational_near {D : ConstructionData 𝕜}
    {N : ℕ} {a : C00 𝕜} (ha : AveragedFunctional (implicitNorm D) N a) (ha0 : a ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : C00 𝕜, b ≠ 0 ∧ AveragedFunctional (implicitNorm D) N b ∧
      RationalUnitSequence b ∧ b.support ⊆ a.support ∧ mass (b-a) < δ := by
  obtain ⟨b,hb,hr,hs,he⟩ := ha.exists_rational_near (lt_min hδ (mass_pos_of_ne_zero ha0))
  refine ⟨b,?_,hb,hr,hs,he.trans_le (min_le_left _ _)⟩
  intro hzero
  have he' : mass a < mass a := by
    simpa only [hzero, zero_sub, map_neg_eq_map] using he.trans_le (min_le_right _ _)
  exact he'.false

end ThesisCommon.GowersMaurey
