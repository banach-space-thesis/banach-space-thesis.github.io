import ThesisCommon.Analysis.GowersMaureyIntervalNorms

/-! An interval partially cuts at most two members of a successive finite
family. The resulting boundary error is bounded in the actual implicit norm,
including zero vectors and empty intervals. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def intervalBoundaryBlocks {k : ℕ} (x : Fin k → C00 𝕜) (E : Interval) : Finset (Fin k) :=
  Finset.univ.filter (fun i => restrict E (x i) ≠ 0 ∧ ¬ (x i).support ⊆ E.set)

def intervalFullBlocks {k : ℕ} (x : Fin k → C00 𝕜) (E : Interval) : Finset (Fin k) :=
  Finset.univ.filter (fun i => (x i).support ⊆ E.set)

theorem Successive.intervalBoundaryBlocks_card_le_two {k : ℕ} {x : Fin k → C00 𝕜}
    (hx : Successive x) (E : Interval) : (intervalBoundaryBlocks x E).card ≤ 2 := by
  classical
  let L := Finset.univ.filter (fun i => ∃ a ∈ (x i).support, ∃ b ∈ (x i).support,
    a < E.first ∧ E.first ≤ b)
  let R := Finset.univ.filter (fun i => ∃ a ∈ (x i).support, ∃ b ∈ (x i).support,
    a ≤ E.last ∧ E.last < b)
  have hL : L.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨a,ha,b,hb,hab⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨c,hc,d,hd,hcd⟩ := (Finset.mem_filter.mp hj).2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hbc := hx i j h b hb c hc
      omega
    · have hda := hx j i h d hd a ha
      omega
  have hR : R.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨a,ha,b,hb,hab⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨c,hc,d,hd,hcd⟩ := (Finset.mem_filter.mp hj).2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hbc := hx i j h b hb c hc
      omega
    · have hda := hx j i h d hd a ha
      omega
  have hsub : intervalBoundaryBlocks x E ⊆ L ∪ R := by
    intro i hi
    obtain ⟨hne,hnot⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨b,hb⟩ := Finsupp.support_nonempty_iff.mpr hne
    have hbn := Finsupp.mem_support_iff.mp hb
    have hbE : b ∈ E.set := by
      by_contra hh
      exact hbn (by simp [restrict_apply,hh])
    have hbx : b ∈ (x i).support := Finsupp.mem_support_iff.mpr (by
      simpa only [restrict_apply,if_pos hbE] using hbn)
    obtain ⟨a,ha,haE⟩ := Finset.not_subset.mp hnot
    have hb' := Finset.mem_Icc.mp hbE
    have ha' : a < E.first ∨ E.last < a := by
      simp only [Interval.set,Finset.mem_Icc] at haE
      omega
    rcases ha' with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ i,⟨a,ha,b,hbx,h,hb'.1⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ i,⟨b,hbx,a,ha,hb'.2,h⟩⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

theorem restrict_sum_eq_full_add_boundary {k : ℕ} (x : Fin k → C00 𝕜) (E : Interval) :
    restrict E (∑ i, x i) = (∑ i ∈ intervalFullBlocks x E, x i) +
      ∑ i ∈ intervalBoundaryBlocks x E, restrict E (x i) := by
  classical
  simp only [map_sum,intervalFullBlocks,intervalBoundaryBlocks,Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hsub : (x i).support ⊆ E.set
  · have he : restrict E (x i) = x i := by
      ext j
      by_cases hj : j ∈ E.set
      · simp [restrict_apply,hj]
      · have hz : x i j = 0 := Finsupp.notMem_support_iff.mp (fun hh => hj (hsub hh))
        simp [restrict_apply,hj,hz]
    simp [hsub,he]
  · by_cases hzero : restrict E (x i) = 0 <;> simp [hsub,hzero]

theorem Successive.interval_boundary_norm_le {D : ConstructionData 𝕜}
    {k : ℕ} {x : Fin k → C00 𝕜} (hx : Successive x)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ i, implicitNorm D (x i) ≤ C) (E : Interval) :
    implicitNorm D (restrict E (∑ i, x i) - ∑ i ∈ intervalFullBlocks x E, x i) ≤ 2*C := by
  rw [restrict_sum_eq_full_add_boundary,add_sub_cancel_left]
  calc
    _ ≤ ∑ i ∈ intervalBoundaryBlocks x E, implicitNorm D (restrict E (x i)) :=
      seminorm_sum_le _ _ _
    _ ≤ ∑ _i ∈ intervalBoundaryBlocks x E, C := Finset.sum_le_sum
      (fun i _ => (implicitNorm_restrict_le D E _).trans (hbound i))
    _ = ((intervalBoundaryBlocks x E).card : ℝ)*C := by simp
    _ ≤ 2*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hx.intervalBoundaryBlocks_card_le_two E) hC

end ThesisCommon.GowersMaurey
