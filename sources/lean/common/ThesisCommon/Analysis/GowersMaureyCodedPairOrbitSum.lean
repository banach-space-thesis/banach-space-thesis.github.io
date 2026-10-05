import ThesisCommon.Analysis.GowersMaureyCodedPairMismatch

/-! For a fixed spread, at most one constructed pair lies between its own
size and the next code cutoff. All earlier pairs vanish exactly and all
later pairs satisfy the selected small-orbit bound. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
variable {T : Y →L[𝕜] ShiftSpace D} {ε η : ℝ} {G : C00 𝕜 → ℝ} {k : ℕ}

theorem CodedDetectingFamily.size_ge_length (hk : 0 < k)
    (d : CodedDetectingFamily T ε η (k-1) k G) (i : Fin k) : k ≤ (d.pair i).size := by
  have hi := d.index_ge_seed i
  have hj : 2*(d.pair i).index+1 ≤ D.j (2*(d.pair i).index+1) := D.j_strict.id_le _
  change k ≤ D.j (2*(d.pair i).index+1)
  omega

theorem CodedDetectingFamily.own_pairing_le_four
    (d : CodedDetectingFamily T ε η (k-1) k G) (i : Fin k) (m n : ℕ) :
    ‖pairing (d.pair i).functional (spread m n (d.pair i).vector)‖ ≤ 4 :=
  ((d.pair i).averaged.dualUnit _).trans
    ((implicitNorm_spread_le D m n _).trans (d.pair i).norm_bound)

theorem CodedDetectingFamily.exists_one_orbit_exception (hk : 0 < k)
    (d : CodedDetectingFamily T ε η (k-1) k G) (m n : ℕ) :
    ∃ j : Fin k, ∀ i, i ≠ j →
      ‖pairing (d.pair i).functional (spread m n (d.pair i).vector)‖ ≤
        (‖T‖+1)/(k : ℝ)^2 := by
  classical
  have hkp : 0 < (k : ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hk)
  have hsmall (i : Fin k) (hz : (m,n) ∈ spreadParameterSquare (d.pair i).size) :
      ‖pairing (d.pair i).functional (spread m n (d.pair i).vector)‖ ≤ (‖T‖+1)/(k : ℝ)^2 := by
    apply ((d.pair i).orbit_small (m,n) hz).trans
    apply div_le_div_of_nonneg_left (by positivity) hkp
    exact pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast d.size_ge_length hk i) 2
  let s := Finset.univ.filter (fun i => (d.pair i).size < max m n)
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hj : j ∈ s := Finset.max'_mem _ _
    refine ⟨j,?_⟩
    intro i hij
    by_cases hi : i ∈ s
    · have hij' : i < j := lt_of_le_of_ne (Finset.le_max' _ i hi) hij
      have hout : (m,n) ∉ spreadParameterSquare (d.pair j).size := by
        intro hz
        have hm := (mem_spreadParameterSquare _ _ _).mp hz
        have hj' := (Finset.mem_filter.mp hj).2
        omega
      rw [pairing_spread_eq_zero_of_cutoff _ _ (d.cutoff i j hij').le m n hout,norm_zero]
      positivity
    · apply hsmall i
      have hh : max m n ≤ (d.pair i).size := by
        have hh := not_lt.mp (show ¬ (d.pair i).size < max m n from fun h =>
          hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i,h⟩))
        exact hh
      exact (mem_spreadParameterSquare _ _ _).mpr ⟨(le_max_left _ _).trans hh,(le_max_right _ _).trans hh⟩
  · refine ⟨⟨0,hk⟩,fun i _ => hsmall i ?_⟩
    have hh : max m n ≤ (d.pair i).size := by
      by_contra h
      exact hs ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,lt_of_not_ge h⟩⟩
    exact (mem_spreadParameterSquare _ _ _).mpr ⟨(le_max_left _ _).trans hh,(le_max_right _ _).trans hh⟩

theorem CodedDetectingFamily.own_diagonal_sum_le (hk : 0 < k)
    (d : CodedDetectingFamily T ε η (k-1) k G) (m n : ℕ) :
    (∑ i, ‖pairing (d.pair i).functional (spread m n (d.pair i).vector)‖) ≤ ‖T‖+5 := by
  classical
  obtain ⟨j,hj⟩ := d.exists_one_orbit_exception hk m n
  let b (i : Fin k) := ‖pairing (d.pair i).functional (spread m n (d.pair i).vector)‖
  have he := Finset.sum_erase_add Finset.univ b (Finset.mem_univ j)
  have hb : (∑ i ∈ Finset.univ.erase j, b i) ≤ (k : ℝ)*((‖T‖+1)/(k : ℝ)^2) := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ.erase j, (‖T‖+1)/(k : ℝ)^2 :=
        Finset.sum_le_sum (fun i hi => hj i (Finset.ne_of_mem_erase hi))
      _ ≤ ∑ _i : Fin k, (‖T‖+1)/(k : ℝ)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => by positivity)
      _ = _ := by simp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnum : (k : ℝ)*((‖T‖+1)/(k : ℝ)^2) ≤ ‖T‖+1 := by
    calc
      _ = (‖T‖+1)/k := by field_simp
      _ ≤ ‖T‖+1 := (div_le_iff₀ hkR).mpr (by
        nlinarith [norm_nonneg T])
  have hbj := d.own_pairing_le_four j m n
  change (∑ i, b i) ≤ ‖T‖+5
  linarith

end ThesisCommon.GowersMaurey
