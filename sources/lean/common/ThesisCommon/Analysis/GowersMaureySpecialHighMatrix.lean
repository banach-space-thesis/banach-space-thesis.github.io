import ThesisCommon.Analysis.GowersMaureyCodedPairOrbitSum

/-! The actual high-code interaction matrix. Mismatches are small, the
initial off-diagonal code collision occurs at most once, and the last
diagonal collision recovers the common preceding functionals. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
variable {T : Y →L[𝕜] ShiftSpace D} {ε η : ℝ} {G : C00 𝕜 → ℝ}

theorem CodedDetectingFamily.high_interaction_sum_le {t : ℕ}
    (d : CodedDetectingFamily T ε η (D.j (2*t)-1) (D.j (2*t)) G)
    {g : Fin (D.j (2*t)) → C00 𝕜} (hg : SpecialSequence D (implicitNorm D) g)
    (m n : ℕ) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => D.j (2*t) < specialSequenceSize D g j),
      ‖pairing (g j) (spread m n (d.pair i).vector)‖) ≤ ‖T‖+14 := by
  classical
  let k := D.j (2*t)
  have hk : 0 < k := D.j_positive _
  let a := fun i => (d.pair i).functional
  have ha : SpecialSequence D (implicitNorm D) a := d.specialSequence hk
  have hsize (i : Fin k) : (d.pair i).size = specialSequenceSize D a i :=
    d.size_eq_specialSequenceSize hk i
  have hmono : StrictMono (specialSequenceSize D a) := by
    intro i j hij
    rw [← hsize,← hsize]
    exact d.size_strict hij
  obtain ⟨last,hlast,hafter,hprefix⟩ := ha.exists_last_diagonal_collision hk hg
  let bad (z : Fin k × Fin k) := z.1 ≠ z.2 ∧ (d.pair z.1).size = specialSequenceSize D g z.2
  have hbad : (Finset.univ.filter bad).card ≤ 1 := by
    simpa only [bad,hsize] using ha.offDiagonal_collision_count hg hmono
  let r (i : Fin k) := ‖pairing (d.pair i).functional (spread m n (d.pair i).vector)‖
  let δ : ℝ := 1/(k : ℝ)^2
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  let b (z : Fin k × Fin k) := if k < specialSequenceSize D g z.2 then
    ‖pairing (g z.2) (spread m n (d.pair z.1).vector)‖ else 0
  have hfour (i j : Fin k) : ‖pairing (g j) (spread m n (d.pair i).vector)‖ ≤ 4 :=
    ((hg.size_averaged j).dualUnit _).trans
      ((implicitNorm_spread_le D m n _).trans (d.pair i).norm_bound)
  have hp (z : Fin k × Fin k) : b z ≤ δ +
      (if z.1 = z.2 then r z.1 else 0) + (if bad z then 4 else 0) +
      (if z.1 = last ∧ z.2 = last then 4 else 0) := by
    obtain ⟨i,j⟩ := z
    by_cases hh : k < specialSequenceSize D g j
    · dsimp only [b]
      rw [if_pos hh]
      by_cases he : specialSequenceSize D g j = (d.pair i).size
      · by_cases hij : i = j
        · subst j
          rcases lt_trichotomy i last with hi | hi | hi
          · have hei : g i = (d.pair i).functional := (hprefix i hi).symm
            rw [hei]
            simp only [ite_true]
            have h1 : 0 ≤ (if bad (i,i) then (4 : ℝ) else 0) := by positivity
            have h2 : 0 ≤ (if i = last ∧ i = last then (4 : ℝ) else 0) := by positivity
            change r i ≤ _
            linarith
          · subst i
            simp only [and_self,ite_true]
            have hh := hfour last last
            have hr : 0 ≤ r last := norm_nonneg _
            have hb : 0 ≤ (if bad (last,last) then (4 : ℝ) else 0) := by positivity
            linarith
          · exact ((hafter i hi) ((hsize i).symm.trans he.symm)).elim
        · have hbadij : bad (i,j) := ⟨hij,he.symm⟩
          simp only [if_neg hij,if_pos hbadij,add_zero]
          have hh := hfour i j
          have hlast : 0 ≤ (if i = last ∧ j = last then (4 : ℝ) else 0) := by positivity
          linarith
      · have hh' := d.high_mismatch_bound hg i j hh he m n
        have hr : 0 ≤ (if i = j then r i else 0) := by positivity
        have hb : 0 ≤ (if bad (i,j) then (4 : ℝ) else 0) := by positivity
        have hl : 0 ≤ (if i = last ∧ j = last then (4 : ℝ) else 0) := by positivity
        change _ ≤ δ at hh'
        linarith
    · simp only [b,if_neg hh]
      positivity
  have hdiag : (∑ z : Fin k × Fin k, if z.1 = z.2 then r z.1 else 0) = ∑ i, r i := by
    simp [Fintype.sum_prod_type]
  have hsingle : (∑ z : Fin k × Fin k, if z.1 = last ∧ z.2 = last then (4 : ℝ) else 0) = 4 := by
    simp [Fintype.sum_prod_type,ite_and]
  have hoff : (∑ z : Fin k × Fin k, if bad z then (4 : ℝ) else 0) ≤ 4 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    have hc : ((Finset.univ.filter bad).card : ℝ) ≤ 1 := by exact_mod_cast hbad
    linarith
  have hconst : (∑ _z : Fin k × Fin k, δ) = 1 := by
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_mul,δ]
    field_simp
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun z _ => hp z)
  simp only [Finset.sum_add_distrib,hconst,hdiag,hsingle] at hs
  have hr := d.own_diagonal_sum_le hk m n
  have he : (∑ i, ∑ j ∈ Finset.univ.filter (fun j => D.j (2*t) < specialSequenceSize D g j),
      ‖pairing (g j) (spread m n (d.pair i).vector)‖) = ∑ z : Fin k × Fin k, b z := by
    simp only [Fintype.sum_prod_type,b,Finset.sum_filter,k]
  rw [he]
  change (∑ i, r i) ≤ ‖T‖+5 at hr
  linarith

end ThesisCommon.GowersMaurey
