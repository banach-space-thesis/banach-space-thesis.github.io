import ThesisCommon.Analysis.GowersMaureyCodedPairSelection
import ThesisCommon.Analysis.GowersMaureySpecialCollisions
import ThesisCommon.Analysis.GowersMaureyNPairMismatch
import ThesisCommon.Analysis.GowersMaureyAveragedSpreads

/-! The high-size mismatch estimate applied to the actual coded family,
including arbitrary competing special sequences and every genuine spread. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
variable {T : Y →L[𝕜] ShiftSpace D} {ε η : ℝ} {G : C00 𝕜 → ℝ}

theorem CodedDetectingFamily.index_ge_seed {seed k : ℕ}
    (d : CodedDetectingFamily T ε η seed k G) (i : Fin k) : seed ≤ (d.pair i).index := by
  have hk : 0 < k := (Nat.zero_le i.val).trans_lt i.isLt
  have hfirst : (d.pair ⟨0,hk⟩).size = D.j (2*seed+1) := by
    simpa only [Fin.mk_zero,Fin.val_zero,if_pos rfl] using d.size_rule ⟨0,hk⟩
  have hle := d.size_strict.monotone (show (⟨0,hk⟩ : Fin k) ≤ i from Nat.zero_le _)
  rw [hfirst] at hle
  have hi := D.j_strict.le_iff_le.mp hle
  omega

theorem CodedDetectingFamily.size_eq_specialSequenceSize {k : ℕ} (hk : 0 < k)
    (d : CodedDetectingFamily T ε η (k-1) k G) (i : Fin k) :
    (d.pair i).size = specialSequenceSize D (fun j => (d.pair j).functional) i := by
  have he : 2*(k-1)+1 = 2*k-1 := by omega
  simpa only [specialSequenceSize,he] using d.size_rule i

theorem CodedDetectingFamily.high_mismatch_bound {t : ℕ}
    (d : CodedDetectingFamily T ε η (D.j (2*t)-1) (D.j (2*t)) G)
    {g : Fin (D.j (2*t)) → C00 𝕜} (hg : SpecialSequence D (implicitNorm D) g)
    (i j : Fin (D.j (2*t))) (hhigh : D.j (2*t) < specialSequenceSize D g j)
    (hne : specialSequenceSize D g j ≠ (d.pair i).size) (m n : ℕ) :
    ‖pairing (g j) (spread m n (d.pair i).vector)‖ ≤ 1/(D.j (2*t) : ℝ)^2 := by
  obtain ⟨s,hs⟩ := hg.size_is_odd j
  have hts : t ≤ s := by
    rw [hs] at hhigh
    have hh := D.j_strict.lt_iff_lt.mp hhigh
    omega
  have hti : t ≤ (d.pair i).index := by
    have h0 : 2*t ≤ D.j (2*t) := D.j_strict.id_le _
    have hp := D.j_positive (2*t)
    have hi := d.index_ge_seed i
    omega
  have hsi : s ≠ (d.pair i).index := by
    intro he
    apply hne
    simp only [hs,he,DetectingPair.size]
  have ha := (hg.size_averaged j).spread n m
  rw [hs] at ha
  obtain ⟨v,hv,he⟩ := (d.pair i).ris
  rw [← pairing_spread_left n m,he]
  exact averaged_pairing_normalizedPairVector_le_special_inv_square D hti hts hsi hv ha

end ThesisCommon.GowersMaurey
