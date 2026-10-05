import ThesisCommon.Analysis.LpHaarTraceSplitSelection

/-! Normalize traces by the positive measure of the actual parent.
The block's arithmetic diagonal average and both child traces can be
made as close as desired to the normalized limiting parent trace. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def lpHaarParentTrace (a : LpHaarDyadicSetIndex → 𝕜) (P : LpHaarFiniteParent) : 𝕜 :=
  a P.index / ((volume.restrict (Icc (0 : ℝ) 1)).real P.set : 𝕜)

def lpHaarSplitDiagonal (d : ∀ n, Fin (2 ^ n) → 𝕜) (S : LpHaarFiniteSplit) : 𝕜 :=
  (S.atoms.card : 𝕜)⁻¹ * ∑ k ∈ S.atoms, d S.level k

theorem lpHaarParentTrace_congr (a : LpHaarDyadicSetIndex → 𝕜)
    (heq : ∀ i j, lpHaarDyadicSet i = lpHaarDyadicSet j → a i = a j)
    (P Q : LpHaarFiniteParent) (h : P.set = Q.set) :
    lpHaarParentTrace a P = lpHaarParentTrace a Q := by
  unfold lpHaarParentTrace
  rw [h, heq P.index Q.index h]

theorem lpHaarSplitDiagonal_trace (d : ∀ n, Fin (2 ^ n) → 𝕜) (S : LpHaarFiniteSplit) :
    lpHaarSplitDiagonal d S = lpHaarLevelTrace d S.level S.parent.set /
      ((volume.restrict (Icc (0 : ℝ) 1)).real S.parent.set : 𝕜) := by
  change (S.atoms.card : 𝕜)⁻¹ * ∑ k ∈ S.atoms, d S.level k =
    lpHaarLevelTrace d S.level (lpHaarBlockParent S.level S.atoms) /
      ((volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarBlockParent S.level S.atoms) : 𝕜)
  rw [lpHaarLevelTrace_parent, lpHaarBlockParent_real_measure]
  have hr : (intervalLpDyadicRadius S.level : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos S.level).ne'
  have hc : (S.atoms.card : 𝕜) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr S.nonempty).ne'
  push_cast
  field_simp

theorem lpHaar_trace_parent_select_normalized
    (d : ∀ n, Fin (2 ^ n) → 𝕜) (a : LpHaarDyadicSetIndex → 𝕜)
    (r : ℕ → ℕ) (hr : StrictMono r) {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, ‖a i‖ ≤ M * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i))
    (hlim : ∀ i, Tendsto (fun t => lpHaarLevelTrace d (r t) (lpHaarDyadicSet i)) atTop (𝓝 (a i)))
    (heq : ∀ i j, lpHaarDyadicSet i = lpHaarDyadicSet j → a i = a j)
    (hadd : ∀ i j k, Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j) →
      lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j → a k = a i + a j)
    (P : LpHaarFiniteParent) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ S.parent.set = P.set ∧
      ‖lpHaarSplitDiagonal d S - lpHaarParentTrace a P‖ < ε ∧
      ∀ b : Bool, ‖lpHaarParentTrace a (S.child b) - lpHaarParentTrace a P‖ < ε := by
  obtain ⟨S, hN, hP, hd, hc⟩ := lpHaar_trace_parent_select d a r hr hM ha hlim heq hadd P N hε
  let m := (volume.restrict (Icc (0 : ℝ) 1)).real P.set
  have hm : 0 < m := P.mass_pos
  have hmc : (m : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hm.ne'
  refine ⟨S, hN, hP, ?_, ?_⟩
  · rw [lpHaarSplitDiagonal_trace, lpHaarParentTrace, hP, ← sub_div, norm_div,
      RCLike.norm_ofReal, abs_of_pos hm]
    exact (div_lt_iff₀ hm).mpr (by simpa only [hP] using hd)
  · intro b
    have hchild : ((volume.restrict (Icc (0 : ℝ) 1)).real (S.child b).set : 𝕜) =
        (m : 𝕜) / 2 := by
      rw [S.child_mass, hP]
      push_cast
      rfl
    have hid : lpHaarParentTrace a (S.child b) - lpHaarParentTrace a P =
        (a (S.child b).index - (2 : 𝕜)⁻¹ * a P.index) / ((m : 𝕜) / 2) := by
      unfold lpHaarParentTrace
      rw [hchild]
      change _ / ((m : 𝕜) / 2) - _ / (m : 𝕜) = _
      field_simp
    rw [hid, norm_div, norm_div, RCLike.norm_ofReal, abs_of_pos hm]
    have htwo : ‖(2 : 𝕜)‖ = (2 : ℝ) := by norm_num
    rw [htwo]
    apply (div_lt_iff₀ (div_pos hm (by norm_num))).mpr
    simpa only [mul_div_assoc] using hc b

end ThesisCommon
