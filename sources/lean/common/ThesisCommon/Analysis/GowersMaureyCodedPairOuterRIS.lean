import ThesisCommon.Analysis.GowersMaureyCodedPairSelection
import ThesisCommon.Analysis.GowersMaureyOuterRISSize
import ThesisCommon.Analysis.GowersMaureyFloorSizes
import ThesisCommon.Analysis.GowersMaureyFloorWeight

/-! The selected pairs, divided by eight, form a genuine outer RIS.
The first-size and spacing conditions are proved from the original rapid
construction sizes and the code-growth budget imposed during selection. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def codedPairGrowthBudget (x : C00 𝕜) : ℝ := 4*((supportInterval x).set.card : ℝ)^2

theorem prefixSum_real_smul {n : ℕ} (x : Fin n → C00 𝕜) (r : ℝ) (i : Fin n) :
    prefixSum (fun j => r • x j) i = r • prefixSum x i := by
  simp only [prefixSum,Finset.smul_sum]

theorem CodedDetectingFamily.outerRIS {D : ConstructionData 𝕜}
    {Y : Submodule 𝕜 (ShiftSpace D)} {T : Y →L[𝕜] ShiftSpace D} {ε η : ℝ}
    {k : ℕ} (hk : 0 < k)
    (d : CodedDetectingFamily T ε η (k-1) k codedPairGrowthBudget) :
    IsRIS D 1 (fun i => (1/8 : ℝ) • (d.pair i).vector) := by
  classical
  letI : NeZero k := ⟨hk.ne'⟩
  have hindex : StrictMono (fun i => 2*(d.pair i).index+1) := by
    intro i j hij
    exact D.j_strict.lt_iff_lt.mp (d.size_strict hij)
  have hfirst : (d.pair ⟨0,hk⟩).size = D.j (2*k-1) := by
    have he : 2*(k-1)+1 = 2*k-1 := by omega
    simpa only [Fin.mk_zero,Fin.val_zero,if_pos rfl,he] using d.size_rule ⟨0,hk⟩
  have hindexlo (i : Fin k) : 2*k-1 ≤ 2*(d.pair i).index+1 := by
    apply D.j_strict.le_iff_le.mp
    change D.j (2*k-1) ≤ (d.pair i).size
    rw [← hfirst]
    exact d.size_strict.monotone (Fin.zero_le i)
  refine ⟨{
    epsilon_pos := by norm_num
    epsilon_le_one := le_rfl
    successive := successive_real_smul d.successive _
    size := fun i => ⌊Real.sqrt ((d.pair i).size : ℝ)⌋₊
    size_strict := fun i j hij => D.floor_sqrt_size_strictMono (hindex hij)
    size_pos := fun i => D.floor_sqrt_size_pos _
    first_large := ?_
    norm_bound := ?_
    spacing := ?_
  }⟩
  · intro i
    have h := (D.outer_ris_floor_size_gt hk).trans_le
      (Nat.cast_le.mpr (D.floor_sqrt_size_strictMono.monotone (hindexlo i)))
    simpa only [one_pow,div_one] using h
  · intro i
    rw [seminorm_real_smul,abs_of_pos (by norm_num : (0 : ℝ) < 1/8)]
    have hb := (d.pair i).interval_bound _ (D.floor_sqrt_size_pos _)
      (Nat.floor_le (Real.sqrt_nonneg _))
    change intervalNorm D ⌊Real.sqrt ((d.pair i).size : ℝ)⌋₊ (d.pair i).vector ≤ 8 at hb
    linarith
  · intro i hi
    rw [prefixSum_real_smul,supportInterval_real_smul (by norm_num : (1/8 : ℝ) ≠ 0),one_mul]
    have hg := d.growth i hi
    change 4*((supportInterval (prefixSum (fun j => (d.pair j).vector) i)).set.card : ℝ)^2 <
      logarithmicWeight (d.pair i).size at hg
    have hw := D.weight_le_four_floor_sqrt (2*(d.pair i).index+1)
    have hs := Real.sq_sqrt (logarithmicWeight_nonneg ⌊Real.sqrt ((d.pair i).size : ℝ)⌋₊)
    have hn := Real.sqrt_nonneg (logarithmicWeight ⌊Real.sqrt ((d.pair i).size : ℝ)⌋₊)
    have hc : 0 ≤ ((supportInterval (prefixSum (fun j => (d.pair j).vector) i)).set.card : ℝ) :=
      Nat.cast_nonneg _
    change logarithmicWeight (d.pair i).size ≤
      4*logarithmicWeight ⌊Real.sqrt ((d.pair i).size : ℝ)⌋₊ at hw
    nlinarith

theorem exists_detecting_special_RIS_family
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (hne : ∀ i, u.vector i ≠ 0)
    (T : Y →L[𝕜] ShiftSpace D) (q : ℕ → ℕ) (hq : StrictMono q)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ i, ∀ z ∈ spreadVectorOrbit D (u.vector i) (q i),
      ε ≤ ‖T (u.inSubspace i)-z‖)
    {η : ℝ} (hη : 0 < η) (k : ℕ) (hk : 0 < k) :
    ∃ d : CodedDetectingFamily T ε η (k-1) k codedPairGrowthBudget,
      SpecialSequence D (implicitNorm D) (fun i => (d.pair i).functional) ∧
      IsRIS D 1 (fun i => (1/8 : ℝ) • (d.pair i).vector) := by
  obtain ⟨d,hd⟩ := exists_detecting_special_family u hne T q hq hε hsep hη k hk codedPairGrowthBudget
  exact ⟨d,hd,d.outerRIS hk⟩

end ThesisCommon.GowersMaurey
