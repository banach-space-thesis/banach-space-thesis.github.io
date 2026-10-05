import Posets.AlspachCounterexampleSynthesis

/-! The uniform one-third lower estimate for Alspach's probability rows.
Each nonroot row is the average of a private probability and its parent.
Reading the pairwise disjoint private supports is contractive. The inverse
coefficient operator has columns `2 e_i - e_parent`, hence norm at most three.
This proves the estimate over every RCLike scalar field. The argument is the
finite-parent-forest specialization of Alspach (1997), Lemma 1.3. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable {𝕜 I E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

structure AlspachForestRows (𝕜 I E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] where
  parent : I → Option I
  depth : I → ℕ
  parent_lt : ∀ i j, parent i = some j → depth j < depth i
  privateRow : I → E
  row : I → E
  read : E →L[𝕜] lp (fun _ : I => 𝕜) 1
  read_norm_le : ‖read‖ ≤ 1
  read_private : ∀ i, read (privateRow i) = lp.single 1 i 1
  root_row : ∀ i, parent i = none → row i = privateRow i
  child_row : ∀ i j, parent i = some j →
    row i = (1 / 2 : 𝕜) • (privateRow i + row j)
  row_norm_le : ∀ i, ‖row i‖ ≤ 1

namespace AlspachForestRows
variable (F : AlspachForestRows 𝕜 I E)

def inverseColumn (i : I) : lp (fun _ : I => 𝕜) 1 :=
  match F.parent i with
  | none => lp.single 1 i 1
  | some j => (2 : 𝕜) • lp.single 1 i 1 - lp.single 1 j 1

theorem inverseColumn_norm_le (i : I) : ‖F.inverseColumn i‖ ≤ 3 := by
  unfold inverseColumn
  split
  · simp [lp.norm_single]
  · calc
      _ ≤ ‖(2 : 𝕜) • lp.single (E := fun _ : I => 𝕜) 1 i 1‖ +
          ‖lp.single (E := fun _ : I => 𝕜) 1 _ 1‖ := norm_sub_le _ _
      _ = 3 := by simp [norm_smul, lp.norm_single]; norm_num

def inverseCoefficients : lp (fun _ : I => 𝕜) 1 →L[𝕜] lp (fun _ : I => 𝕜) 1 :=
  alspachSynthesis F.inverseColumn 3 F.inverseColumn_norm_le

@[simp] theorem inverseCoefficients_single (i : I) :
    F.inverseCoefficients (lp.single 1 i 1) = F.inverseColumn i := by
  simp [inverseCoefficients]

theorem inverseCoefficients_norm_le : ‖F.inverseCoefficients‖ ≤ 3 :=
  alspachSynthesis_norm_le _ (by norm_num) _

theorem inverse_read_row (i : I) :
    F.inverseCoefficients (F.read (F.row i)) = lp.single 1 i 1 := by
  induction hi : F.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    cases hp : F.parent i with
    | none => rw [F.root_row i hp, F.read_private, F.inverseCoefficients_single,
        inverseColumn, hp]
    | some j =>
      have hj : F.inverseCoefficients (F.read (F.row j)) = lp.single 1 j 1 :=
        ih (F.depth j) (hi ▸ F.parent_lt i j hp) j rfl
      rw [F.child_row i j hp, map_smul, map_add, map_smul, map_add,
        F.read_private, F.inverseCoefficients_single, hj, inverseColumn, hp]
      module

def synthesis : lp (fun _ : I => 𝕜) 1 →L[𝕜] E :=
  alspachSynthesis F.row 1 F.row_norm_le

@[simp] theorem synthesis_single (i : I) (c : 𝕜) :
    F.synthesis (lp.single 1 i c) = c • F.row i :=
  alspachSynthesis_single _ _ _ _ _

theorem inverse_read_synthesis :
    F.inverseCoefficients.comp (F.read.comp F.synthesis) =
      ContinuousLinearMap.id 𝕜 (lp (fun _ : I => 𝕜) 1) := by
  apply alspach_lp_ext
  intro i
  simpa only [ContinuousLinearMap.comp_apply, synthesis_single, one_smul,
    ContinuousLinearMap.id_apply] using F.inverse_read_row i

theorem synthesis_lower (a : lp (fun _ : I => 𝕜) 1) :
    (1 / 3 : ℝ) * ‖a‖ ≤ ‖F.synthesis a‖ := by
  have hid : F.inverseCoefficients (F.read (F.synthesis a)) = a :=
    DFunLike.congr_fun F.inverse_read_synthesis a
  have hread : ‖F.read (F.synthesis a)‖ ≤ ‖F.synthesis a‖ := by
    exact (F.read.le_opNorm _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right F.read_norm_le (norm_nonneg _))
  have h := F.inverseCoefficients.le_opNorm (F.read (F.synthesis a))
  have hnorm := mul_le_mul_of_nonneg_right F.inverseCoefficients_norm_le
    (norm_nonneg (F.read (F.synthesis a)))
  rw [hid] at h
  nlinarith

theorem synthesis_norm_le : ‖F.synthesis‖ ≤ 1 :=
  alspachSynthesis_norm_le _ zero_le_one _

end AlspachForestRows
end Posets
