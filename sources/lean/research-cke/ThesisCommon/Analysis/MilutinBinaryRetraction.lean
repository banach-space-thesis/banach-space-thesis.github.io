import ThesisCommon.Analysis.MilutinBinaryPrefixes

/-! A continuous retraction of binary Cantor space onto any nonempty closed
subset. Outside the closed subset, the output is chosen from the last
compatible prefix, making the retraction locally constant there. -/

noncomputable section
open Set Filter Topology
namespace ThesisCommon

variable (C : Set (ℕ → Bool)) (hC : C.Nonempty) (hclosed : IsClosed C)

def milutinBinaryRetractValue (x : ℕ → Bool) : C := by
  classical
  exact if hx : x ∈ C then ⟨x, hx⟩ else
    milutinBinaryPrefixChoice C hC (milutinBinaryExit C hclosed x hx)
      (milutinBinaryPrefix x (milutinBinaryExit C hclosed x hx))

theorem milutinBinaryRetractValue_of_mem (x : C) :
    milutinBinaryRetractValue C hC hclosed x.val = x := by
  simp [milutinBinaryRetractValue, x.property]

theorem milutinBinaryRetractValue_prefix (x : ℕ → Bool) (hx : x ∉ C) :
    ∀ k < milutinBinaryExit C hclosed x hx,
      (milutinBinaryRetractValue C hC hclosed x).val k = x k := by
  simpa only [milutinBinaryRetractValue, dif_neg hx] using
    milutinBinaryPrefixChoice_eq C hC x _ (milutinBinaryExit_compatible C hC hclosed x hx)

theorem milutinBinaryRetractValue_preserves_prefix (x : ℕ → Bool) (n : ℕ)
    (hc : MilutinPrefixCompatible C x n) :
    ∀ k < n, (milutinBinaryRetractValue C hC hclosed x).val k = x k := by
  classical
  by_cases hx : x ∈ C
  · simp [milutinBinaryRetractValue, hx]
  · have hn : n ≤ milutinBinaryExit C hclosed x hx := by
      by_contra! hn
      exact milutinBinaryExit_bad C hclosed x hx (hc.mono (Nat.succ_le_of_lt hn))
    intro k hk
    exact milutinBinaryRetractValue_prefix C hC hclosed x hx k (lt_of_lt_of_le hk hn)

theorem milutinBinaryRetractValue_locally_constant (x : ℕ → Bool) (hx : x ∉ C)
    (y : ℕ → Bool)
    (hxy : ∀ k < milutinBinaryExit C hclosed x hx + 1, y k = x k) :
    milutinBinaryRetractValue C hC hclosed y = milutinBinaryRetractValue C hC hclosed x := by
  classical
  have hybad : ¬ MilutinPrefixCompatible C y (milutinBinaryExit C hclosed x hx + 1) := by
    intro h
    exact milutinBinaryExit_bad C hclosed x hx ((milutinPrefixCompatible_congr hxy).mp h)
  have hy : y ∉ C := fun hy => hybad ⟨⟨y, hy⟩, fun _ _ => rfl⟩
  have hyx : milutinBinaryExit C hclosed y hy ≤ milutinBinaryExit C hclosed x hx :=
    Nat.find_min' (milutinBinary_exists_incompatible C hclosed y hy) hybad
  have hxbad : ¬ MilutinPrefixCompatible C x (milutinBinaryExit C hclosed y hy + 1) := by
    intro h
    apply milutinBinaryExit_bad C hclosed y hy
    exact (milutinPrefixCompatible_congr (fun k hk =>
      (hxy k (lt_of_lt_of_le hk (Nat.add_le_add_right hyx 1))).symm)).mp h
  have hxyExit : milutinBinaryExit C hclosed x hx ≤ milutinBinaryExit C hclosed y hy :=
    Nat.find_min' (milutinBinary_exists_incompatible C hclosed x hx) hxbad
  have he : milutinBinaryExit C hclosed y hy = milutinBinaryExit C hclosed x hx :=
    le_antisymm hyx hxyExit
  simp only [milutinBinaryRetractValue, dif_neg hx, dif_neg hy]
  rw [he]
  congr 1
  funext i
  exact hxy i (Nat.lt_succ_of_lt i.isLt)

theorem milutinBinaryRetractValue_continuous : Continuous (milutinBinaryRetractValue C hC hclosed) := by
  classical
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  apply continuous_iff_continuousAt.mpr
  intro x
  have he : (fun y => (milutinBinaryRetractValue C hC hclosed y).val k) =ᶠ[𝓝 x]
      (fun _ => (milutinBinaryRetractValue C hC hclosed x).val k) := by
    by_cases hx : x ∈ C
    · filter_upwards [milutinBinaryCylinder_mem_nhds x (k + 1)] with y hy
      have hcompat : MilutinPrefixCompatible C y (k + 1) :=
        ⟨⟨x, hx⟩, fun i hi => (hy i hi).symm⟩
      rw [milutinBinaryRetractValue_preserves_prefix C hC hclosed y (k + 1) hcompat k (Nat.lt_succ_self k)]
      simpa [milutinBinaryRetractValue, hx] using hy k (Nat.lt_succ_self k)
    · filter_upwards [milutinBinaryCylinder_mem_nhds x (milutinBinaryExit C hclosed x hx + 1)] with y hy
      exact congrArg (fun z : C => z.val k) (milutinBinaryRetractValue_locally_constant C hC hclosed x hx y hy)
  exact (continuousAt_congr he).mpr continuousAt_const

def milutinBinaryRetraction : C((ℕ → Bool), C) :=
  ⟨milutinBinaryRetractValue C hC hclosed, milutinBinaryRetractValue_continuous C hC hclosed⟩

@[simp] theorem milutinBinaryRetraction_apply_subtype (x : C) :
    milutinBinaryRetraction C hC hclosed x.val = x :=
  milutinBinaryRetractValue_of_mem C hC hclosed x

end ThesisCommon
