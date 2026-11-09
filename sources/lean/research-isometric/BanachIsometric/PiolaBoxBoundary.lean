import BanachIsometric.PiolaTestLift
import Mathlib.Order.Fin.Tuple
import Mathlib.Topology.Order.Compact

/-! # The compact union of coordinate faces of a closed box -/

namespace BanachIsometric

open Set

def piolaBoxBoundary {n : ℕ} (a b : PiolaSpace n) : Set (PiolaSpace n) :=
  Icc a b ∩ ⋃ i : Fin n, ({x | x i = a i} ∪ {x | x i = b i})

theorem mem_piolaBoxBoundary_iff {n : ℕ} {a b x : PiolaSpace n} :
    x ∈ piolaBoxBoundary a b ↔ x ∈ Icc a b ∧ ∃ i, x i = a i ∨ x i = b i := by
  simp only [piolaBoxBoundary, mem_inter_iff, mem_iUnion, mem_union, mem_setOf_eq]

theorem isCompact_piolaBoxBoundary {n : ℕ} (a b : PiolaSpace n) :
    IsCompact (piolaBoxBoundary a b) := by
  apply isCompact_Icc.inter_right
  apply isClosed_iUnion_of_finite
  intro i
  exact (isClosed_eq (continuous_apply i) continuous_const).union
    (isClosed_eq (continuous_apply i) continuous_const)

theorem snoc_zero_le_snoc_one {n : ℕ} {a b : PiolaSpace n} (hab : a ≤ b) :
    (Fin.snoc a (0 : ℝ) : PiolaSpace (n + 1)) ≤ (Fin.snoc b (1 : ℝ) : PiolaSpace (n + 1)) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa only [Fin.snoc_castSucc] using hab j

theorem init_mem_Icc_of_mem_snoc_box {n : ℕ} {a b : PiolaSpace n}
    {z : PiolaSpace (n + 1)} (hz : z ∈ Icc (Fin.snoc a (0 : ℝ)) (Fin.snoc b 1)) :
    Fin.init z ∈ Icc a b := by
  constructor
  · intro i
    simpa only [Fin.snoc_castSucc, Fin.init_def] using hz.1 i.castSucc
  · intro i
    simpa only [Fin.snoc_castSucc, Fin.init_def] using hz.2 i.castSucc

theorem last_mem_unitInterval_of_mem_snoc_box {n : ℕ} {a b : PiolaSpace n}
    {z : PiolaSpace (n + 1)} (hz : z ∈ Icc (Fin.snoc a (0 : ℝ)) (Fin.snoc b 1)) :
    z (Fin.last n) ∈ Icc (0 : ℝ) 1 := by
  exact ⟨by simpa only [Fin.snoc_last] using hz.1 (Fin.last n),
    by simpa only [Fin.snoc_last] using hz.2 (Fin.last n)⟩

end BanachIsometric
