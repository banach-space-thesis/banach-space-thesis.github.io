import Mathlib.Algebra.Order.Group.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Finite positive decompositions in a vector lattice. These are the common
refinement steps in the Riesz--Kantorovich construction of operator moduli. -/
noncomputable section
open Finset
namespace ThesisCommon
variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]

theorem lattice_abs_sum_le {ι : Type*} (s : Finset ι) (f : ι → E) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    rw [sum_insert his, sum_insert his]
    exact (abs_add_le _ _).trans (add_le_add_left ih _)

/-- Split 0≤x≤y+z into positive pieces dominated by y and z. -/
theorem riesz_split_pair {x y z : E} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxyz : x ≤ y + z) :
    ∃ u v : E, 0 ≤ u ∧ u ≤ y ∧ 0 ≤ v ∧ v ≤ z ∧ u + v = x := by
  refine ⟨x ⊓ y, x - (x ⊓ y), le_inf hx hy, inf_le_right,
    sub_nonneg.mpr inf_le_left, ?_, by abel⟩
  have hmin : x - z ≤ x ⊓ y :=
    le_inf (sub_le_self x hz) (sub_le_iff_le_add.mpr hxyz)
  apply sub_le_iff_le_add.mpr
  simpa only [add_comm] using sub_le_iff_le_add.mp hmin

/-- A positive element below a finite sum can be split into pieces below the
respective summands. No total-order or pointwise-function assumption is used. -/
theorem riesz_split_finset {ι : Type*} (s : Finset ι) (a : ι → E)
    (ha : ∀ i ∈ s, 0 ≤ a i) (x : E) (hx : 0 ≤ x) (hxa : x ≤ ∑ i ∈ s, a i) :
    ∃ b : ι → E, (∀ i ∈ s, 0 ≤ b i ∧ b i ≤ a i) ∧ (∑ i ∈ s, b i) = x := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    have hx0 : x = 0 := le_antisymm (by simpa using hxa) hx
    exact ⟨fun _ => 0, by simp, by simp [hx0]⟩
  | @insert i s his ih =>
    have hspos : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (mem_insert_of_mem hj)
    have hispos := ha i (mem_insert_self i s)
    obtain ⟨u, v, hu, hua, hv, hvs, huv⟩ :=
      riesz_split_pair hx hispos (sum_nonneg hspos) (by simpa [sum_insert his] using hxa)
    obtain ⟨b, hb, hbsum⟩ := ih hspos v hv hvs
    refine ⟨Function.update b i u, ?_, ?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · simpa using And.intro hu hua
      · have hji : j ≠ i := fun h => his (h ▸ hj)
        simpa [Function.update_of_ne hji] using hb j hj
    · rw [sum_insert his, Function.update_self]
      have hsum : (∑ j ∈ s, Function.update b i u j) = ∑ j ∈ s, b j := by
        apply sum_congr rfl
        intro j hj
        have hji : j ≠ i := fun h => his (h ▸ hj)
        exact Function.update_of_ne hji _ _
      rw [hsum, hbsum, huv]

/-- Two finite positive decompositions of the same element have a common
positive refinement. Rows recover the first decomposition, columns the second. -/
theorem riesz_refine_finsets {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → E) (b : κ → E) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ j ∈ t, 0 ≤ b j)
    (hab : (∑ i ∈ s, a i) = ∑ j ∈ t, b j) :
    ∃ c : ι → κ → E, (∀ i ∈ s, ∀ j ∈ t, 0 ≤ c i j) ∧
      (∀ i ∈ s, (∑ j ∈ t, c i j) = a i) ∧ (∀ j ∈ t, (∑ i ∈ s, c i j) = b j) := by
  classical
  induction t using Finset.induction_on generalizing a with
  | empty =>
    refine ⟨fun _ _ => 0, by simp, ?_, by simp⟩
    intro i hi
    have hsum : (∑ i ∈ s, a i) = 0 := by simpa using hab
    have hle : a i ≤ 0 := (single_le_sum ha hi).trans_eq hsum
    simp [le_antisymm hle (ha i hi)]
  | @insert j t hjt ih =>
    have htpos : ∀ k ∈ t, 0 ≤ b k := fun k hk => hb k (mem_insert_of_mem hk)
    have hjpos := hb j (mem_insert_self j t)
    have hja : b j ≤ ∑ i ∈ s, a i := by
      rw [hab, sum_insert hjt]
      exact le_add_of_nonneg_right (sum_nonneg htpos)
    obtain ⟨u, hu, husum⟩ := riesz_split_finset s a ha (b j) hjpos hja
    have hrespos : ∀ i ∈ s, 0 ≤ a i - u i := fun i hi => sub_nonneg.mpr (hu i hi).2
    have hres : (∑ i ∈ s, (a i - u i)) = ∑ k ∈ t, b k := by
      rw [sum_sub_distrib, hab, husum, sum_insert hjt]
      abel
    obtain ⟨c, hc, hcrows, hccols⟩ := ih (fun i => a i - u i) hrespos htpos hres
    refine ⟨fun i => Function.update (c i) j (u i), ?_, ?_, ?_⟩
    · intro i hi k hk
      rcases mem_insert.mp hk with rfl | hk
      · simpa using (hu i hi).1
      · have hkj : k ≠ j := fun h => hjt (h ▸ hk)
        simpa [Function.update_of_ne hkj] using hc i hi k hk
    · intro i hi
      change (∑ k ∈ insert j t, Function.update (c i) j (u i) k) = a i
      rw [sum_insert hjt, Function.update_self]
      have hsum : (∑ k ∈ t, Function.update (c i) j (u i) k) = ∑ k ∈ t, c i k := by
        apply sum_congr rfl
        intro k hk
        have hkj : k ≠ j := fun h => hjt (h ▸ hk)
        exact Function.update_of_ne hkj _ _
      rw [hsum, hcrows i hi]
      abel
    · intro k hk
      rcases mem_insert.mp hk with rfl | hk
      · simpa using husum
      · have hkj : k ≠ j := fun h => hjt (h ▸ hk)
        simpa [Function.update_of_ne hkj] using hccols k hk

end ThesisCommon
