import ThesisCommon.Analysis.OperatorModulus

/-! The order-interval form of the Riesz--Kantorovich formula. Finite sums
of lattice absolute values are bounded by testing all choices of signs.
Applied to positive decompositions, this identifies the constructed modulus
with the supremum of the images of the original order interval. -/
noncomputable section
open Set Finset
namespace ThesisCommon

theorem lattice_sum_abs_le_of_signed_sum_le {F ι : Type*}
    [AddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
    (s : Finset ι) (a : ι → F) (b : F)
    (h : ∀ ε : ι → Bool, (∑ i ∈ s, if ε i then a i else -a i) ≤ b) :
    (∑ i ∈ s, |a i|) ≤ b := by
  classical
  induction s using Finset.induction_on generalizing b with
  | empty => simpa using h (fun _ => true)
  | @insert i s his ih =>
    have hsign (v : Bool) (ε : ι → Bool) :
        (if v then a i else -a i) + (∑ j ∈ s, if ε j then a j else -a j) ≤ b := by
      have hh := h (Function.update ε i v)
      rw [sum_insert his, Function.update_self] at hh
      have heq : (∑ j ∈ s, if Function.update ε i v j then a j else -a j) =
          ∑ j ∈ s, if ε j then a j else -a j := by
        apply sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hj his)]
      rwa [heq] at hh
    have hp : a i + (∑ j ∈ s, |a j|) ≤ b := by
      apply (le_sub_iff_add_le').mp
      exact ih (b - a i) (fun ε => (le_sub_iff_add_le').mpr (by simpa using hsign true ε))
    have hn : -a i + (∑ j ∈ s, |a j|) ≤ b := by
      apply (le_sub_iff_add_le').mp
      exact ih (b - -a i) (fun ε => (le_sub_iff_add_le').mpr (by simpa using hsign false ε))
    rw [sum_insert his, abs, sup_add]
    exact sup_le hp hn

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
variable [IsOrderedAddMonoid E] [HasSolidNorm E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Lattice F]
variable [IsOrderedAddMonoid F] [HasSolidNorm F] [CompleteSpace F] [OrderClosedTopology F]
variable (hALE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
variable (hALF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)

/-- The precise interval-supremum formula used in PEMS Section 3. -/
theorem operatorModulus_rieszKantorovich (T : E →L[ℝ] F) (x : E) (hx : 0 ≤ x) :
    IsLUB (T '' Icc (-x) x) (operatorModulus hALE hALF T x) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    have habs : |g| ≤ x := abs_le'.mpr ⟨hg.2, by simpa using neg_le_neg hg.1⟩
    have hmono : operatorModulus hALE hALF T |g| ≤ operatorModulus hALE hALF T x := by
      have hn := operatorModulus_nonneg hALE hALF T (x - |g|) (sub_nonneg.mpr habs)
      rw [map_sub] at hn
      exact sub_nonneg.mp hn
    exact (le_abs_self (T g)).trans ((abs_apply_le_operatorModulus_abs hALE hALF T g).trans hmono)
  · intro b hb
    rw [operatorModulus_apply_of_nonneg hALE hALF T x hx]
    apply (operatorModulusPos_isLUB hALE hALF T x hx).2
    rintro _ ⟨d, rfl⟩
    apply lattice_sum_abs_le_of_signed_sum_le
    intro ε
    let g : E := ∑ i, if ε i then d.part i else -d.part i
    have habs : |g| ≤ x := by
      calc
        |g| ≤ ∑ i, |if ε i then d.part i else -d.part i| := lattice_abs_sum_le _ _
        _ = ∑ i, d.part i := by
          apply sum_congr rfl
          intro i _
          split <;> simp [abs_of_nonneg (d.nonneg i)]
        _ = x := d.sum_eq
    have hg : g ∈ Icc (-x) x :=
      ⟨by simpa using neg_le_neg (abs_le'.mp habs).2, (abs_le'.mp habs).1⟩
    have hTg := hb (show T g ∈ T '' Icc (-x) x from ⟨g, hg, rfl⟩)
    have heq : T g = ∑ i, if ε i then T (d.part i) else -T (d.part i) := by
      rw [show g = ∑ i, if ε i then d.part i else -d.part i from rfl, map_sum]
      apply sum_congr rfl
      intro i _
      split <;> simp_all only [map_neg]
    rwa [heq] at hTg

end ThesisCommon
