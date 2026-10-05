import ThesisCommon.Analysis.GowersMaureyFiniteSequences
import Mathlib.Tactic

/-! Exact interval restriction identities for finite sequences and tail spreads. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def Interval.inter (E F : Interval) : Interval :=
  ⟨max E.first F.first, min E.last F.last⟩

@[simp] theorem Interval.mem_inter (E F : Interval) (i : ℕ) :
    i ∈ (E.inter F).set ↔ i ∈ E.set ∧ i ∈ F.set := by
  simp only [Interval.inter, Interval.set, Finset.mem_Icc]
  omega

theorem restrict_restrict (E F : Interval) (x : C00 𝕜) :
    restrict E (restrict F x) = restrict (E.inter F) x := by
  ext i
  simp only [restrict_apply, Interval.mem_inter]
  by_cases hi : i ∈ E.set <;> by_cases hj : i ∈ F.set <;> simp [hi, hj]

theorem restrict_comm (E F : Interval) (x : C00 𝕜) :
    restrict E (restrict F x) = restrict F (restrict E x) := by
  ext i
  simp only [restrict_apply]
  by_cases hi : i ∈ E.set <;> by_cases hj : i ∈ F.set <;> simp [hi, hj]

/-- The image of the part of E in the domain of a tail spread. -/
def Interval.spreadImage (E : Interval) (m n : ℕ) : Interval :=
  if m ≤ E.last then ⟨E.first - m + n, E.last - m + n⟩ else ⟨1, 0⟩

theorem Interval.mem_spreadImage (E : Interval) (m n i : ℕ) (hi : m ≤ i) :
    i - m + n ∈ (E.spreadImage m n).set ↔ i ∈ E.set := by
  unfold Interval.spreadImage
  split_ifs with h
  · simp only [Interval.set, Finset.mem_Icc]
    omega
  · simp only [Interval.set, Finset.mem_Icc]
    omega

theorem spread_restrict (E : Interval) (m n : ℕ) (x : C00 𝕜) :
    spread m n (restrict E x) = restrict (E.spreadImage m n) (spread m n x) := by
  have h : (spread (𝕜 := 𝕜) m n).comp (restrict E) =
      (restrict (E.spreadImage m n)).comp (spread m n) := by
    apply Finsupp.lhom_ext
    intro i c
    simp only [LinearMap.comp_apply, restrict_single]
    by_cases hi : m ≤ i
    · by_cases hE : i ∈ E.set
      · rw [if_pos hE, spread_single, if_pos hi, restrict_single,
          if_pos ((E.mem_spreadImage m n i hi).mpr hE)]
      · rw [if_neg hE, map_zero, spread_single, if_pos hi, restrict_single,
          if_neg (fun h => hE ((E.mem_spreadImage m n i hi).mp h))]
    · rw [spread_single, if_neg hi, map_zero]
      split_ifs <;> simp [spread_single, hi]
  exact DFunLike.congr_fun h x

end ThesisCommon.GowersMaurey
