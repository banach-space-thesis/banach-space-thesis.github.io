import Posets.AlspachCounterexampleSuccessor
import Posets.AlspachCounterexampleLimit

/-! The finite stages and the ω stage of the specialized Alspach family.
These are explicit probability forests, with the same lower estimate at
every stage. Topological properties are proved separately. -/

noncomputable section
namespace Posets
universe u v
variable (𝕜 : Type v) [RCLike 𝕜]

structure AlspachRowFamily where
  Point : Type u
  Index : Type u
  rows : AlspachPointedRows 𝕜 Point Index

variable {𝕜}

def alspachFiniteRows (B : Type u) (p : B) : ℕ → AlspachRowFamily.{u, v} 𝕜
  | 0 => ⟨B, B, AlspachPointedRows.base p⟩
  | n + 1 =>
      let F := AlspachPointedRows.base (𝕜 := 𝕜) p
      let G := (alspachFiniteRows B p n).rows
      ⟨F.SuccessorPoints G, F.SuccessorIndices G, F.successor G⟩

def alspachOmegaRows (B : Type u) (p : B) : AlspachRowFamily.{u, v} 𝕜 :=
  let F := fun n => (alspachFiniteRows (𝕜 := 𝕜) B p n).rows
  ⟨AlspachPointedRows.LimitPoints F, AlspachPointedRows.LimitIndices F,
    AlspachPointedRows.limit F⟩

theorem alspachFiniteRows_point_countable (B : Type u) [Countable B] (p : B) (n : ℕ) :
    Countable (alspachFiniteRows (𝕜 := 𝕜) B p n).Point := by
  induction n with
  | zero => exact inferInstanceAs (Countable B)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Countable
        (B ⊕ (B × B × {x : (alspachFiniteRows (𝕜 := 𝕜) B p n).Point //
          x ≠ (alspachFiniteRows (𝕜 := 𝕜) B p n).rows.point})))

theorem alspachFiniteRows_index_countable (B : Type u) [Countable B] (p : B) (n : ℕ) :
    Countable (alspachFiniteRows (𝕜 := 𝕜) B p n).Index := by
  induction n with
  | zero => exact inferInstanceAs (Countable B)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Countable
        (B ⊕ (B × {x : (alspachFiniteRows (𝕜 := 𝕜) B p n).Index //
          x ≠ (alspachFiniteRows (𝕜 := 𝕜) B p n).rows.index})))

theorem alspachOmegaRows_point_countable (B : Type u) [Countable B] (p : B) :
    Countable (alspachOmegaRows (𝕜 := 𝕜) B p).Point := by
  letI (n : ℕ) := alspachFiniteRows_point_countable (𝕜 := 𝕜) B p n
  exact inferInstanceAs (Countable (AlspachPointedRows.LimitPoints
    (fun n => (alspachFiniteRows (𝕜 := 𝕜) B p n).rows)))

theorem alspachOmegaRows_index_countable (B : Type u) [Countable B] (p : B) :
    Countable (alspachOmegaRows (𝕜 := 𝕜) B p).Index := by
  letI (n : ℕ) := alspachFiniteRows_index_countable (𝕜 := 𝕜) B p n
  exact inferInstanceAs (Countable (AlspachPointedRows.LimitIndices
    (fun n => (alspachFiniteRows (𝕜 := 𝕜) B p n).rows)))

theorem alspachOmegaRows_synthesis_lower (B : Type u) (p : B)
    (a : lp (fun _ : (alspachOmegaRows (𝕜 := 𝕜) B p).Index => 𝕜) 1) :
    (1 / 3 : ℝ) * ‖a‖ ≤ ‖(alspachOmegaRows (𝕜 := 𝕜) B p).rows.forest.synthesis a‖ :=
  (alspachOmegaRows (𝕜 := 𝕜) B p).rows.forest.synthesis_lower a

end Posets
