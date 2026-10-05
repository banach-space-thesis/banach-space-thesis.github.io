import Posets.AlspachCounterexamplePointed

/-! The countable limit operation glues the distinguished points and rows
of a sequence of probability families. It preserves their uniform forest
estimate without requiring uniform bounds on their finite depths. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
namespace AlspachPointedRows
variable {𝕜 : Type*} [RCLike 𝕜] {K I : ℕ → Type*}
variable (F : ∀ n, AlspachPointedRows 𝕜 (K n) (I n))

abbrev LimitPoints := Option (Σ n, {x : K n // x ≠ (F n).point})
abbrev LimitIndices := Option (Σ n, {i : I n // i ≠ (F n).index})

def limitPoint (n : ℕ) (x : K n) : LimitPoints F :=
  if h : x = (F n).point then none else some ⟨n, ⟨x, h⟩⟩

def limitIndex (n : ℕ) (i : I n) : LimitIndices F :=
  if h : i = (F n).index then none else some ⟨n, ⟨i, h⟩⟩

@[simp] theorem limitPoint_root (n : ℕ) : limitPoint F n (F n).point = none := by
  simp [limitPoint]

@[simp] theorem limitIndex_root (n : ℕ) : limitIndex F n (F n).index = none := by
  simp [limitIndex]

def limitOwner : LimitPoints F → LimitIndices F
  | none => none
  | some ⟨n, x⟩ => some ⟨n, ⟨(F n).owner x, fun h => x.property ((F n).owner_root x |>.mp h)⟩⟩

def limitParent : LimitIndices F → Option (LimitIndices F)
  | none => none
  | some ⟨n, i⟩ => ((F n).parent i).map (limitIndex F n)

def limitDepth : LimitIndices F → ℕ
  | none => 0
  | some ⟨n, i⟩ => (F n).depth i

def limitPrivate : LimitIndices F → AlspachProbability (LimitPoints F)
  | none => .point none
  | some ⟨n, i⟩ => ((F n).privateRow i).map (limitPoint F n)

def limitRow : LimitIndices F → AlspachProbability (LimitPoints F)
  | none => .point none
  | some ⟨n, i⟩ => ((F n).row i).map (limitPoint F n)

theorem limitOwner_root (x : LimitPoints F) : limitOwner F x = none ↔ x = none := by
  cases x with
  | none => simp [limitOwner]
  | some z => rcases z with ⟨n, x⟩; simp [limitOwner]

theorem limitOwner_private (i : LimitIndices F) (x : LimitPoints F)
    (hx : x ∈ (limitPrivate F i).support) : limitOwner F x = i := by
  cases i with
  | none =>
      have : x = none := by simpa [limitPrivate, AlspachProbability.support] using hx
      subst x
      rfl
  | some z =>
      rcases z with ⟨n, i⟩
      obtain ⟨y, hy, rfl⟩ := (AlspachProbability.mem_support_map _ _ _).mp hx
      have hyp : y ≠ (F n).point := by
        intro h; subst y; exact (F n).point_not_mem_private i.property hy
      simp only [limitPoint, hyp, ↓reduceDIte, limitOwner]
      congr 2
      exact Subtype.ext ((F n).owner_private i y hy)

theorem limitParent_none (i : LimitIndices F) : limitParent F i = none ↔ i = none := by
  cases i with
  | none => simp [limitParent]
  | some z =>
      rcases z with ⟨n, i⟩
      have hn : (F n).parent i ≠ none := fun h => i.property (((F n).parent_none i).mp h)
      simp [limitParent, hn]

theorem limitDepth_index (n : ℕ) (i : I n) :
    limitDepth F (limitIndex F n i) = (F n).depth i := by
  by_cases h : i = (F n).index
  · subst i; simp [limitDepth, (F n).depth_root]
  · simp [limitIndex, h, limitDepth]

theorem limitParent_lt (i j : LimitIndices F) (h : limitParent F i = some j) :
    limitDepth F j < limitDepth F i := by
  cases i with
  | none => simp [limitParent] at h
  | some z =>
      rcases z with ⟨n, i⟩
      cases hp : (F n).parent i with
      | none => simp [limitParent, hp] at h
      | some a =>
          simp only [limitParent, hp, Option.map_some, Option.some.injEq] at h
          subst j
          rw [limitDepth_index]
          exact (F n).parent_lt i a hp

theorem limitRow_index (n : ℕ) (i : I n) :
    limitRow F (limitIndex F n i) = ((F n).row i).map (limitPoint F n) := by
  by_cases h : i = (F n).index
  · subst i; simp [limitRow, (F n).row_root, AlspachProbability.map]
  · simp [limitIndex, h, limitRow]

theorem limitChild_row (i j : LimitIndices F) (h : limitParent F i = some j) :
    (limitRow F i).vector (𝕜 := 𝕜) =
      (1 / 2 : 𝕜) • ((limitPrivate F i).vector + (limitRow F j).vector) := by
  cases i with
  | none => simp [limitParent] at h
  | some z =>
      rcases z with ⟨n, i⟩
      cases hp : (F n).parent i with
      | none => simp [limitParent, hp] at h
      | some a =>
          simp only [limitParent, hp, Option.map_some, Option.some.injEq] at h
          subst j
          rw [limitRow_index]
          have he := congrArg (AlspachProbability.mapLinear (𝕜 := 𝕜) (limitPoint F n))
            ((F n).child_row i a hp)
          simpa only [map_smul, map_add, AlspachProbability.mapLinear_vector,
            limitRow, limitPrivate] using he

def limit : AlspachPointedRows 𝕜 (LimitPoints F) (LimitIndices F) where
  point := none
  index := none
  parent := limitParent F
  depth := limitDepth F
  parent_lt := limitParent_lt F
  parent_none := limitParent_none F
  depth_root := rfl
  privateRow := limitPrivate F
  row := limitRow F
  owner := limitOwner F
  owner_root := limitOwner_root F
  owner_private := limitOwner_private F
  private_root := rfl
  row_root := rfl
  child_row := limitChild_row F

end AlspachPointedRows
end Posets
