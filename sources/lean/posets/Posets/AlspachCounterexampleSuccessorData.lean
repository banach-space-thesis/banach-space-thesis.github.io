import Posets.AlspachCounterexamplePointed

/-! The underlying sets and probability rows of the successor graft.
We include a spine for every pair of a base point and an outer row. Spines
outside the support of that row receive zero mass. This harmless enlargement
makes the underlying sets independent of the support representation. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
namespace AlspachPointedRows
variable {𝕜 K I X J : Type*} [RCLike 𝕜]
variable (F : AlspachPointedRows 𝕜 K I) (G : AlspachPointedRows 𝕜 X J)

abbrev SuccessorPoints (_F : AlspachPointedRows 𝕜 K I) (G : AlspachPointedRows 𝕜 X J) := K ⊕ (K × I × {x : X // x ≠ G.point})
abbrev SuccessorIndices (_F : AlspachPointedRows 𝕜 K I) (G : AlspachPointedRows 𝕜 X J) := I ⊕ (I × {j : J // j ≠ G.index})

def attach (k : K) (i : I) (x : X) : F.SuccessorPoints G :=
  if h : x = G.point then .inl k else .inr (k, i, ⟨x, h⟩)

@[simp] theorem attach_root (k : K) (i : I) : F.attach G k i G.point = .inl k := by
  simp [attach]

@[simp] theorem attach_nonroot (k : K) (i : I) {x : X} (h : x ≠ G.point) :
    F.attach G k i x = .inr (k, i, ⟨x, h⟩) := by simp [attach, h]

def successorOwner : F.SuccessorPoints G → F.SuccessorIndices G
  | .inl k => .inl (F.owner k)
  | .inr (_, i, x) => .inr (i, ⟨G.owner x.val, fun h => x.property ((G.owner_root x).mp h)⟩)

def successorParent : F.SuccessorIndices G → Option (F.SuccessorIndices G)
  | .inl i => (F.parent i).map Sum.inl
  | .inr (i, j) => (G.parent j).map (fun a =>
      if h : a = G.index then Sum.inl i else Sum.inr (i, ⟨a, h⟩))

def successorDepth : F.SuccessorIndices G → ℕ
  | .inl i => F.depth i
  | .inr (i, j) => F.depth i + G.depth j

def successorPrivate : F.SuccessorIndices G → AlspachProbability (F.SuccessorPoints G)
  | .inl i => (F.privateRow i).map Sum.inl
  | .inr (i, j) => (F.row i).bind (fun k => (G.privateRow j).map (F.attach G k i))

def successorRow : F.SuccessorIndices G → AlspachProbability (F.SuccessorPoints G)
  | .inl i => (F.row i).map Sum.inl
  | .inr (i, j) => (F.row i).bind (fun k => (G.row j).map (F.attach G k i))

theorem successorOwner_root (x : F.SuccessorPoints G) :
    F.successorOwner G x = .inl F.index ↔ x = .inl F.point := by
  cases x with
  | inl k => simpa [successorOwner] using F.owner_root k
  | inr z => simp [successorOwner]

theorem successorOwner_private (i : F.SuccessorIndices G) (x : F.SuccessorPoints G)
    (hx : x ∈ (F.successorPrivate G i).support) : F.successorOwner G x = i := by
  cases i with
  | inl i =>
      obtain ⟨k, hk, rfl⟩ := (AlspachProbability.mem_support_map _ _ _).mp hx
      exact congrArg Sum.inl (F.owner_private i k hk)
  | inr ij =>
      rcases ij with ⟨i, j⟩
      obtain ⟨k, _, hx⟩ := (AlspachProbability.mem_support_bind _ _ _).mp hx
      obtain ⟨z, hz, rfl⟩ := (AlspachProbability.mem_support_map _ _ _).mp hx
      have hzp : z ≠ G.point := by
        intro h; subst z; exact G.point_not_mem_private j.property hz
      rw [F.attach_nonroot G k i hzp]
      change Sum.inr (i, (⟨G.owner z, _⟩ : {a : J // a ≠ G.index})) = Sum.inr (i, j)
      congr 2
      exact Subtype.ext (G.owner_private j z hz)

theorem successorParent_none (i : F.SuccessorIndices G) :
    F.successorParent G i = none ↔ i = .inl F.index := by
  cases i with
  | inl i => simpa [successorParent] using F.parent_none i
  | inr ij =>
      rcases ij with ⟨i, j⟩
      have hn : G.parent j ≠ none := fun h => j.property ((G.parent_none j).mp h)
      simp [successorParent, hn]

theorem successorParent_lt (i j : F.SuccessorIndices G)
    (h : F.successorParent G i = some j) :
    F.successorDepth G j < F.successorDepth G i := by
  cases i with
  | inl i =>
      cases hp : F.parent i with
      | none => simp [successorParent, hp] at h
      | some a =>
          simp only [successorParent, hp, Option.map_some, Option.some.injEq] at h
          subst j
          exact F.parent_lt i a hp
  | inr ij =>
      rcases ij with ⟨i, b⟩
      cases hp : G.parent b with
      | none => simp [successorParent, hp] at h
      | some a =>
          have hl := G.parent_lt b a hp
          by_cases ha : a = G.index
          · subst a
            simp only [successorParent, hp, Option.map_some, ↓reduceDIte,
              Option.some.injEq] at h
            subst j
            simp only [successorDepth]
            exact Nat.lt_add_of_pos_right (G.depth_pos b.property)
          · simp only [successorParent, hp, Option.map_some, ha, ↓reduceDIte,
              Option.some.injEq] at h
            subst j
            exact Nat.add_lt_add_left hl _

end AlspachPointedRows
end Posets

