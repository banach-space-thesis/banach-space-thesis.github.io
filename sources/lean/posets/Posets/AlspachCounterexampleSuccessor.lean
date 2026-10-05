import Posets.AlspachCounterexampleSuccessorData

/-! The successor operation preserves pointed probability forests and hence
the uniform lower ℓ¹ estimate. The row in a new spine is the outer probability
averaged over copies of the inner row, exactly the successor row formula. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
namespace AlspachPointedRows
variable {𝕜 K I X J : Type*} [RCLike 𝕜]
variable (F : AlspachPointedRows 𝕜 K I) (G : AlspachPointedRows 𝕜 X J)

theorem successorRow_lift (i : I) (j : J) :
    AlspachProbability.tensorRightLinear (𝕜 := 𝕜) (F.row i) (fun k => F.attach G k i)
      (G.row j).vector =
    (F.successorRow G (if h : j = G.index then .inl i else .inr (i, ⟨j, h⟩))).vector := by
  by_cases h : j = G.index
  · subst j
    simp only [G.row_root, AlspachProbability.vector,
      AlspachProbability.tensorRightLinear, alspachSynthesis_single, one_smul,
      attach_root, ↓reduceDIte, successorRow]
  · simp only [h, ↓reduceDIte, successorRow]
    exact AlspachProbability.tensorRightLinear_vector _ _ _

theorem successorChild_row (i j : F.SuccessorIndices G)
    (h : F.successorParent G i = some j) :
    (F.successorRow G i).vector (𝕜 := 𝕜) =
      (1 / 2 : 𝕜) • ((F.successorPrivate G i).vector + (F.successorRow G j).vector) := by
  cases i with
  | inl i =>
      cases hp : F.parent i with
      | none => simp [successorParent, hp] at h
      | some a =>
          simp only [successorParent, hp, Option.map_some, Option.some.injEq] at h
          subst j
          have he := congrArg (AlspachProbability.mapLinear
            (𝕜 := 𝕜) (Sum.inl : K → F.SuccessorPoints G)) (F.child_row i a hp)
          simpa only [map_smul, map_add, AlspachProbability.mapLinear_vector,
            successorRow, successorPrivate] using he
  | inr ij =>
      rcases ij with ⟨i, b⟩
      cases hp : G.parent b with
      | none => simp [successorParent, hp] at h
      | some a =>
          simp only [successorParent, hp, Option.map_some, Option.some.injEq] at h
          subst j
          have he := congrArg (AlspachProbability.tensorRightLinear
            (𝕜 := 𝕜) (F.row i) (fun k => F.attach G k i)) (G.child_row b a hp)
          rw [map_smul, map_add, F.successorRow_lift G i a] at he
          simpa only [AlspachProbability.tensorRightLinear_vector,
            successorRow, successorPrivate] using he

def successor : AlspachPointedRows 𝕜 (F.SuccessorPoints G) (F.SuccessorIndices G) where
  point := .inl F.point
  index := .inl F.index
  parent := F.successorParent G
  depth := F.successorDepth G
  parent_lt := F.successorParent_lt G
  parent_none := F.successorParent_none G
  depth_root := F.depth_root
  privateRow := F.successorPrivate G
  row := F.successorRow G
  owner := F.successorOwner G
  owner_root := F.successorOwner_root G
  owner_private := F.successorOwner_private G
  private_root := by simp only [successorPrivate, F.private_root, AlspachProbability.map]
  row_root := by simp only [successorRow, F.row_root, AlspachProbability.map]
  child_row := F.successorChild_row G

end AlspachPointedRows
end Posets
