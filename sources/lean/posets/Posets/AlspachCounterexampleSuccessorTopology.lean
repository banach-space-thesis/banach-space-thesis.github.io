import Posets.AlspachCounterexampleSuccessor
import Posets.AlspachCounterexampleReindex
import Posets.AlspachCounterexampleCompactSpines
import Posets.AlspachCounterexampleProbabilityEvaluation

/-! Compact Hausdorff realizations of the successor point and row sets,
with explicit formulas for the transported probability evaluations. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
namespace AlspachPointedRows
variable {𝕜 K I X J : Type*} [RCLike 𝕜]
  [TopologicalSpace K] [TopologicalSpace I] [TopologicalSpace X] [TopologicalSpace J]
variable (F : AlspachPointedRows 𝕜 K I) (G : AlspachPointedRows 𝕜 X J)

abbrev SuccessorPointGraft (_F : AlspachPointedRows 𝕜 K I) (G : AlspachPointedRows 𝕜 X J) :=
  AlspachGraft (Prod.fst : K × I → K) (fun _ : K × I => {x : X // x ≠ G.point})

abbrev SuccessorIndexGraft (_F : AlspachPointedRows 𝕜 K I) (G : AlspachPointedRows 𝕜 X J) :=
  AlspachGraft (id : I → I) (fun _ : I => {j : J // j ≠ G.index})

def successorPointEquiv : F.SuccessorPoints G ≃ F.SuccessorPointGraft G :=
  (Equiv.sumCongr (Equiv.refl K)
    ({ toFun z := ⟨(z.1, z.2.1), z.2.2⟩
       invFun z := (z.1.1, z.1.2, z.2)
       left_inv _ := rfl
       right_inv _ := rfl } :
      (K × I × {x : X // x ≠ G.point}) ≃ (Σ _ : K × I, {x : X // x ≠ G.point}))).trans
    (alspachGraftEquiv Prod.fst _)

def successorIndexEquiv : F.SuccessorIndices G ≃ F.SuccessorIndexGraft G :=
  (Equiv.sumCongr (Equiv.refl I)
    ({ toFun z := ⟨z.1, z.2⟩
       invFun z := (z.1, z.2)
       left_inv _ := rfl
       right_inv _ := rfl } :
      (I × {j : J // j ≠ G.index}) ≃ (Σ _ : I, {j : J // j ≠ G.index}))).trans
    (alspachGraftEquiv id _)

@[simp] theorem successorPointEquiv_inl (k : K) :
    F.successorPointEquiv G (.inl k) = alspachGraftBase _ _ k := rfl
@[simp] theorem successorPointEquiv_inr (k : K) (i : I) (x : {x : X // x ≠ G.point}) :
    F.successorPointEquiv G (.inr (k, i, x)) = alspachGraftSpine _ _ ⟨(k, i), x⟩ := rfl
@[simp] theorem successorIndexEquiv_inl (i : I) :
    F.successorIndexEquiv G (.inl i) = alspachGraftBase _ _ i := rfl
@[simp] theorem successorIndexEquiv_inr (i : I) (j : {j : J // j ≠ G.index}) :
    F.successorIndexEquiv G (.inr (i, j)) = alspachGraftSpine _ _ ⟨i, j⟩ := rfl
@[simp] theorem successorIndexEquiv_symm_base (i : I) :
    (F.successorIndexEquiv G).symm (alspachGraftBase _ _ i) = .inl i := rfl
@[simp] theorem successorIndexEquiv_symm_spine (i : I) (j : {j : J // j ≠ G.index}) :
    (F.successorIndexEquiv G).symm (alspachGraftSpine _ _ ⟨i, j⟩) = .inr (i, j) := rfl

theorem successorPointEquiv_attach [CompactSpace X] [T2Space X] (k : K) (i : I) (x : X) :
    F.successorPointEquiv G (F.attach G k i x) =
      alspachCompactGraftAttach Prod.fst (fun _ : K × I => X) (fun _ => G.point) (k, i) x := by
  by_cases hx : x = G.point
  · subst x; simp
  · simp [attach_nonroot, hx]

def topologicalSuccessor :
    AlspachPointedRows 𝕜 (F.SuccessorPointGraft G) (F.SuccessorIndexGraft G) :=
  (F.successor G).reindex (F.successorPointEquiv G) (F.successorIndexEquiv G)

theorem topologicalSuccessor_eval_base (f : F.SuccessorPointGraft G → 𝕜) (i : I) :
    ((F.topologicalSuccessor G).row (alspachGraftBase _ _ i)).eval f =
      (F.row i).eval (fun k => f (alspachGraftBase _ _ k)) := by
  change (((F.row i).map Sum.inl).map (F.successorPointEquiv G)).eval f = _
  simp only [AlspachProbability.eval_map, successorPointEquiv_inl]

theorem topologicalSuccessor_eval_spine [CompactSpace X] [T2Space X]
    (f : F.SuccessorPointGraft G → 𝕜) (i : I) (j : {j : J // j ≠ G.index}) :
    ((F.topologicalSuccessor G).row (alspachGraftSpine _ _ ⟨i, j⟩)).eval f =
      (F.row i).eval (fun k => (G.row j).eval (fun x => f
        (alspachCompactGraftAttach Prod.fst (fun _ : K × I => X) (fun _ => G.point) (k, i) x))) := by
  change (((F.row i).bind (fun k => (G.row j).map (F.attach G k i))).map
    (F.successorPointEquiv G)).eval f = _
  simp only [AlspachProbability.eval_map, AlspachProbability.eval_bind,
    successorPointEquiv_attach]

end AlspachPointedRows
end Posets
