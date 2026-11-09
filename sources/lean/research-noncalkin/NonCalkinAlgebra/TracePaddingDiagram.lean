import NonCalkinAlgebra.RootedBlockDiagram

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement

def PadRow (n : ℕ) (_ : PUnit) := Fin (if n = 0 then 1 else 2)

private def padRootStep : Refinement (PadRow 0) (PadRow 1) where
  Copies _ := Fin 2
  color _ _ := PUnit.unit
  rows _ :=
    { toFun := Sigma.fst
      invFun := fun x => ⟨x, (0 : Fin 1)⟩
      left_inv := by
        rintro ⟨k, x⟩
        have hx : x = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) x 0
        subst x
        rfl
      right_inv := fun _ => rfl }

private def padStep : ∀ n, Refinement (PadRow n) (PadRow (n + 1))
  | 0 => padRootStep
  | _ + 1 => identity (fun _ : PUnit => Fin 2)

/-- A stationary full two-by-two factor, initially scalar. -/
def paddingDiagram : RootedBlockDiagram where
  Color _ := PUnit
  Row := PadRow
  colorFinite _ := inferInstance
  rowFinite n _ := inferInstanceAs (Finite (Fin (if n = 0 then 1 else 2)))
  colorNonempty _ := inferInstance
  rowNonempty n _ := by
    cases n
    · exact ⟨(0 : Fin 1)⟩
    · exact ⟨(0 : Fin 2)⟩
  rootColorSubsingleton := inferInstance
  rootRowSubsingleton _ := inferInstanceAs (Subsingleton (Fin 1))
  step := padStep
  step_covers n := by
    cases n with
    | zero => exact fun ⟨⟩ => ⟨PUnit.unit, (0 : Fin 2), rfl⟩
    | succ n => exact identity_covers

theorem paddingDiagram_mixes : paddingDiagram.EventuallyMixes := by
  intro n
  refine ⟨n, le_rfl, ?_⟩
  rw [paddingDiagram.path_self]
  exact fun ⟨⟩ ⟨⟩ => ⟨PUnit.unit, rfl⟩

def paddingWeight (n : ℕ) (_ : paddingDiagram.Color n) : ℝ :=
  if n = 0 then 1 else 1/2

end NonCalkinAlgebra.FiniteBlockRefinement
