import ThesisCommon.Analysis.JamesRightShift
import ThesisCommon.Analysis.JamesFiniteBlocks

/-! Standard finite James sections are the actual subspaces supported on
the first n coordinates. Translation identifies them, with uniform bounds,
with the finite intervals used in the block decomposition. -/
noncomputable section
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

def jamesInitialSubmodule (n : ℕ) : Submodule 𝕜 (JamesSequenceSpace 𝕜 p) where
  carrier := {x | ∀ k, n ≤ k → x k = 0}
  zero_mem' := by simp
  add_mem' hx hy := by intro k hk; simp only [JamesSequenceSpace.add_apply, hx k hk, hy k hk, add_zero]
  smul_mem' a x hx := by intro k hk; simp only [JamesSequenceSpace.smul_apply, hx k hk, smul_zero]

abbrev JamesInitialBlock (n : ℕ) := ↥(jamesInitialSubmodule 𝕜 p n)

instance jamesInitialBlock_normedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (JamesInitialBlock 𝕜 p n) :=
  inferInstanceAs (NormedAddCommGroup ↥(jamesInitialSubmodule 𝕜 p n))

instance jamesInitialBlock_normedSpace (n : ℕ) :
    NormedSpace 𝕜 (JamesInitialBlock 𝕜 p n) :=
  inferInstanceAs (NormedSpace 𝕜 ↥(jamesInitialSubmodule 𝕜 p n))

theorem jamesInitialSubmodule_isClosed (n : ℕ) :
    IsClosed (jamesInitialSubmodule 𝕜 p n : Set (JamesSequenceSpace 𝕜 p)) := by
  change IsClosed {x : JamesSequenceSpace 𝕜 p |
    ∀ k, n ≤ k → JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) k x = 0}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun k => isClosed_iInter fun _ =>
    isClosed_eq (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) k).continuous continuous_const

instance jamesInitialBlock_completeSpace (n : ℕ) : CompleteSpace (JamesInitialBlock 𝕜 p n) :=
  (jamesInitialSubmodule_isClosed 𝕜 p n).completeSpace_coe

instance jamesInitialBlock_finiteDimensional (n : ℕ) :
    FiniteDimensional 𝕜 (JamesInitialBlock 𝕜 p n) := by
  let R : JamesInitialBlock 𝕜 p n →ₗ[𝕜] (Fin n → 𝕜) :=
    LinearMap.pi fun k => (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) k.val).toLinearMap.comp
      (jamesInitialSubmodule 𝕜 p n).subtype
  apply FiniteDimensional.of_injective R
  intro x y hxy
  apply Subtype.ext
  apply JamesSequenceSpace.ext
  intro k
  by_cases hk : k < n
  · exact congrFun hxy ⟨k, hk⟩
  · rw [x.property k (le_of_not_gt hk), y.property k (le_of_not_gt hk)]

variable {𝕜} (hp : p.val ≠ ⊤) (lo n : ℕ)

def jamesInitialBlockInsert : JamesInitialBlock 𝕜 p n →L[𝕜]
    JamesIntervalBlock 𝕜 p lo (lo + 1 + n) :=
  ((jamesRightShift (𝕜 := 𝕜) p hp (lo + 1)).comp
    (jamesInitialSubmodule 𝕜 p n).subtypeL).codRestrict _ (by
      intro x k hk
      change jamesRightShift (𝕜 := 𝕜) p hp (lo + 1) x.val k = 0
      rw [jamesRightShift_apply]
      rcases hk with hk | hk
      · rw [if_pos (by omega)]
      · rw [if_neg (by omega), x.property _ (by omega)])

def jamesInitialBlockRead : JamesIntervalBlock 𝕜 p lo (lo + 1 + n) →L[𝕜]
    JamesInitialBlock 𝕜 p n :=
  ((jamesDrop (𝕜 := 𝕜) p hp (lo + 1)).comp
    (jamesIntervalSubmodule 𝕜 p lo (lo + 1 + n)).subtypeL).codRestrict _ (by
      intro x k hk
      change jamesDrop (𝕜 := 𝕜) p hp (lo + 1) x.val k = 0
      rw [jamesDrop_apply]
      exact x.property _ (Or.inr (by omega)))

@[simp] theorem jamesInitialBlockInsert_apply (x : JamesInitialBlock 𝕜 p n) :
    (jamesInitialBlockInsert (𝕜 := 𝕜) p hp lo n x).val =
      jamesRightShift (𝕜 := 𝕜) p hp (lo + 1) x.val := rfl

@[simp] theorem jamesInitialBlockRead_apply (x : JamesIntervalBlock 𝕜 p lo (lo + 1 + n)) :
    (jamesInitialBlockRead (𝕜 := 𝕜) p hp lo n x).val =
      jamesDrop (𝕜 := 𝕜) p hp (lo + 1) x.val := rfl

theorem jamesInitialBlock_read_insert (x : JamesInitialBlock 𝕜 p n) :
    jamesInitialBlockRead (𝕜 := 𝕜) p hp lo n
      (jamesInitialBlockInsert (𝕜 := 𝕜) p hp lo n x) = x := by
  apply Subtype.ext
  exact DFunLike.congr_fun (jamesDrop_rightShift (𝕜 := 𝕜) p hp (lo + 1)) x.val

theorem jamesInitialBlock_insert_read (x : JamesIntervalBlock 𝕜 p lo (lo + 1 + n)) :
    jamesInitialBlockInsert (𝕜 := 𝕜) p hp lo n
      (jamesInitialBlockRead (𝕜 := 𝕜) p hp lo n x) = x := by
  apply Subtype.ext
  ext k
  change jamesRightShift (𝕜 := 𝕜) p hp (lo + 1)
    (jamesDrop (𝕜 := 𝕜) p hp (lo + 1) x.val) k = x.val k
  rw [jamesRightShift_apply]
  split_ifs with hk
  · exact (x.property k (Or.inl (by omega))).symm
  · rw [jamesDrop_apply, Nat.sub_add_cancel (by omega)]

theorem jamesInitialBlockInsert_norm_le : ‖jamesInitialBlockInsert (𝕜 := 𝕜) p hp lo n‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  exact jamesRightShift_norm_bound p hp (lo + 1) x.val

theorem jamesInitialBlockRead_norm_le : ‖jamesInitialBlockRead (𝕜 := 𝕜) p hp lo n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact ((jamesDrop (𝕜 := 𝕜) p hp (lo + 1)).le_opNorm x.val).trans
    (mul_le_mul_of_nonneg_right (jamesDrop_norm_le p hp (lo + 1)) (norm_nonneg _))

def jamesInitialBlockEquiv : JamesInitialBlock 𝕜 p n ≃L[𝕜]
    JamesIntervalBlock 𝕜 p lo (lo + 1 + n) :=
  { (jamesInitialBlockInsert (𝕜 := 𝕜) p hp lo n).toLinearMap with
    invFun := jamesInitialBlockRead (𝕜 := 𝕜) p hp lo n
    left_inv := jamesInitialBlock_read_insert p hp lo n
    right_inv := jamesInitialBlock_insert_read p hp lo n
    continuous_toFun := (jamesInitialBlockInsert (𝕜 := 𝕜) p hp lo n).continuous
    continuous_invFun := (jamesInitialBlockRead (𝕜 := 𝕜) p hp lo n).continuous }

end ThesisCommon
