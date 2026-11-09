import BanachIsometric.CubicalSphereDescent
import Mathlib.Topology.Order.ProjIcc

/-! Two actual cube reparametrizations fix the boundary condition and send
the complements of disjoint interior boxes to the cube boundary. -/

noncomputable section
namespace BanachIsometric.SphereGenerator
open Set
open scoped Topology Topology.Homotopy unitInterval

abbrev SpherePinchCube (n : ℕ) := Fin (n + 1) → unitInterval

def boxPinchLower {n : ℕ} (right : Bool) (i : Fin (n + 1)) : ℝ :=
  if i = 0 then (if right then 5 / 8 else 1 / 8) else 1 / 4

def boxPinchUpper {n : ℕ} (right : Bool) (i : Fin (n + 1)) : ℝ :=
  if i = 0 then (if right then 7 / 8 else 3 / 8) else 3 / 4

theorem boxPinchLower_pos {n : ℕ} (right : Bool) (i : Fin (n + 1)) :
    0 < boxPinchLower right i := by
  unfold boxPinchLower
  split_ifs <;> norm_num

theorem boxPinchUpper_lt_one {n : ℕ} (right : Bool) (i : Fin (n + 1)) :
    boxPinchUpper right i < 1 := by
  unfold boxPinchUpper
  split_ifs <;> norm_num

theorem boxPinchLower_lt_upper {n : ℕ} (right : Bool) (i : Fin (n + 1)) :
    boxPinchLower right i < boxPinchUpper right i := by
  unfold boxPinchLower boxPinchUpper
  split_ifs <;> norm_num

def boxPinchCoordinate {n : ℕ} (right : Bool) (i : Fin (n + 1))
    (t : unitInterval) : unitInterval :=
  Set.projIcc 0 1 zero_le_one
    (((t : ℝ) - boxPinchLower right i) / (boxPinchUpper right i - boxPinchLower right i))

theorem continuous_boxPinchCoordinate {n : ℕ} (right : Bool) (i : Fin (n + 1)) :
    Continuous (boxPinchCoordinate right i) :=
  continuous_projIcc.comp ((continuous_subtype_val.sub continuous_const).div_const _)

theorem boxPinchCoordinate_eq_zero {n : ℕ} (right : Bool) (i : Fin (n + 1))
    (t : unitInterval) (ht : (t : ℝ) ≤ boxPinchLower right i) : boxPinchCoordinate right i t = 0 := by
  unfold boxPinchCoordinate
  exact Set.projIcc_of_le_left _ (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht)
    (sub_nonneg.mpr (boxPinchLower_lt_upper right i).le))

theorem boxPinchCoordinate_eq_one {n : ℕ} (right : Bool) (i : Fin (n + 1))
    (t : unitInterval) (ht : boxPinchUpper right i ≤ (t : ℝ)) : boxPinchCoordinate right i t = 1 := by
  have hdiv : 1 ≤ ((t : ℝ) - boxPinchLower right i) /
      (boxPinchUpper right i - boxPinchLower right i) := by
    apply (le_div_iff₀ (sub_pos.mpr (boxPinchLower_lt_upper right i))).mpr
    linarith
  unfold boxPinchCoordinate
  exact Set.projIcc_of_right_le _ hdiv

theorem boxPinchCoordinate_fixed_endpoint {n : ℕ} (right : Bool) (i : Fin (n + 1))
    (t : unitInterval) (ht : t = 0 ∨ t = 1) : boxPinchCoordinate right i t = t := by
  rcases ht with rfl | rfl
  · exact boxPinchCoordinate_eq_zero right i 0 (boxPinchLower_pos right i).le
  · exact boxPinchCoordinate_eq_one right i 1 (boxPinchUpper_lt_one right i).le

def cubeBoxPinch (n : ℕ) (right : Bool) : C(SpherePinchCube n, SpherePinchCube n) where
  toFun u i := boxPinchCoordinate right i (u i)
  continuous_toFun := continuous_pi (fun i => (continuous_boxPinchCoordinate right i).comp (continuous_apply i))

theorem cubeBoxPinch_boundary (n : ℕ) (right : Bool) (u : SpherePinchCube n)
    (hu : u ∈ Cube.boundary (Fin (n + 1))) : cubeBoxPinch n right u ∈ Cube.boundary (Fin (n + 1)) := by
  obtain ⟨i, hi⟩ := hu
  refine ⟨i, ?_⟩
  change boxPinchCoordinate right i (u i) = 0 ∨ boxPinchCoordinate right i (u i) = 1
  rw [boxPinchCoordinate_fixed_endpoint right i (u i) hi]
  exact hi

def cubePinchSupport (n : ℕ) (right : Bool) : Set (SpherePinchCube n) :=
  {u | ∀ i, boxPinchLower right i ≤ (u i : ℝ) ∧ (u i : ℝ) ≤ boxPinchUpper right i}

theorem isClosed_cubePinchSupport (n : ℕ) (right : Bool) : IsClosed (cubePinchSupport n right) := by
  have h : cubePinchSupport n right = ⋂ i : Fin (n + 1),
      {u | boxPinchLower right i ≤ (u i : ℝ)} ∩ {u | (u i : ℝ) ≤ boxPinchUpper right i} := by
    ext u
    simp [cubePinchSupport]
  rw [h]
  apply isClosed_iInter
  intro i
  have hi : Continuous (fun u : SpherePinchCube n => (u i : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  exact (isClosed_le continuous_const hi).inter (isClosed_le hi continuous_const)

theorem not_boundary_of_mem_cubePinchSupport (n : ℕ) (right : Bool) (u : SpherePinchCube n)
    (hu : u ∈ cubePinchSupport n right) : u ∉ Cube.boundary (Fin (n + 1)) := by
  rintro ⟨i, hi | hi⟩
  · have h : 0 < (u i : ℝ) := (boxPinchLower_pos right i).trans_le (hu i).1
    rw [hi] at h
    exact (lt_irrefl (0 : ℝ)) h
  · have h : (u i : ℝ) < 1 := (hu i).2.trans_lt (boxPinchUpper_lt_one right i)
    rw [hi] at h
    exact (lt_irrefl (1 : ℝ)) h

theorem disjoint_cubePinchSupport (n : ℕ) :
    Disjoint (cubePinchSupport n false) (cubePinchSupport n true) := by
  apply Set.disjoint_left.mpr
  intro u hfalse htrue
  have h₁ := (hfalse (0 : Fin (n + 1))).2
  have h₂ := (htrue (0 : Fin (n + 1))).1
  norm_num [boxPinchUpper, boxPinchLower] at h₁ h₂
  linarith

theorem cubeBoxPinch_boundary_of_not_mem_support (n : ℕ) (right : Bool) (u : SpherePinchCube n)
    (hu : u ∉ cubePinchSupport n right) : cubeBoxPinch n right u ∈ Cube.boundary (Fin (n + 1)) := by
  change ¬ ∀ i, boxPinchLower right i ≤ (u i : ℝ) ∧ (u i : ℝ) ≤ boxPinchUpper right i at hu
  obtain ⟨i, hi⟩ := not_forall.mp hu
  refine ⟨i, ?_⟩
  change boxPinchCoordinate right i (u i) = 0 ∨ boxPinchCoordinate right i (u i) = 1
  by_cases h : (u i : ℝ) ≤ boxPinchLower right i
  · exact Or.inl (boxPinchCoordinate_eq_zero right i (u i) h)
  · have hh : boxPinchUpper right i ≤ (u i : ℝ) := by
      by_contra! hn
      exact hi ⟨(lt_of_not_ge h).le, hn.le⟩
    exact Or.inr (boxPinchCoordinate_eq_one right i (u i) hh)

def cubePinchInterpolation (n : ℕ) (right : Bool) :
    C(unitInterval × SpherePinchCube n, SpherePinchCube n) where
  toFun z i := Set.projIcc 0 1 zero_le_one
    ((1 - (z.1 : ℝ)) * (z.2 i : ℝ) + (z.1 : ℝ) * (cubeBoxPinch n right z.2 i : ℝ))
  continuous_toFun := by
    apply continuous_pi
    intro i
    have ht : Continuous (fun z : unitInterval × SpherePinchCube n => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hu : Continuous (fun z : unitInterval × SpherePinchCube n => (z.2 i : ℝ)) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
    have hp : Continuous (fun z : unitInterval × SpherePinchCube n => (cubeBoxPinch n right z.2 i : ℝ)) :=
      continuous_subtype_val.comp ((continuous_apply i).comp ((cubeBoxPinch n right).continuous.comp continuous_snd))
    exact continuous_projIcc.comp (((continuous_const.sub ht).mul hu).add (ht.mul hp))

theorem cubePinchInterpolation_zero (n : ℕ) (right : Bool) (u : SpherePinchCube n) :
    cubePinchInterpolation n right (0, u) = u := by
  funext i
  change Set.projIcc 0 1 zero_le_one ((1 - (0 : ℝ)) * (u i : ℝ) +
    (0 : ℝ) * (cubeBoxPinch n right u i : ℝ)) = u i
  simpa only [sub_zero, one_mul, zero_mul, add_zero] using Set.projIcc_val zero_le_one (u i)

theorem cubePinchInterpolation_one (n : ℕ) (right : Bool) (u : SpherePinchCube n) :
    cubePinchInterpolation n right (1, u) = cubeBoxPinch n right u := by
  funext i
  change Set.projIcc 0 1 zero_le_one ((1 - (1 : ℝ)) * (u i : ℝ) +
    (1 : ℝ) * (cubeBoxPinch n right u i : ℝ)) = cubeBoxPinch n right u i
  simpa only [sub_self, zero_mul, one_mul, zero_add] using
    Set.projIcc_val zero_le_one (cubeBoxPinch n right u i)

theorem cubePinchInterpolation_boundary (n : ℕ) (right : Bool) (t : unitInterval)
    (u : SpherePinchCube n) (hu : u ∈ Cube.boundary (Fin (n + 1))) :
    cubePinchInterpolation n right (t, u) ∈ Cube.boundary (Fin (n + 1)) := by
  obtain ⟨i, hi⟩ := hu
  have hp : cubeBoxPinch n right u i = u i := boxPinchCoordinate_fixed_endpoint right i (u i) hi
  have he : cubePinchInterpolation n right (t, u) i = u i := by
    change Set.projIcc 0 1 zero_le_one ((1 - (t : ℝ)) * (u i : ℝ) +
      (t : ℝ) * (cubeBoxPinch n right u i : ℝ)) = u i
    rw [hp, show (1 - (t : ℝ)) * (u i : ℝ) + (t : ℝ) * (u i : ℝ) = (u i : ℝ) by ring]
    exact Set.projIcc_val zero_le_one (u i)
  refine ⟨i, ?_⟩
  rw [he]
  exact hi

end BanachIsometric.SphereGenerator
