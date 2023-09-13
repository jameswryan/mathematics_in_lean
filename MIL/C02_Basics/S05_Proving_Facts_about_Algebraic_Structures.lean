import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type _} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type _} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x :=by
  have h : ∀ x y : α, x ⊓ y ≤ y ⊓ x := by
    intros
    apply le_inf
    apply inf_le_right
    apply inf_le_left
  apply le_antisymm
  repeat apply h


example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  . apply le_inf
    . apply le_trans
      apply inf_le_left
      apply inf_le_left
    apply le_inf
    . apply le_trans
      apply inf_le_left
      apply inf_le_right
    apply inf_le_right
  apply le_inf
  . apply le_inf
    . apply inf_le_left
    apply le_trans
    apply inf_le_right
    apply inf_le_left
  . apply le_trans
    apply inf_le_right
    apply inf_le_right


example : x ⊔ y = y ⊔ x := by
  have h : ∀ x y : α, x ⊔ y ≤ y ⊔ x := by
    intros
    apply sup_le
    apply le_sup_right
    apply le_sup_left
  apply le_antisymm
  repeat apply h


theorem le_sup_right_assoc : x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z) := by
  apply sup_le
  · apply sup_le
    apply le_sup_left
    · apply le_trans
      apply @le_sup_left _ _ y z
      apply le_sup_right
  . apply le_trans
    apply @le_sup_right _ _ y z
    rw [sup_comm]
    apply le_sup_right

theorem le_sup_left_assoc : x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z := by
  apply sup_le
  . apply le_trans
    apply @le_sup_left _ _ x y
    apply le_sup_left
  . apply sup_le
    apply le_trans
    apply @le_sup_right _ _ x y
    apply le_sup_left
    apply le_sup_right

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  apply le_sup_right_assoc
  apply le_sup_left_assoc


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . apply inf_le_left
  . apply le_inf
    rfl
    apply le_sup_left


theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  . apply sup_le
    rfl
    apply inf_le_left
  . apply le_sup_left

end

section
variable {α : Type _} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type _} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc, @inf_comm _ _ c a,
    absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b), h, ← inf_assoc, @sup_comm _ _ c a,
  absorb1, sup_comm]

end

section
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem le_sub_of_le : a ≤ b → 0 ≤ b - a := by
  intro h
  rw [← sub_self a, sub_eq_add_neg,  sub_eq_add_neg, add_comm, add_comm b]
  apply add_le_add_left h

theorem le_of_le_sub : 0 ≤ b - a → a ≤ b := by
  intro h
  rw [← add_zero a, ← sub_add_cancel b a, add_comm (b-a)]
  apply add_le_add_left h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₁ : 0 ≤ (b-a) * c := mul_nonneg (le_sub_of_le _ _ h) h'
  rw [sub_mul] at h₁
  apply le_of_le_sub _ _ h₁

end

section
variable {X : Type _} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

#check (nonneg_of_mul_nonneg_left)

#check mul_one

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  rw [dist_comm y x, ← mul_one (dist x y), ← mul_add, one_add_one_eq_two] at h
  apply nonneg_of_mul_nonneg_left h
  exact two_pos

end
