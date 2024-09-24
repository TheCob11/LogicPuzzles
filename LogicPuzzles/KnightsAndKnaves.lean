import Mathlib
import LogicPuzzles.QuestionProblem

structure Guard where
  truther: Bool
  good_door: Bool
deriving Repr

open Guard
open QuestionProblem (Spec CountingSolver)

structure Basic where
  a : Guard
  b : Guard
  door_eq_not : a.good_door = !b.good_door
attribute [simp] Basic.door_eq_not
@[simp] theorem Basic.doors_ne (b: Basic) : b.a.good_door ≠ b.b.good_door :=
  b.door_eq_not ▸ Bool.not_ne_self b.b.good_door
@[simp] theorem Basic.not_both_door_true (b: Basic)
  (ha: b.a.good_door = true) (hb: b.b.good_door = true) : False :=
  b.doors_ne <| ha.trans hb.symm
@[simp] theorem Basic.not_both_door_false (b: Basic)
  (ha: b.a.good_door = false) (hb: b.b.good_door = false) : False :=
  b.doors_ne <| ha.trans hb.symm
@[simp] theorem Basic.not_and_doors (b: Basic) :
 ¬(b.a.good_door ∧ b.b.good_door) := fun ⟨ha, hb⟩ ↦
  b.doors_ne <| ha.trans hb.symm
abbrev Basic.guards (b: Basic) := [b.a, b.b]
abbrev BasicProblem : Spec Basic (.CharPicker 2 Guard Bool) := fun b ↦ {
  check := fun c ↦ b.guards[c].good_door
  ask := fun c q ↦ b.guards[c].truther = q b.guards[c]
}

example : BasicProblem.Solution where
  solver prob := bif prob.ask 0 fun _ ↦ prob.ask 0 good_door then 0 else 1
  all_valid b := by
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, doors_ne⟩ <;>
    simp
    all_goals exact Bool.false_eq_true.mp doors_ne

example : BasicProblem.SolutionN 1 where
  solver asker := do
    let q ← asker fun prob ↦ (0, fun _ ↦ prob.ask 0 good_door)
    return bif q then 0 else 1
  all_valid b := by
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, doors_ne⟩ <;>
    simp [pure, bind, WriterT.mk]
    all_goals exact Bool.false_eq_true.mp doors_ne
  asks_le_n b := by
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, doors_ne⟩ <;>
    simp [pure, bind, WriterT.mk, Multiplicative.ofAdd]

example : BasicProblem.Solution where
  solver prob := bif prob.ask 0 fun ⟨char, good⟩ ↦ (char = true) = good then 0 else 1
  all_valid b := by
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, doors_ne⟩ <;>
    simp
    all_goals exact Bool.false_eq_true.mp doors_ne

example : BasicProblem.SolutionN 1 where
  solver asker := do
    let q ← asker fun _p ↦ (0, fun ⟨char, good⟩ ↦ (char = true) = good)
    return bif q then 0 else 1
  all_valid b := by
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, doors_ne⟩ <;>
    simp [pure, bind, WriterT.mk] at doors_ne ⊢
  asks_le_n b := by
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, doors_ne⟩ <;>
    simp [pure, bind, WriterT.mk, Multiplicative.ofAdd]

example (chars_ne: (b: Basic) → b.a.truther ≠ b.b.truther) : BasicProblem.Solution where
  solver prob := bif prob.ask 0 fun _ ↦ prob.ask 1 good_door then 0 else 1
  all_valid b := by
    have := chars_ne b
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, doors_ne⟩ <;>
    simp_all
    all_goals exact Bool.true_eq_false.mp doors_ne

example (chars_ne: (b: Basic) → b.a.truther ≠ b.b.truther) : BasicProblem.Solution where
  solver prob :=
    bif prob.ask 0 fun ⟨char, good⟩ ↦ bif char = true then good else !good
    then 0 else 1
  all_valid b := by
    have := chars_ne b
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, doors_ne⟩ <;>
    simp_all
    all_goals exact Bool.true_eq_false.mp doors_ne
