import Mathlib
import LogicPuzzles.QuestionProblem

structure Guard where
  truther: Bool
  good_door: Bool
deriving Repr

structure Basic where
  a : Guard
  b : Guard
  door_eq_not : a.good_door = !b.good_door
def Basic.getChar (b: Basic) : Fin 2 → Guard | 0 => b.a | 1 => b.b

def BasicSpec : QuestionProblem.Spec (.CharPicker 2 Guard Bool Basic) := fun b ↦ {
  check := fun c ↦ (b.getChar c).good_door
  ask := fun (c, q) ↦ (b.getChar c).truther = q b
}

example : BasicSpec.SolutionN 1 := .of_solver_valid_and_n_asks
  fun asker ↦ do
    let ans ← asker <|.mk 0 fun ⟨⟨c_true, c_good⟩, _, _⟩ ↦ c_true == c_good
    return cond ans 0 1
  fun b ↦ by
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, door_eq_not⟩ <;>
    apply And.intro <;>
    solve | exact door_eq_not | rfl

example : BasicSpec.SolutionN 1 := .of_solver_valid_and_n_asks
  fun asker ↦ do
    let ans ← asker <|.mk 0
      fun b ↦ (BasicSpec b).ask <|.mk 0 fun ⟨⟨_, good⟩, _, _⟩ ↦ good
    return cond ans 0 1
  fun b ↦ by
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, door_eq_not⟩ <;>
    apply And.intro <;>
    solve | exact door_eq_not | rfl

example : BasicSpec.SolutionN 1 := .of_solver_valid_and_n_asks
  fun asker ↦ do
    let ans ← asker <|.mk 0 fun ⟨⟨char, good⟩, _, _⟩ ↦ (char = true) == good
    return cond ans 0 1
  fun b ↦ by
    apply And.intro <;>
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, door_eq_not⟩ <;>
    solve | exact door_eq_not | rfl

example (chars_ne: (b: Basic) → b.a.truther ≠ b.b.truther) :
  BasicSpec.SolutionN 1 := .of_solver_valid_and_n_asks
  fun asker ↦ do
    let ans ← asker <|.mk 0
      fun prob ↦ (BasicSpec prob).ask <|.mk 1 fun ⟨_, ⟨_, good⟩, _⟩ ↦ good
    return cond ans 0 1
  fun b ↦ by
    have := chars_ne b
    apply And.intro <;>
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, door_eq_not⟩ <;>
    simp [door_eq_not] at this <;>
    solve | exact door_eq_not | rfl

example (chars_ne: (b: Basic) → b.a.truther ≠ b.b.truther) :
  BasicSpec.SolutionN 1 := .of_solver_valid_and_n_asks
  fun asker ↦ do
    let ans ← asker <|.mk 0 fun ⟨⟨char, good⟩, _, _⟩ ↦ cond char good !good
    return cond ans 0 1
  fun b ↦ by
    have := chars_ne b
    apply And.intro <;>
    rcases b with ⟨⟨_|_, _|_⟩, ⟨_|_, _|_⟩, door_eq_not⟩ <;>
    simp [door_eq_not] at this ⊢ <;>
    solve | exact door_eq_not | rfl
