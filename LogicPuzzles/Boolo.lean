import Mathlib
import LogicPuzzles.QuestionProblem

inductive Character
| T -- always tells the truth
| F -- always lies
| R -- random
deriving DecidableEq

inductive Response
| X | Y
deriving DecidableEq
open Character Response

structure Boolo (gen := StdGen) [RandomGen gen] where
  (a b c : Character)
  translate : Bool ≃ Response
  rng : gen

abbrev Boolo.chars (b: Boolo) := [b.a, b.b, b.c]

abbrev BooloConfig := QuestionProblem.Config.CharIDer Character (Fin 3) Response
abbrev BooloSpec : QuestionProblem.Spec Boolo BooloConfig := fun b ↦ {
  check := fun s ↦ s 0 = b.a ∧ s 1 = b.b ∧ s 2 = b.c
  ask := fun i q ↦ b.translate <| match b.chars[i] with
  | T => q b
  | F => ! q b
  | R => randBool b.rng |>.1
}

example : BooloSpec.SolutionN 1 := .of_solver_valid_and_n_asks
  fun asker ↦ do
    let mut (a, b, c) := (none, none, none)
    let r1 ← asker 0 fun prob ↦
      ((BooloSpec prob).ask 0 fun _ ↦ true) == X
    match r1 with
    | X =>
      a := some R
      let r2 ← asker 1 sorry
      (b, c) := match r2 with
      | X => (T, F)
      | Y => (F, T)
    | Y => (b, c) := (some R, some R)
    return fun
    | 0 => a.get sorry
    | 1 => b.get sorry
    | 2 => c.get sorry
  fun b ↦
    sorry
