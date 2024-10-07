import Mathlib
import LogicPuzzles.QuestionProblem

inductive Character
| T -- always tells the truth
| F -- always lies
| R -- random
deriving Repr, DecidableEq

inductive Response
| X | Y
deriving Repr, DecidableEq
open Character Response

structure Boolo (gen := StdGen) [RandomGen gen] where
  (a b c : Character)
  translate : Bool ≃ Response
  unique : a ≠ b ∧ a ≠ c ∧ b ≠ c
  rng : gen

@[simp] theorem Boolo.translate_ne (b: Boolo) :
  b.translate true ≠ b.translate false := fun h ↦
    Bool.true_eq_false.mp <| b.translate.injective h

@[simp] theorem Boolo.translate_ne' (b: Boolo) (r: Response)
  (ht: b.translate true = r) (hf: b.translate false = r) : False :=
    b.translate_ne (ht.trans hf.symm)

abbrev Boolo.getChar (b: Boolo) : Fin 3 → Character
| 0 => b.a | 1 => b.b | 2 => b.c

abbrev BooloConfig := QuestionProblem.Config.CharIDer Character (Fin 3) Response
abbrev BooloSpec : QuestionProblem.Spec Boolo BooloConfig := fun b ↦
  {
  check := fun s ↦ s 0 = b.a ∧ s 1 = b.b ∧ s 2 = b.c
  ask := fun i q ↦ b.translate <| match b.getChar i with
  | T => q b
  | F => ! q b
  | R => randBool b.rng |>.1
  }

@[simp] def solver_hopefully : QuestionProblem.Solver Boolo BooloConfig := fun asker ↦ do
    let mut (id_a, id_b, id_c) := (R, R, R) -- default garbage
    let be_honest (translate : Bool ≃ Response) (char: Character) (q: Bool) :=
      ((translate true = X) = (char = T)) = q
    -- if r1 is X, then c is not random; if Y, then a is not random
    let r1 ← asker 1 fun ⟨a, b, _, translate, _, _⟩ ↦ be_honest translate b (a = R)
    let non_rando : BooloConfig.Idx := match r1 with | X => 2 | Y => 0
    let r2 ← asker non_rando fun ⟨a, _, c, translate, _, _⟩ ↦
      let you := match r1 with | X => c | Y => a
      be_honest translate you (you = F)
    let non_rando_id := match r2 with | X => F | Y => T
    match r1 with
    | X => id_c := non_rando_id
    | Y => id_a := non_rando_id
    let r3 ← asker non_rando fun ⟨a, b, c, translate, _, _⟩ ↦
      let you := match r1 with | X => c | Y => a
      be_honest translate you (b = R)
    let remaining_id := match r2 with
    | X => T
    | Y => F -- swapped from non_rando_id
    match r3 with
    | X =>
      id_b := R
      match r1 with
      | X => id_a := remaining_id
      | Y => id_c := remaining_id
    | Y =>
      id_b := remaining_id
      -- the remaining char is random
      match r1 with
      | X => id_a := R
      | Y => id_c := R
    return ![id_a, id_b, id_c]

instance : BooloSpec.Solution where
  solver := solver_hopefully
  valid b := by
    rcases hb:b with ⟨_|_|_, _|_|_, _|_|_, _, ⟨a_ne_b, a_ne_c, b_ne_c⟩, rng⟩ <;>
    try first
    | exact a_ne_b.irrefl.elim
    | exact a_ne_c.irrefl.elim
    | exact b_ne_c.irrefl.elim
    all_goals cases ht: b.translate true <;> cases hf: b.translate false <;>
    try exact Boolo.translate_ne' b _ ht hf |>.elim
    set_option maxHeartbeats 1 in
    all_goals solve
    | simp_all [pure, bind, WriterT.mk]
    | rcases hr: (randBool rng).1 with ⟨_|_⟩ <;> simp_all [pure, bind, WriterT.mk]

#eval let ctx : Boolo := {
        a := T, b := R, c := F,
        translate := {
          toFun := fun
          | true => X
          | false => Y
          invFun := fun
          | X => true
          | Y => false
          left_inv := by rintro ⟨_|_⟩ <;> exact rfl
          right_inv := by rintro ⟨_|_⟩ <;> exact rfl
        }
        unique := ⟨noConfusion, noConfusion, noConfusion⟩
        rng := mkStdGen
      }
      (BooloSpec.run solver_hopefully ctx).map id List.length
