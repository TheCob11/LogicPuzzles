import Mathlib

structure QuestionProblem.Config where
  (Character Idx Response Solution : Type*)
abbrev QuestionProblem.Question (Ctx: Type _) := ReaderM Ctx Bool
structure QuestionProblem (Ctx) (Cfg: QuestionProblem.Config) where
  check : Cfg.Solution → Prop
  ask : Cfg.Idx → QuestionProblem.Question Ctx → Cfg.Response
namespace QuestionProblem

abbrev Config.CharPicker (n: ℕ) := (Config.mk · (Fin n) · (Fin n))
abbrev Config.CharIDer Character Idx :=
  (Config.mk Character Idx · (Idx → Character))

def Spec Ctx Cfg := Ctx → QuestionProblem Ctx Cfg

abbrev History Ctx Cfg := List (Config.Idx Cfg × Question Ctx)
abbrev WriterHistT M [Monad M] Ctx Cfg := WriterT (History Ctx Cfg) (StateT Ctx M)
abbrev AskerT M [Monad M] Ctx Cfg :=
  Cfg.Idx → ReaderT (Question Ctx) (WriterHistT M Ctx Cfg) Cfg.Response

abbrev loggedAsk (prob: QuestionProblem Ctx Cfg): AskerT Id Ctx Cfg := fun i q ↦ do
  tell [(i, q)]
  return prob.ask i q

def Solver Ctx Cfg := {M: _} → [Monad M] →
  ReaderT (AskerT M Ctx Cfg) (WriterHistT M Ctx Cfg) Cfg.Solution

abbrev Solver.ofSpec (_: Spec Ctx Cfg) := Solver Ctx

namespace Spec
abbrev run (spec: Spec Ctx Cfg) (solver: Solver Ctx Cfg) (ctx: Ctx) :
  Cfg.Solution × History Ctx Cfg := @solver Id _ (spec ctx).loggedAsk ctx |>.1
abbrev valid (spec: Spec Ctx Cfg) (solver: Solver Ctx Cfg) (ctx: Ctx) : Prop :=
  spec.run solver ctx |>.1 |> (spec ctx).check
abbrev asks_le_n (spec: Spec Ctx Cfg) (solver: Solver Ctx Cfg) (n: ℕ) (ctx: Ctx) : Prop :=
  spec.run solver ctx |>.2.length ≤ n

structure Solution (spec: Spec Ctx Cfg) where
  solver: Solver Ctx Cfg
  valid ctx: spec.valid solver ctx
structure SolutionN (spec: Spec Ctx Cfg) (n: ℕ) extends Solution spec where
  asks_le_n ctx: spec.asks_le_n solver n ctx

def SolutionN.of_solver_valid_and_n_asks {spec: Spec Ctx Cfg} {n: ℕ}
  (solver: Solver Ctx Cfg) (h: ∀ctx, spec.valid solver ctx ∧ spec.asks_le_n solver n ctx) :
  spec.SolutionN n := ⟨⟨solver, (h · |>.left)⟩, (h · |>.right)⟩

end Spec
