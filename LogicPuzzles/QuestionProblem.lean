import Mathlib

structure QuestionProblem.Config where
  (Character Idx Response Solution Ctx : Type*)
abbrev QuestionProblem.Config.Question (Cfg: QuestionProblem.Config) :=
  Cfg.Idx × ReaderM Cfg.Ctx Bool
structure QuestionProblem (Cfg: QuestionProblem.Config) where
  check : Cfg.Solution → Prop
  ask : Cfg.Question → Cfg.Response
namespace QuestionProblem
abbrev Config.CharPicker (n: ℕ) := (Config.mk · (Fin n) · (Fin n))
abbrev Config.CharIDer Character Idx :=
  (Config.mk Character Idx · (Idx → Character))

variable (Cfg: Config)

def Spec := Cfg.Ctx → QuestionProblem Cfg

abbrev History := List Cfg.Question
abbrev WriterHistT M [Monad M] Cfg := WriterT (History Cfg) (StateT Cfg.Ctx M)
abbrev AskerT M [Monad M] Cfg :=
  ReaderT (Cfg.Question) (WriterHistT M Cfg) Cfg.Response

abbrev loggedAsk (prob: QuestionProblem Cfg): AskerT Id Cfg := fun q ↦ do
  tell [q]
  return prob.ask q

def Solver := {M: Type _ → Type _} → [Monad M] →
  ReaderT (AskerT M Cfg) (WriterHistT M Cfg) Cfg.Solution

variable {Cfg}

abbrev Solver.ofSpec (_: Spec Cfg) := Solver Cfg

namespace Spec
abbrev run (spec: Spec Cfg) (solver: Solver Cfg) (ctx: Cfg.Ctx) :
  Cfg.Solution × History Cfg := @solver Id _ (spec ctx).loggedAsk ctx |>.1
abbrev valid (spec: Spec Cfg) (solver: Solver Cfg) (ctx: Cfg.Ctx) : Prop :=
  spec.run solver ctx |>.1 |> (spec ctx).check
abbrev asks_le_n (spec: Spec Cfg) (solver: Solver Cfg) (n: ℕ) (ctx: Cfg.Ctx) : Prop :=
  spec.run solver ctx |>.2.length ≤ n

structure Solution (spec: Spec Cfg) where
  solver: Solver Cfg
  valid ctx: spec.valid solver ctx
structure SolutionN (spec: Spec Cfg) (n: ℕ) extends Solution spec where
  asks_le_n ctx: spec.asks_le_n solver n ctx

def SolutionN.of_solver_valid_and_n_asks {spec: Spec Cfg} {n: ℕ}
  (solver: Solver Cfg) (h: ∀ctx, spec.valid solver ctx ∧ spec.asks_le_n solver n ctx) :
  spec.SolutionN n := ⟨⟨solver, (h · |>.left)⟩, (h · |>.right)⟩

end Spec
