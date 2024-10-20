import Mathlib

structure QuestionProblem.Config where
  (Character Idx Response Solution Ctx : Type*)
abbrev QuestionProblem.Config.Question (Cfg: Config) :=
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
abbrev WriterHistT M [Monad M] := WriterT (History Cfg) (StateT Cfg.Ctx M)
abbrev AskerT M [Monad M] :=
  ReaderT Cfg.Question (WriterHistT Cfg M) Cfg.Response

abbrev loggedAsk (prob: QuestionProblem Cfg): AskerT Cfg Id := fun q ↦ do
  tell [q]
  return prob.ask q

def Solver := {M: Type _ → Type _} → [Monad M] →
  ReaderT (AskerT Cfg M) (WriterHistT Cfg M) Cfg.Solution

variable {Cfg} (spec: Spec Cfg)

abbrev Solver.ofSpec := Solver Cfg

namespace Spec

section Running
variable (solver: Solver Cfg) (ctx: Cfg.Ctx)
abbrev run : Cfg.Solution × History Cfg := solver (spec ctx).loggedAsk ctx |>.1
abbrev valid : Prop := spec ctx |>.check <| spec.run solver ctx |>.1
abbrev asks_le_n (n: ℕ) : Prop := spec.run solver ctx |>.2.length ≤ n
end Running

structure Solution where
  solver: Solver Cfg
  valid [Monad M] ctx: spec.valid solver ctx
structure SolutionN (n) extends Solution spec where
  asks_le_n [Monad M] ctx: spec.asks_le_n solver ctx n

def SolutionN.of_solver_valid_and_n_asks {spec: Spec Cfg} {n} solver
  (h: ∀ctx, spec.valid solver ctx ∧ spec.asks_le_n solver ctx n) :
  spec.SolutionN n := ⟨⟨solver, (h · |>.left)⟩, (h · |>.right)⟩

end Spec
