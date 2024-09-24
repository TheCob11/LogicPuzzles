import Mathlib

structure QuestionProblem.Config where
  (Character Idx Response Solution : Type*)
abbrev QuestionProblem.Config.Question (cfg: Config) := cfg.Character → Bool
class QuestionProblem (cfg: QuestionProblem.Config) where
  check : cfg.Solution → Prop
  ask : cfg.Idx → cfg.Question → cfg.Response
namespace QuestionProblem

abbrev Config.CharPicker (n: ℕ) := (Config.mk · (Fin n) · (Fin n))

def Solver (cfg) := QuestionProblem cfg → cfg.Solution
def valid (self: QuestionProblem cfg) (solver: Solver cfg) : Prop :=
  self.check (solver self)

def Spec (α: Type*) (cfg) := α → QuestionProblem cfg
abbrev Spec.Problem (_: Spec α cfg) := QuestionProblem cfg
-- this doesn't just take in a problem because if it did the solver could
-- know about it
structure Spec.Solution (self: Spec α cfg) where
  solver : Solver cfg
  all_valid : ∀a: α, (self a).valid solver

def CountingAsker (cfg: Config) {M} [Monad M] :=
  (QuestionProblem cfg → cfg.Idx × cfg.Question) →
    WriterT (Multiplicative ℕ) M cfg.Response
def CountingSolver (cfg: Config) := {M: Type → Type} → [Monad M] →
    @CountingAsker cfg M _ → WriterT (Multiplicative ℕ) M cfg.Solution
abbrev CountingSolver.run (self: CountingSolver cfg) (prob: QuestionProblem cfg) :
  Writer (Multiplicative ℕ) cfg.Solution :=
  self (prob.ask.uncurry <| · prob, .ofAdd 1)
structure Spec.SolutionN (spec: Spec α cfg) (n: ℕ) where
  solver : CountingSolver cfg
  all_valid : ∀a: α, (spec a).check (solver.run (spec a)).1
  asks_le_n : ∀a: α, (solver.run (spec a)).2 ≤ n

attribute [simp] check ask valid CountingSolver.run
