import Mathlib

structure QuestionProblem.Config where
  (Character Idx Response Solution : Type*)
abbrev QuestionProblem.Question (α: Type*) := α → Bool
class QuestionProblem (cfg: QuestionProblem.Config) (α: Type*) where
  check : cfg.Solution → Prop
  ask : cfg.Idx → QuestionProblem.Question α → cfg.Response
namespace QuestionProblem
abbrev Config.CharPicker (n: ℕ) := (Config.mk · (Fin n) · (Fin n))
abbrev Config.CharIDer (Character Idx : Type*) :=
  (Config.mk Character Idx · (Idx → Character))

def Spec α cfg := α → QuestionProblem cfg α
abbrev History α cfg := List (Config.Idx cfg × Question α)
abbrev Asker M [Monad M] α cfg :=
  cfg.Idx → Question α → WriterT (History α cfg) M cfg.Response
abbrev loggedAsk (prob: QuestionProblem cfg α): Asker Id α cfg :=
  fun i q ↦ (prob.ask i q, [(i, q)])
def Solver α cfg := {M: Type _ → Type _} → [Monad M] → Asker M α cfg →
  WriterT (History α cfg) M cfg.Solution
abbrev Solver.fromSpec (_: Spec α cfg) := Solver α
namespace Spec
def valid (spec: Spec α cfg) (solver: Solver α cfg) (a: α): Prop :=
  (spec a).check <| @solver Id _ (spec a).loggedAsk |>.1
def n_asks (spec: Spec α cfg) (solver: Solver α cfg) (n: ℕ) (a: α) : Prop :=
  @solver Id _ (spec a).loggedAsk |>.2.length = n
structure Solution (self: Spec α cfg) where
  solver: Solver α cfg
  valid a: self.valid solver a
structure SolutionN (self: Spec α cfg) (n: ℕ) extends Solution self where
  n_asks a: self.n_asks solver n a
def SolutionN.of_solver_valid_and_n_asks {spec: Spec α cfg} {n: ℕ}
  (solver: Solver α cfg) (h: ∀a, spec.valid solver a ∧ spec.n_asks solver n a) :
  spec.SolutionN n := ⟨⟨solver, (h · |>.left)⟩, (h · |>.right)⟩

end Spec
attribute [simp] check ask loggedAsk Spec.valid Spec.n_asks
