import Mathlib

structure QuestionProblem.Config where
  (Character Idx Response Solution : Type*)
abbrev QuestionProblem.Question (α: Type*) := α → Bool
structure QuestionProblem (cfg: QuestionProblem.Config) (α: Type*) where
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

def Solver (α: Type _) (cfg: Config.{_,v₂,_,_}) := {M: _} → [Monad M] →
  ReaderT (Asker M α cfg) (WriterT (History α cfg) M) cfg.Solution
abbrev Solver.fromSpec (_: Spec α cfg) := Solver α

namespace Spec
abbrev run (spec: Spec α cfg) (solver: Solver α cfg) (a: α) :
  Writer (History α cfg) cfg.Solution := solver (spec a).loggedAsk
abbrev valid (spec: Spec α cfg) (solver: Solver α cfg) (a: α) : Prop :=
  (spec a).check <| spec.run solver a |>.1
abbrev asks_le_n (spec: Spec α cfg) (solver: Solver α cfg) (n: ℕ) (a: α) : Prop :=
  spec.run solver a |>.2.length ≤ n
structure Solution (self: Spec α cfg) where
  solver: Solver α cfg
  valid a: self.valid solver a
structure SolutionN (self: Spec α cfg) (n: ℕ) extends Solution self where
  asks_le_n a: self.asks_le_n solver n a
def SolutionN.of_solver_valid_and_n_asks {spec: Spec α cfg} {n: ℕ}
  (solver: Solver α cfg) (h: ∀a, spec.valid solver a ∧ spec.asks_le_n solver n a) :
  spec.SolutionN n := ⟨⟨solver, (h · |>.left)⟩, (h · |>.right)⟩

end Spec
attribute [simp] check ask loggedAsk Spec.run Spec.valid
