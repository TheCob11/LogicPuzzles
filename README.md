# LogicPuzzles
Formalizing logic puzzles in Lean4

Currently just "question problems" where there are some (arbitrary) characters and you have to ask them yes/no questions and based on their (arbitrary) responses determine an (arbitrary) solution

So far:
- Formalized [`QuestionProblem`](/LogicPuzzles/QuestionProblem.lean), including mechanisms for solutions and solutions with n questions
- Formalized and offered a bunch of solutions to [Knights and Knaves](/LogicPuzzles/KnightsAndKnaves.lean) (two guards, truther/liar and good door/bad door)
- Hopefully working towards [The Hardest Logic Puzzle Ever [Wikipedia]](https://en.wikipedia.org/wiki/The_Hardest_Logic_Puzzle_Ever)