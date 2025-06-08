# Smullyan-KnightsAndKnaves
Problems from raymond smullyans book 'What is the name of this book', the knights and knaves chapter.

# Project Structure
There are three competing formalizations of knights and knaves.

## Set Theory Approach
The setup for this approach is in `settheory.lean`.
You can read about this setup and solve problems [here](https://adam.math.hhu.de/#/g/jadabouhawili/knightsandknaves-lean4game/world/KnightsAndKnavesLemmas/level/0)

This approach has many custom theorems(some used to solve puzzles and some not) concerning sets.
You can forgo these and only have the basic setup.

## Domain Specific Language(DSL) Approach
The setup for this approach is in `dsl_knights_knaves.lean`.
You can read about this setup and solve problems [here](https://adam.math.hhu.de/#/g/jadabouhawili/knightsandknaves-lean4game/world/DSL_Knights_Knaves/level/0)

## Propositional Approach
This setup doesn't have its own file.

You just declare islanders say `A,B,C` as propositions:
```
A B C : Prop
```
and use the logic theorems available in lean.

You can read about this setup and solve problems [here](https://adam.math.hhu.de/#/g/jadabouhawili/knightsandknaves-lean4game/world/KnightsAndKnaves2/level/0)

## How to solve any puzzle
You can take all cases of all islanders, then execute `tauto` which would break down the goal and fill truth values in the hypothesis and the goal. If the goal reduces to true, then you are done and if a hypothesis reduces to false then there was a contradiction and the goal can be closed. The way `tauto` actually works is a bit more complicated than that, you could also try `simp [*] at *` to use all simp lemmas on all hypothesis.

There are other provers that might be more suited for this however.
You can look into:
- SMT solvers
- [Prolog](https://www.youtube.com/watch?v=oEAa2pQKqQU)

## Translation between puzzles
Puzzles can translated from one representation to the other, and the solution as well.

We have the following correspondence:
| Set Theory       | DSL           | Propositional  |
| ------------- |:-------------:| -----:|
| `h : A ∈ Knight`  | `h : A.isKnight` | `h : A` |
| `h : A ∉ Knight` | `h : ¬A.isKnight` | `h : ¬A` |
| `h : A ∈ Knave`  | `h : A.isKnave` | `h : ¬A` |
| `h : A ∉ Knave`  | `h : ¬A.isKnave` | `h : ¬¬A` |
| `h : A ∈ Knight ∨ A ∈ Knave` | `h : A.isKnight or A.isKnave` | `h : A ∨ ¬A` |
| `h : Knight ∩ Knave = ∅` | `h : not (A.isKnight and A.isKnave)` | `h: ¬(A ∧ ¬A)`  |


Note for `¬¬A`, it is equivalent to `A`

