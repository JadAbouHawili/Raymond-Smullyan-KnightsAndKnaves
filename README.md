# Smullyan-KnightsAndKnaves
Problems from raymond smullyans book 'What is the name of this book', the knights and knaves chapter.

# Project Structure
There are three competing formalizations of knights and knaves.

## Set Theory Approach
The setup for this approach is in `settheory.lean`.
You can read about this setup and solve problems [here](https://adam.math.hhu.de/#/g/jadabouhawili/knightsandknaves-lean4game/world/KnightsAndKnavesLemmas/level/0)

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

# Formalization
Despite the different setups in lean, formalization adheres to the same ideas.

(When the server updates)
You can find an explanation of every approach in the introduction of the respective world.
