# Smullyan-KnightsAndKnaves
Problems from raymond smullyans book 'What is the name of this book', the knights and knaves chapter.

# Project Structure
There are three competing formalizations of knights and knaves.

## Set Theory Approach
The setup for this approach is in `settheory.lean`.

## Domain Specific Language(DSL) Approach
The setup for this approach is in `dsl_knights_knaves.lean`.

## Propositional Approach
There is no custom setup

You just declare islanders say `A,B,C` as propositions:
```
A B C : Prop
```
and use the logic theorems available in lean.

# Formalization
Despite the different setups in lean, formalization adheres to the same ideas.

(When the server updates)
You can find an explanation of every approach in the introduction of the respective world.
