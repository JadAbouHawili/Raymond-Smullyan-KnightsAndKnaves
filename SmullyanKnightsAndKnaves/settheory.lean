import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic

import SmullyanKnightsAndKnaves.logic

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.DeriveFintype

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic


#check Prop
open Finset

#check eq_univ_iff_forall


section

variable {K : Type} [DecidableEq K] 
variable (A B C : K)
variable (all : ∀ x : K, x = A ∨ x = B ∨ x = C)
----example :
--  (Finset.univ : Finset K) = ({A,B,C} : Finset K) := by
--  ext x
--  simp [Finset.mem_univ, all]


-- construct an actual instance using the axiom
instance : Fintype K :=
{ elems := ({A, B, C} : Finset K),
  complete := by
    intro x
    rcases all x with rfl | rfl | rfl
    <;> simp }
example : Finset K := by
  let foo := instFintype_smullyanKnightsAndKnaves A B C all -- add instance manually because
                                    -- typeclass inference won't do it
  let bar : Finset K := Finset.univ
  have : Finset.univ = {A,B,C} := by
    /-
    just having variable [Fintype K]
    ext x
    simp
    exact all x
    -/
    rfl

  exact bar
end






--works
section
-- would solve problems?
class HasThreeElems (K : Type*) where
  A : K
  B : K
  C : K
  all : ∀ x : K, x = A ∨ x = B ∨ x = C

variable {K : Type*} [DecidableEq K] [HasThreeElems K]

-- needed instances [decidableeq] [HasThreeElems] , previously there where implicit variables like {A,B,C,all} that didn't allow ynthesis because the system couldn't find them...
instance : Fintype K :=
  ⟨({HasThreeElems.A, HasThreeElems.B, HasThreeElems.C} : Finset K),
   by
     intro x
     simp [HasThreeElems.all]⟩

open HasThreeElems
example :
    (Finset.univ : Finset K)
      = ({A, B, C} : Finset K) := by
  rfl 
  -- works
  --ext x
  --simp [HasThreeElems.all]
end



#check Insert
#check Finset.instInsert
#check insert_idem
#check Finset
#check Finset.instUnion
#check Finset.instHasSubset
#check Finset.instMembership
#check Finset.card_singleton_inter
#check Finset.instInter
#check Finset.instUnion
#check Finset.instSetLike

infixr:35 " and " => And
infixr:30 " or  "  => Or

#check Set.mem_insert_iff
#check Set.mem_singleton
#check Lean.Parser.Tactic.locationHyp

--  a ∈ {a}
#check Finset.mem_singleton_self
-- a ∈ insert a s
#check Finset.mem_insert_self
-- a ∈ s → a ∈ insert b s
#check Finset.mem_insert_of_mem
#check Finset.mem_inter.mpr

variable {K : Type} {A : K} 
[DecidableEq K] {AA : Finset K}
#check AA ∪ AA
#check Union.union
#check Finset.instInter
example
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(h' : A ∈ S') : A ∉ S := by
  intro a
  have := Finset.mem_inter_of_mem h' a
  rw [Finset.inter_comm] at h
  rw [h] at this
  contradiction

theorem disjoint_finset
{left right : Finset K}
(h : left ∩ right = ∅ )
(hk : A ∈ left)
(hkn : A ∈ right)  : False := by
  have := Finset.mem_inter_of_mem hk hkn
  rw [h] at this
  contradiction

-- potentially unncessary
--macro_rules
--| `(tactic| contradiction) =>
--  do `(tactic |solve  | ( try (apply disjoint_finset ; repeat assumption) ) )
--
omit [DecidableEq K] in
theorem disjoint_set
{left : Set K} {right : Set K}
(h : left ∩ right = ∅ )
(hk : A ∈ left)
(hkn : A ∈ right)  : False := by
  have := Set.mem_inter hk hkn
  rw [h] at this
  contradiction
-- potentially unnecessary
--macro_rules
--| `(tactic| contradiction) =>
--  do `(tactic |solve  | ( apply disjoint_set ; repeat assumption ) )


theorem inleft_notinright_finset
{S S' : Finset K}
{A : K}
(h : S ∩ S' = ∅ )
(h' : A ∈ S) : A ∉ S' := by
  intro a
  have := Finset.mem_inter_of_mem h' a
  rw [h] at this
  contradiction
#print inleft_notinright_finset

theorem notinleft_inright
{S S' : Finset K}
{A : K}
(SorS' : A ∈ S ∨ A ∈ S')
(h' : A ∉ S) : A ∈ S' := by
  exact notleft_right SorS' h'

theorem inright_notinleft_finset
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(h' : A ∈ S') : A ∉ S := by
  intro a
  have := Finset.mem_inter_of_mem h' a
  rw [Finset.inter_comm] at h
  rw [h] at this
  contradiction

theorem notinright_inleft
{S S' : Finset K}
(SorS' : A ∈ S ∨ A ∈ S')
(h' : A ∉ S') : A ∈ S := by
  exact notright_left SorS' h'

-------------------
theorem inleft_notinrightIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∈ S ↔  ¬(A ∈ S') := by
  constructor
  · exact inleft_notinright_finset h
  · exact notinright_inleft SorS'

theorem notinleft_inrightIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∉ S ↔  A ∈ S' := by
  constructor
  · exact notinleft_inright SorS'
  · exact inright_notinleft_finset h

theorem inright_notinleftIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∈ S' ↔  A ∉ S := by
  constructor
  · exact inright_notinleft_finset h
  · exact notleft_right SorS'

theorem notinright_inleftIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
 : A ∉ S' ↔  A ∈ S := by
  constructor
  · exact notinright_inleft SorS'
  · exact inleft_notinright_finset h

open Finset


--↥ coercing a finset into a type(where is this symbol even defined...)
#check Finset.coe_sort_coe -- Coerce `s : Finset α` to the type of all `x ∈ s`
-- find document for double up arrow , ↥ etc...
#check Finset.fintypeCoeSort 
#check Fintype.card_coe
#check Finset.card_singleton
#check Finset.card_insert_of_notMem
/-
some resources
pbs infinity series

💤 lattice theory - YouTube
https://www.youtube.com/results?search_query=lattice+theory

💤 Universal Algebra and Lattice Theory - Lecture 1: Introduction and Background - YouTube
https://www.youtube.com/watch?v=3JNn-vggUH4&list=PLkNMPCqtfFRTbWTgXabLJZGnyt7koG8KR

💤 Lattice-Based Cryptography: The Tricky Math of Dots - YouTube
https://www.youtube.com/watch?v=QDdOoYdb748&t=115s

💤 Chalk Talk - YouTube
https://www.youtube.com/@chalktalkmath

💤 Lattice-based cryptography - Wikipedia
https://en.wikipedia.org/wiki/Lattice-based_cryptography

💤 Lattice (group) - Wikipedia
https://en.wikipedia.org/wiki/Lattice_(group)

💤 Square lattice - Wikipedia
https://en.wikipedia.org/wiki/Square_lattice

💤 sets as lattices at DuckDuckGo
https://duckduckgo.com/?t=ffab&q=sets+as+lattices&ia=web

a new tomorrow alan ellis - YouTube
https://www.youtube.com/results?search_query=a+new+tomorrow+alan+ellis

💤 The Music Channel - YouTube
https://www.youtube.com/channel/UC-9-kyTW8ZkZNDHQJ6FgpwQ

💤 General Profile :: math.ucdavis.edu
https://www.math.ucdavis.edu/people/general-profile?fac_id=babson

💤 Ethan Vosburg - YouTube
https://www.youtube.com/@ethanvosburg/videos

💤 Lattice Coding Theory - Introduction - YouTube
https://www.youtube.com/watch?v=AWozmtOlTbE

💤 Lattice (order) - Wikipedia
https://en.wikipedia.org/wiki/Lattice_(order)

💤 A lattice is a join-semilattice which is also a meet-semilattice. - at DuckDuckGo
https://duckduckgo.com/?t=ffab&q=A+lattice+is+a+join-semilattice+which+is+also+a+meet-semilattice.+-&ia=web

Semilattice - Wikipedia
https://en.wikipedia.org/wiki/Semilattice

💤 mathematics in lean 4 lattices at DuckDuckGo
https://duckduckgo.com/?t=ffab&q=mathematics+in+lean+4+lattices&ia=web


Mathlib.Data.Finset.Defs
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Defs.html#Finset.instHasSubset

💤 Init.Core
https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#HasSubset

💤 finite intersections sets lean 4 at DuckDuckGo
https://duckduckgo.com/?t=ffab&q=finite+intersections+sets+lean+4&ia=web

💤 Maths in Lean: Sets and set-like objects
https://leanprover-community.github.io/theories/sets.html

💤 coerce to a type lean 4 at DuckDuckGo
https://duckduckgo.com/?t=ffab&q=coerce+to+a+type+lean+4&ia=web

💤 Coercing to Function Types
https://lean-lang.org/doc/reference/latest/Coercions/Coercing-to-Function-Types/

💤 Coercing to Sorts
https://lean-lang.org/doc/reference/latest/Coercions/Coercing-to-Sorts/#sort-coercion

Mathlib.Data.Finset.Lattice.Basic
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Lattice/Basic.html

(50014) Jon Eugster - Lean - Zulip
https://leanprover.zulipchat.com/#narrow/dm/385895-Jon-Eugster

💤 (49993) #mathlib4 > `Fintype` / `DecidablePred` confusion with `Subgroup` - Lean - Zulip
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/.60Fintype.60.20.2F.20.60DecidablePred.60.20confusion.20with.20.60Subgroup.60/with/580814743

💤 (49993) #new members > Question about CIC expressiveness — type reification without - Lean - Zulip
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Question.20about.20CIC.20expressiveness.20.E2.80.94.20type.20reification.20without/with/580745432

💤 (49993) #general > Lean community awards? - Lean - Zulip
https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Lean.20community.20awards.3F/with/580787077

💤 (49994) #mathlib4 > linter requests - Lean - Zulip
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/linter.20requests/with/580813314

💤 (49994) #mathlib4 > le_mul_left - Lean - Zulip
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/le_mul_left/with/580631119

💤 (49994) #new members > `rfl` does not work on definitionally equal terms - Lean - Zulip
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/.60rfl.60.20does.20not.20work.20on.20definitionally.20equal.20terms/with/580475574

💤 (49994) #new members > stuck in the realanalysis game - Lean - Zulip
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/stuck.20in.20the.20realanalysis.20game/with/580581454

💤 (49994) #general > Make mathlib less dependent on choice - Lean - Zulip
https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Make.20mathlib.20less.20dependent.20on.20choice/with/580403392

💤 (49994) #mathlib4 > Absence of corollaries in Mathlib - Lean - Zulip
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Absence.20of.20corollaries.20in.20Mathlib/with/580434031

💤 (49994) #mathlib4 > Unused Decidable Instances linter - Lean - Zulip
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Unused.20Decidable.20Instances.20linter/with/580273784

-/

#check instDecidableEqBool
#check Finset.mem_insert_of_mem
#check Finset.mem_insert

#check Finset.univ

theorem univ_iff_all
{K : Type}
[ DecidableEq K]
 [ inst: Fintype K]
{A B C : K}
: Finset.univ = ({A,B,C} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by
  rw [eq_comm]
  exact Iff.trans Finset.eq_univ_iff_forall (by simp)

theorem set_subset_univ3
{A B C : K}
 {S : Finset K}
(all : ∀ (x : K), x = A ∨ x = B ∨ x = C)
: S ⊆ ({A,B,C} : Finset K) := by
  intro x h ; simp ;  exact all x


theorem set_subset_univ2
{A B : K}
 {S : Finset K}
(all : ∀ (x : K), x = A ∨ x = B )
: S ⊆ ({A,B} : Finset K) := by
  intro x h ; simp ;  exact all x
