import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!

#  Definitions, Structures and Typeclasses

In mathematics, you often package together various different notions into a single one.
Here are a few examples:
* a basis of a vector space;
* the degree of a polynomial;
* whether a number is prime;
* a group, vector space, ring, field, algebra,...;
* whether a function `f : G → H` between groups is a group homomorphism;
* a zero-divisor in a ring;

and so on.

From a mathematical point of view, we would probably not have any problems calling all of
the items above "definitions".

However, when formalising these notions, we may exploit different parts of Lean's internal mechanism
to guide it and ultimately simplify our following efforts.

Lean has 3 keywords that can be used in the situations above:
* `def`;
* `structure`;
* `class`.

Knowing which one to use when normally means asking yourself "what is the expected usage of this notion".

Here is a somewhat heuristic description of the differences between the keywords and
the contexts in which they may be used.

##  `def`

A `def`inition in Lean is usually a "single" property, a function or a "statement".
For example, the degree of a polynomial is a function that takes a polynomial and returns a natural number.
This is a definition in `Mathlib`:
-/
#check Polynomial.natDegree    -- immediately followed by more definitions
#check Polynomial.leadingCoeff
#check Polynomial.Monic

#check Nat.Prime  -- slightly unusual, since `Irreducible` is a structure
#check Nat.minFac

/-

##  `structure`

This is typically a "collection" of properties that we would like to treat as a single "bundle".
For example
-/
#check Basis       --  a basis of a vector space
#check MonoidHom   --  a homomorphism of monoids (e.g. of groups!)
#check Units       --  the units in a monoid (e.g. in a ring)
#check SimpleGraph --  a simple, undirected, loopless graph

/-

##  `class`

This is very similar to structure, except that we would expect at most one such structure to be present on a given Type.
-/

#check Group
#check Ring
#check Field
#check NoZeroDivisors
#check TopologicalSpace
/-

Among `def`s, `structure`s and `class`es, the `class`es are the ones that are trickier.
Technically, a `class` is simply a `structure` that is visible to the typeclass system.
The typeclass system is the part of Lean that takes care of handling, synthesizing and discharging assumptions that appear inside square brackets (such as `[CommRing R] [Algebra R A]`,...).

Thus, when Lean sees `class`, it created a structure, but also adds the corresponding structure to its database of `class`es.
It will then look up at this database for figuring out that `Field` implies `AddCommGroup`, for instance.
To create an implication among typeclasses, you should prove that some `class` is a consequence of others (e.g. as before that `AddCommGroup` follows from `Field`).
You do this, by "proving" an `instance`.
In some sense, `class`es are the vertices and `instance`s are the edges in the "typeclass graph".
Lean uses this information in the background to simplify our formalisation.
-/
--@[ext]  --we will see later what this does!
structure point where
  x : ℝ
  y : ℝ

/-
Let's tell Lean that we want to be able to add two points, using component-wise addition.
This means that we will register an `Add` instance on `point`.
-/

variable (p q : point) in
#check p + q

instance : Add point where
  add p q := {
    x := p.x + q.x
    y := p.y + q.y
  }

variable (p q : point) in
#check p + q

instance : AddCommGroup point where
  add := (· + ·)
  add_assoc := by
    intros a b c
    ext
    · apply add_assoc
    · apply add_assoc
    done
  zero := { x := 0, y := 0 }  -- this can also be written as ⟨0, 0⟩
  zero_add := by
    intro a
    ext
    · apply zero_add
    · apply zero_add
    done
  add_zero := by
    intro a
    ext
    · apply add_zero
    · apply add_zero
    done
  neg := fun ⟨px, py⟩ => ⟨-px, -py⟩
  add_left_neg := by
    intro a
    ext
    · apply add_left_neg
    · apply add_left_neg
    done
  add_comm := by
    intros a b
    ext
    · apply add_comm
    · apply add_comm
    done

/-

In Lean, `typeclass` refers to a mathematical structure that is associated with a given "object".

Typeclasses are introduced by the `class` keyword.
Other than that

The difference between a `typeclass` and `structure` entails


Sometimes, the "definition" that you want to make is to endow some "object" with some "structure":
for instance you may want to define the component-wise addition on pairs of integers and
prove that what you defined is an (additive) abelian group.

Lean has a special mechanism to keep track of such "definitions" which, for instance, automatically allows
you to use `+` as a notation for the operation.
Another great feature is that if your newly defined `+`-operation actually induces an abelian group
(i.e. you proved this!), then Lean will already know that therefore it is also an `AddMonoid` and you will
be able to use the lemmas that `Mathlib` has about `AddMonoid`s.

This mechanism is called the *typeclass system* and it is mostly painless to use.
When assuming such a hypothesis (e.g. you want to prove a result about groups or topological spaces),
then these assumptions are written inside square bracket (e.g. `[Group G]` or `[TopologicalSpace X]`).
If you want a new object `N` that you defined to be registered by Lean as a `Group N`, then you should
provide an `instance` of `Group` to `N`.

Here is an example.
We introduce the notion of an additive group to the pairs of integers.


-/

#eval 0
