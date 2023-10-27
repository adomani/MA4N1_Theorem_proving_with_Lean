import Mathlib.Tactic

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

A `def`inition in Lean is ∀


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
