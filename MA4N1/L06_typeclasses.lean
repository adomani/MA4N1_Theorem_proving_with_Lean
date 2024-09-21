import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace TPwL_typeclasses

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

Here we look at the 3 keywords
* `def`;
* `structure`;
* `class`;

that Lean has to generate new definitions.

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
@[ext]  --we will see later what this does!
structure point where
  x : ℝ
  y : ℝ

/-
Let's tell Lean that we want to be able to add two points, using component-wise addition.
This means that we will register an `Add` instance on `point`.
-/

variable (p q : point) in
/--
error: failed to synthesize
  HAdd point point ?m.1133
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check p + q

instance : Add point where
  add p q := {
    x := p.x + q.x
    y := p.y + q.y
  }

variable (p q : point) in
#check p + q

/-!
We want to inform Lean that `point` has the structure of an (additive) commutative group,
where the operations are the "obvious" ones (component-wise addition).

Note that in our informal description above of the "commutative group structure", we reference
the *operations* and say that `point` is a group with respect to those operations.
This brings up the distinction between "data" and "`Prop`":
* the operations are "data";
* the properties that these operations satisfy are "`Prop`".

This distinction is equally important in formal and informal mathematics,
though it is more *explicit* in formal maths.

Informal mathematics sometimes blurs the distinction between the two.
For instance, when we say that `point` is a group with with respect to the usual operations,
we are being very implicit about what is the `zero` of the group operation.
After all, the general theory guarantees that a group has a unique zero, so, technically,
we do not have to provide one.
However, it turns out that for formalization it is more convenient to be as explicit as possible
about what the unit of our operation is (and more generally, about everything!).

In this case, we isolate the definition of the zero element and of the opposite.
The reason for isolating these two fields has more to do with a Lean-language detail, than anything
mathematical.

Note that both `zero` and `neg` are "data", and that there is more "data" in the
additive commutative group instance on `point`.
-/

instance : Zero point where zero := {x := 0, y := 0}
-- the above instance can also be written as
-- `instance : Zero point := ⟨{x := 0, y := 0}⟩`
-- or even as
-- `instance : Zero point := ⟨⟨0, 0⟩⟩`

instance : Neg point where neg a := ⟨-a.x, -a.y⟩

instance : AddCommGroup point where
  add a b          := a + b
  add_assoc a b c  := by ext <;> apply add_assoc
  zero_add a       := by ext <;> apply zero_add
  add_zero a       := by ext <;> apply add_zero
  nsmul            := nsmulRec -- do not worry about this: hover for info and ask if you want more!
  zsmul            := zsmulRec -- do not worry about this: hover for info and ask if you want more!
  neg_add_cancel a := by ext <;> apply neg_add_cancel
  add_comm a b     := by ext <;> apply add_comm

/-
From now, Lean knows that the `structure` that we called `point` is an additive commutative group.
In particular, all the lemmas in the library that apply to `AddCommGroup` also apply to `point`!
-/

example {p q r : point} : r + p + q - r = p + q := by
  abel  -- tries to solve goals in abelian groups (additive or multiplicative)
  done

/-
`Mathlib` has a very intricate hierarchy of structures and typeclasses linking them:
to get an impression, think about how many "structures" there are between a "bare" Type and
and `Field`.

The graphs in [this post](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/instance.20graphs/near/378851049)
were the actual instance graphs in `Mathlib` a few months ago.

While the process of adding typeclass assumptions to `structure`s is as easy as adding
hypotheses in square brackets, there are a couple of issues to keep in mind.

###  `extends` vs assumption

A `structure` can `extend` a typeclass or it can take the typeclass as an assumption.
Here is the difference.
-/

section right_and_wrong_structures

-- structure `A` expects to find already the typeclass `Add` on `α`
structure A (α : Type) [Add α] where

/--
error: failed to synthesize
  Add α
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
variable {α : Type} (h : A α)         -- fails
variable {α : Type} [Add α] (h : A α) -- works

-- structure `B` will add the typeclass `Add` on `α`
structure B (α : Type) extends Add α where

variable {α : Type} (h : B α)  -- works

end right_and_wrong_structures

/-
###  Putting a typeclass assumption twice on the same type

This mistake leads to confusing errors.
It happens when you accidentally (or unknowingly) put two different assumptions on a Type that
imply the same typeclass.
-/

example {α : Type} /-
    [Add α] --/
    [CommRing α] (a b : α) :
    a + b - b = a := by
  exact? says exact Eq.symm (eq_sub_of_add_eq rfl)
  done

class group (G : Type) where
  id        : G
  mul       : G → G → G
  inv       : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  mul_inv   : ∀ g, mul g (inv g) = id
  -- and so on

end TPwL_typeclasses
