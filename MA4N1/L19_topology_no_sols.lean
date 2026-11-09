import MA4N1.Init
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.UpperLowerSetTopology

namespace TPwL_topology_no_sols

/-!
#  Topological spaces in `Mathlib`

In this file, we look at how `Mathlib` deals with topological spaces.

Recall the definition that you have probably seen in a first course on topology.
A *topological space* is a set `X`, together with a collection of subsets of `X`,
called the *open sets*, satisfying the following axioms:
* the empty set `∅` and the whole set `X` are open;
* the intersection of two open sets is open;
* the union of an arbitrary family of open sets is open.

We already briefly met `TopologicalSpace` in the lecture on typeclasses: it is a `class`.
As usual, let's see the definition.
-/

#print TopologicalSpace

/--
A copy of `Mathlib`'s `TopologicalSpace`.

As usual, note the lower-case `t`, to avoid confusing Lean when we later use
`Mathlib`'s `TopologicalSpace`.
-/
class topologicalSpace (X : Type*) where
  /-- A predicate saying that a set is an open set. -/
  IsOpen : Set X → Prop
  /-- The whole space is an open set. -/
  isOpen_univ : IsOpen Set.univ
  /-- The intersection of two open sets is an open set. -/
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- The union of a family of open sets is an open set. -/
  isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

/-!
A few comments are in order.
* Rather than a *collection* of open subsets, there is a *predicate* `IsOpen : Set X → Prop`.
  The two points of view are equivalent: the collection of open sets is `{s | IsOpen s}`;
  conversely, given the collection, a set is open if and only if it belongs to the collection.
* There is no axiom saying that the empty set is open!
  Can you see why it is not needed?
  You will prove that `∅` is open in one of the exercises below.
* The axiom on intersections only mentions *two* open sets.
  By induction, finite intersections of open sets are open.
* The axiom on unions uses `⋃₀ s`: here `s : Set (Set X)` is a set of subsets of `X`
  and `⋃₀ s` is the union of all the elements of `s`.

In `Mathlib`, the fields of `TopologicalSpace` are `protected`:
you will (almost) never use them directly.
Instead, there is an API (remember the lecture on developing an API around new definitions!)
that you should use.
-/

#check IsOpen
#check isOpen_univ
#check IsOpen.inter
#check isOpen_sUnion
#check isOpen_empty  -- this is a lemma, not an axiom!
#check IsOpen.union
#check isOpen_iUnion -- the union of an indexed family `⋃ i, s i` of open sets is open

/-!
##  A short digression on `Set`

We already met `Set X` when talking about graphs: it is the Type of subsets of `X`.
Under the hood, a subset of `X` is simply a predicate on `X`, i.e. a function `X → Prop`:
the elements of the subset are the terms of `X` that satisfy the predicate.
-/

#print Set

/-!
Here is a summary of the most common notation.

* `x ∈ s`    -- `x` is an element of `s` (type `\in`);
* `s ⊆ t`    -- `s` is contained in `t` (type `\subseteq`);
* `s ∩ t`    -- the intersection of `s` and `t` (type `\cap`);
* `s ∪ t`    -- the union of `s` and `t` (type `\cup`);
* `sᶜ`       -- the complement of `s`;
* `s \ t`    -- the elements of `s` that are not in `t`;
* `∅`        -- the empty set (type `\empty`);
* `Set.univ` -- the whole of `X`;
* `{x | p x}` -- the set of all `x` satisfying the property `p x`;
* `f ⁻¹' s`  -- the preimage of `s` under the function `f`;
* `f '' s`   -- the image of `s` under the function `f`;
* `Set.Ici a, Set.Icc a b, Set.Ioo a b, ...` -- intervals `[a, ∞)`, `[a, b]`, `(a, b)`, ...

To prove that two sets are equal, the tactic `ext x` reduces the goal to showing that an
element `x` belongs to one if and only if it belongs to the other.
Very often, `simp` can then take over.
-/

section sets

variable {α β : Type*}

example (f : α → β) (s t : Set β) : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := by
  ext x
  simp
  done

example (f : α → β) (s : Set β) : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ := by
  ext x
  simp
  done

end sets

section generic

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-!
###  Exercises

In the next two exercises, try to only use `isOpen_sUnion`, rather than `Mathlib`'s
`isOpen_empty` and `IsOpen.union`.

Hint: `Set.sUnion_empty` and `Set.sUnion_pair` express `∅` and `s ∪ t` as unions of sets.
-/

--  The empty set is the union of the empty family of subsets.
example : IsOpen (∅ : Set X) := by
  sorry
  done

example {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) := by
  sorry
  done

/-!
##  Closed sets

A set is closed if its complement is open.
Perhaps surprisingly, `IsClosed` is a `class` with a single field.
-/

#print IsClosed
#check isOpen_compl_iff
#check IsClosed.isOpen_compl

/-!
Remember that "not open" does *not* mean "closed":
a set can be both open and closed (`IsClopen`), or neither.
-/

example {s t : Set X} (hs : IsClosed s) (ht : IsOpen t) : IsOpen (t \ s) := by
  sorry
  done

example {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∪ t) := by
  sorry
  done

/-!
##  Continuous functions

As in your topology course, a function is continuous if
the preimage of every open set is open.
-/

#print Continuous
#check continuous_def

/-!
The docstring of `Continuous` says that it is a `structure` (rather than a `def`)
"to make sure it is not unfolded by Lean".
* To *prove* `Continuous f`, you can use `rw [continuous_def]`
  (or `constructor`, but see below for a caveat).
* To *use* a hypothesis `hf : Continuous f`, you can use `hf.isOpen_preimage`
  (this is dot-notation for `Continuous.isOpen_preimage hf`), or `rw [continuous_def] at hf`.
-/

--  Hint: `(g ∘ f) ⁻¹' s` and `f ⁻¹' (g ⁻¹' s)` are equal *by definition*.
example {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := by
  sorry
  done

/-!
Of course, this is already in `Mathlib`, along with many other results.
-/

#check continuous_id
#check continuous_const
#check Continuous.comp
#check Continuous.add
#check Continuous.mul

/-!
In practice, you will rarely prove continuity "by hand".
The tactic `fun_prop` breaks down a function into simpler pieces and uses lemmas tagged
with the `fun_prop` attribute to prove that it is continuous.
(There is also an older tactic, `continuity`: its own documentation describes `fun_prop` as
"a (usually more powerful) alternative".)
-/

example {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x ^ 2 + 3 * g x - f x * g x) := by
  fun_prop
  done

end generic

/-!
Back in the lecture on limits, we used the "ε-δ" approach.
For metric spaces, such as `ℝ`, `Mathlib` connects the two approaches.
-/

#check Metric.continuous_iff

--  Hint: `Real.dist_eq` and `abs_mul` may be useful.
--  Of course, `fun_prop` proves this immediately, but the point is to see `ε`s and `δ`s!
example : Continuous (fun x : ℝ => 2 * x) := by
  sorry
  done

/-!
##  Many topologies on the same Type

So far, we always worked with a Type `X` equipped with an instance `[TopologicalSpace X]`.
Mathematically, the same set can carry many different topologies, and it is often useful to
compare them.

`Mathlib` can do this: `TopologicalSpace X` is itself a Type, and its terms are the
topologies on `X`.
Moreover, the topologies on `X` are partially ordered and form a complete lattice.

**Pathology alert!**
For two topologies `t₁ t₂ : TopologicalSpace X`, `t₁ ≤ t₂` means that every `t₂`-open set is
also `t₁`-open, that is, `t₁` is *finer* than `t₂`.
So, "smaller" means "more open sets".
In particular,
* `⊥` (the smallest topology) is the *discrete* topology: every subset is open;
* `⊤` (the largest topology) is the *indiscrete* topology: only `∅` and `Set.univ` are open.

If you think of a topology as its collection of open sets, ordered by inclusion,
then this is the *opposite* order!
One consequence of `Mathlib`'s convention is that the identity function `(X, t₁) → (X, t₂)` is
continuous if and only if `t₁ ≤ t₂`.
-/

--  `open Topology` gives access to the notation `IsOpen[t]` that we discuss below.
open Topology

#check TopologicalSpace.le_def
#check continuous_id_iff_le
#check TopologicalSpace.isOpen_top_iff
#check DiscreteTopology

/-!
How do we talk about open sets with respect to a topology that is *not* the one found by
typeclass inference?
After `open Topology`, `Mathlib` provides notation that lets you specify the topology
(you can see it in the output of the `#check`s above):
* `IsOpen[t] s`          -- `s` is open with respect to the topology `t`;
* `IsClosed[t] s`        -- `s` is closed with respect to the topology `t`;
* `closure[t] s`         -- the closure of `s` with respect to the topology `t`;
* `Continuous[t₁, t₂] f` -- `f` is continuous with respect to `t₁` on the domain
  and `t₂` on the codomain.

These are simply notation for `@IsOpen X t s`, `@IsClosed X t s`,...:
the `@` makes all the arguments explicit, so that we can pass the topology `t` ourselves.

When printing, Lean only shows a topology if typeclass inference would *not* find it anyway:
otherwise, it omits it (or prints `_`).
For instance, in the output of `#check TopologicalSpace.le_def` above,
`IsOpen` stands for `IsOpen[s]` and, in `continuous_id_iff_le`,
`Continuous[t, _]` stands for `Continuous[t, t']`.
-/

section many_topologies

variable {X : Type*}

example (s : Set X) : IsOpen[⊤] s ↔ s = ∅ ∨ s = Set.univ := by
  sorry
  done

/-!
Let's prove that the empty set is open in the indiscrete topology.
Surely, `exact isOpen_empty` will work...
-/

/--
error: failed to synthesize instance of type class
  TopologicalSpace X

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : IsOpen[⊤] (∅ : Set X) := by
  exact isOpen_empty
  done

/-!
What went wrong?
The topology is an *instance-implicit* argument of `isOpen_empty` (the `[TopologicalSpace X]`
in its signature).
Lean does not read off instance-implicit arguments from the goal:
it tries to find them using typeclass inference.
Since there is no instance of `TopologicalSpace X`, this fails.

Even `exact?` gets confused: it finds the right lemma, but then cannot use it!
-/

/--
error: found a proof, but the corresponding tactic failed:
  (expose_names; exact isOpen_empty)

It may be possible to correct this proof by adding type annotations, explicitly specifying implicit arguments, or eliminating unnecessary function abstractions.
-/
#guard_msgs in
example : IsOpen[⊤] (∅ : Set X) := by
  exact?

/-!
There are two ways out.
* Pass all the arguments explicitly using `@`.
* Temporarily make `⊤` an instance, using `let`: typeclass inference will then find it.
-/

example : IsOpen[⊤] (∅ : Set X) := by
  exact @isOpen_empty X ⊤
  done

example : IsOpen[⊤] (∅ : Set X) := by
  let _ : TopologicalSpace X := ⊤
  exact isOpen_empty
  done

--  Hint: `isOpen_discrete` and `discreteTopology_bot`.
example (s : Set X) : IsOpen[⊥] s := by
  sorry
  done

end many_topologies

/-!
##  Defining a new topology

The natural numbers already come with a topology: the discrete one.
-/

#synth TopologicalSpace ℕ
#synth DiscreteTopology ℕ

example : IsOpen ({3} : Set ℕ) := by
  exact isOpen_discrete {3}
  done

/-!
Let's define a different topology on `ℕ`: the *upper set topology*.
A set `s` of natural numbers is open if it is *upward closed*:
whenever `a ∈ s` and `a ≤ b`, then also `b ∈ s`.

Since `ℕ` already has a `TopologicalSpace` instance, we do *not* want to make our topology
an `instance`: as we saw in the lecture on typeclasses, having two instances of the same class
on the same Type leads to confusing errors.
Instead, we make it a `def`.

Lean asks us to tag a `def` whose Type is a `class` with `@[instance_reducible]`.
This affects how Lean unfolds `upperTop` during typeclass inference and
`Mathlib` does the same with its own definitions of topologies.
For us, it is enough to know that adding it makes Lean happy.

Note how, inside `where`, we can refer to the `protected` field as simply `IsOpen`.
-/

/-- The *upper set topology* on `ℕ`:
a set `s` is open if, whenever `a ∈ s` and `a ≤ b`, also `b ∈ s`. -/
--  As with `divisibilityGraph`, if instead of `where` you type `:=[new_line]_`,
--  the lightbulb can `Generate a skeleton for the structure under construction`.
@[instance_reducible]
def upperTop : TopologicalSpace ℕ where
  IsOpen s := ∀ a b, a ≤ b → a ∈ s → b ∈ s
  isOpen_univ := by
    sorry
    done
  isOpen_inter s t hs ht := by
    sorry
    done
  isOpen_sUnion S hS := by
    sorry
    done

/-!
Our first API lemma for `upperTop` says what it means to be open.
This is the only place where we "look inside" the definition of `upperTop`:
from now on, we will use `isOpen_upperTop_iff` instead.
-/
lemma isOpen_upperTop_iff {s : Set ℕ} :
    IsOpen[upperTop] s ↔ ∀ a b, a ≤ b → a ∈ s → b ∈ s := by
  exact Iff.rfl
  done

/-!
###  Exercises
-/

--  Hint: `Set.mem_Ici`.
example : IsOpen[upperTop] (Set.Ici 3) := by
  sorry
  done

example : ¬ IsOpen[upperTop] {3} := by
  sorry
  done

/-- The only `upperTop`-open set containing `0` is the whole of `ℕ`. -/
lemma eq_univ_of_zero_mem {s : Set ℕ} (hs : IsOpen[upperTop] s) (h0 : 0 ∈ s) :
    s = Set.univ := by
  sorry
  done

--  Hint: if `upperTop = ⊥`, then `{3}` would be `upperTop`-open.
lemma upperTop_ne_bot : upperTop ≠ ⊥ := by
  sorry
  done

/-!
###  Continuity with respect to `upperTop`

Let's look at continuity, when both the domain and the codomain carry the topology `upperTop`.

*Warning.*
Many lemmas take the topologies as instance-implicit arguments `[TopologicalSpace X]`.
If we use them with `upperTop`, Lean tries to find the topology on `ℕ` using typeclass
inference.
This time, it *succeeds*: it finds the discrete topology!
Lean then complains that this is not the topology `upperTop` that appears in our assumption.
-/

/--
error: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instTopologicalSpaceNat
inferred
  upperTop
-/
#guard_msgs in
example {f : ℕ → ℕ} (hf : Continuous[upperTop, upperTop] f) {s : Set ℕ}
    (hs : IsOpen[upperTop] s) : IsOpen[upperTop] (f ⁻¹' s) := by
  exact hf.isOpen_preimage s hs
  done

/-!
For the same reason, `constructor` does not work to prove `Continuous[upperTop, upperTop] f`
(although, in that case, the error message is less informative).

The lemma `continuous_def`, instead, takes the topologies as (ordinary) implicit arguments
`{_ : TopologicalSpace X}`: Lean reads them off from the goal and everything works.
Hover over `continuous_def` below to see the difference with `Continuous.isOpen_preimage`.
-/

#check continuous_def
#check Continuous.isOpen_preimage

--  Hint: start with `rw [continuous_def]`.
lemma upperTop_continuous_of_monotone {f : ℕ → ℕ} (hf : Monotone f) :
    Continuous[upperTop, upperTop] f := by
  sorry
  done

example : Continuous[upperTop, upperTop] (fun n => n + 1) := by
  sorry
  done

--  Hint: what is the preimage of `Set.Ici 1`?
example : ¬ Continuous[upperTop, upperTop] (fun n => if n = 0 then 1 else 0) := by
  sorry
  done

--  This one is more challenging!
--  Hint: given `a ≤ b`, what is the preimage of `Set.Ici (f a)`?
lemma monotone_of_upperTop_continuous {f : ℕ → ℕ} (hf : Continuous[upperTop, upperTop] f) :
    Monotone f := by
  sorry
  done

example (f : ℕ → ℕ) : Continuous[upperTop, upperTop] f ↔ Monotone f := by
  sorry
  done

--  Hint: `continuous_id_iff_le`.
example : Continuous[⊥, upperTop] id := by
  sorry
  done

example : ¬ Continuous[upperTop, ⊥] id := by
  sorry
  done

/-!
How does `Mathlib` avoid these issues?
The upper set topology is in `Mathlib`, as `Topology.upperSet`, for any preorder.
To use it as an instance, `Mathlib` introduces a *type synonym* `WithUpperSet α`:
a copy of `α` that does not inherit the instances of `α`.
This is the same trick as `myN` in the lecture on setoids!
On `WithUpperSet α`, the upper set topology *is* the instance and all the issues above disappear.
-/

#check Topology.upperSet
#check WithUpperSet

/-!
##  Neighbourhoods

In the lecture on limits, I mentioned that `Mathlib` uses filters to talk about limits.
Most of the topology library is also built using filters.
The main filter in topology is `𝓝 x`, the *neighbourhood filter* of a point `x`
(type `𝓝` as `\nhds`; this notation is available after `open Topology`).
You can think of `𝓝 x` as the collection of all neighbourhoods of `x`.

Even if you do not want to know anything about filters, the following characterisation
is all you need to get started: `s ∈ 𝓝 x` means that `s` contains an open set containing `x`.
-/

#check mem_nhds_iff
#check IsOpen.mem_nhds
#check isOpen_iff_mem_nhds

example : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 (1 / 2) := by
  sorry
  done

/-!
##  Interior and closure

Here are the definitions:
* the interior of `s` is the union of all the open sets contained in `s`;
* the closure of `s` is the intersection of all the closed sets containing `s`.
-/

#print interior
#print closure

#check interior_subset
#check isOpen_interior
#check subset_closure
#check isClosed_closure
#check IsClosed.closure_eq

section closure

variable {X : Type*} [TopologicalSpace X]

example {s : Set X} : closure s = s ↔ IsClosed s := by
  sorry
  done

end closure

example : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc 0 1 := by
  sorry
  done

/-!
##  Properties of topological spaces

Many properties of topological spaces are `Prop`-valued `class`es in `Mathlib`.
For instance, `T2Space X` means that `X` is Hausdorff and `CompactSpace X` means that `X`
is compact.
Since they are `class`es, Lean can often find them automatically.
-/

#check T2Space
#check t2Space_iff
#check CompactSpace

#synth T2Space ℝ
#synth CompactSpace (Set.Icc (0 : ℝ) 1)  -- the subspace topology on `[0, 1]` is compact

/-!
Compactness of *subsets* is expressed by `IsCompact s`, rather than with a class.
Again, there is a filter-based definition, but you can rely on the API.
-/

#check IsCompact
#check isCompact_Icc
#check IsCompact.image
#check IsCompact.isClosed
#check IsCompact.exists_isMaxOn

--  The extreme value theorem: a continuous function on `[0, 1]` attains its maximum.
--  Hint: `Set.nonempty_Icc` and `Continuous.continuousOn`.
example (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, f y ≤ f x := by
  sorry
  done

/-!
Finally, let's go back to the upper set topology.
Since `upperTop` is not an instance, we use `@` to say that `ℕ` with the topology `upperTop`
is *not* Hausdorff.
-/

--  Hint: any open set containing `0` is the whole of `ℕ`.
example : ¬ @T2Space ℕ upperTop := by
  sorry
  done

/-!
#  Conclusion

* A topology on `X` is a term of `TopologicalSpace X`, given by a predicate `IsOpen` on `Set X`.
* `TopologicalSpace` is a `class`: most of the time, Lean finds the topology for you.
* Prefer the API (`isOpen_univ, IsOpen.inter, isOpen_sUnion, isOpen_compl_iff, continuous_def`, ...)
  to unfolding definitions, and let `fun_prop` prove continuity.
* Topologies on `X` are ordered, with `⊥` the discrete topology and `⊤` the indiscrete one:
  `t₁ ≤ t₂` means that `t₁` has *more* open sets.
* To work with a topology `t` that is not an instance, use `IsOpen[t]`, `Continuous[t₁, t₂]`,...
  and be careful with lemmas taking instance-implicit `[TopologicalSpace X]` arguments:
  use `@`, `let`, or lemmas with implicit topologies such as `continuous_def`.
  Better still, follow `Mathlib` and use a type synonym!
-/

end TPwL_topology_no_sols
