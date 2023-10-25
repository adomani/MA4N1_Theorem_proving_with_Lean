import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.PNat.Prime

namespace TPwL

/-
#  Graphs in `Mathlib`

In maths, you may have seen the definition of a graph as a pair `(V, E)`
consisting of
* a set a `V`, whose elements are called vertices;
* a set `E ⊂ Sym^2 V` of unordered pairs of distinct vertices of `V`.

There are various "flavours" or variations, where you may allow edges between
a vertex and itself, or where you may allow multiple edges connecting the same
pair of vertices.

We will only look at the notion `SimpleGraph` from `Mathlib`, which corresponds
to what are called simple, undirected, loopless graphs: no edges between a vertex
and itself, at most one edge between any pair of vertices, edges are *un*ordered
pairs.

In `Mathlib`, all this data is encoded in the structure `SimpleGraph`, associated
with a Type `V` and containing as fields
* the relation `SimpleGraph.Adj` on `V` -- the adjacency relation, where two vertices
  are in relation if they correspond to adjacent vertices;
* a proof that the relation is symmetric -- corresponding to the fact that our graphs
  are undirected;
* a proof that the relation is irreflexive -- corresponding to the fact that our graphs
  are loopless.

In case you have seen the notion of graph elsewhere, you may want to take some time
to convince yourself that this version really is equivalent to the one with which
you may be familiar!

There is quite a bit of machinery developed to convert smoothly between edges
simply represented as terms of `V` that are in relation and actual "concrete"
unordered pairs.
The relevant Type of unordered pairs is called `Sym2` and it has a fairly extensive
API, allowing to go back and forth between vertices in relation and pairs.
Also, `SimpleGraph.edgeSet` is... the edge set of a graph!
It is a subset of `Sym2 V`.

We still did not see this, but the Type of subsets of a given Type `V` is
denoted by `Set V` is `Mathlib`.
So, writing `U : Set V` means "`U` is a subset of `V`".

The notation for an edge, viewed as an unordered pair is `⟦(a, b)⟧`.
-/

--  Hover over these notions, to see the internal documentation.
--  Go to definition if you want to see the implementation.
#check SimpleGraph
#check Sym2
#check SimpleGraph.edgeSet

/-
`Mathlib` already has the definition of some graphs:
-/
#check completeGraph
#check emptyGraph
#check completeBipartiteGraph
#check SimpleGraph.pathGraph
#check SimpleGraph.hasse  -- graph associated to an order

open SimpleGraph

--  Hint: try `simp` and see if you can understand what is going on!
lemma completeGraph_mem_edgeSet_of_ne (V : Type) {a b : V} (h : a ≠ b) :
    ⟦(a, b)⟧ ∈ edgeSet (completeGraph V) := by
  simp [h]  -- `simp` leaves `¬ a = b` as a goal
  done
/-
_Aside: `DefEq` and its abuse._
Just using `exact?` suggests `exact h`.
While of course this works, it is probably considered a "bad" proof,
or what is sometimes called "`DefEq` abuse".
`DefEq` is `Def`initional `Eq`uality and it is a very very strict form of equality.
Proving that `(a, b)` is an edge of the complete graph, since `a` is different from `b`
is exploiting the actual implementation of the graph, rather than its properties.
If someone decided to implement the notion of `completeGraph` with a
different (e.g. non-`DefEq` by still equivalent) property, *ideally* the only proofs
that should be rewritten are the ones of the "API" surrounding `completeGraph`.
From this point of view, the `simp [h]` proof should still work, while the proof
`exact h` is more brittle and likelier to no longer work.
-/

example {V : Type} {G : SimpleGraph V} {a b : V} (h : ⟦(a, b)⟧ ∈ G.edgeSet) :
    ⟦(b, a)⟧ ∈ G.edgeSet := by
  apply G.symm  -- `G.symm` is dot-notation: it stands for SimpleGraph.symm G
  exact h
  -- or, combining the two `exact G.symm h`
  done

/-!
We now define a new graph.
-/

/--
the `divisibilityGraph`: this is a graph with vertices the natural numbers
whose edges consist of pairs of distinct numbers one of which divides the other.
-/
--  Most of this is auto-generated: if instead of `where` you type `:=[new_line]_`,
--  wait for the lightbulb to appear and click on it, then you can auto-complete
--  using `Generate a skeleton for the structure under construction`.
def divisibilityGraph : SimpleGraph ℕ where
  --  if you notice, we use `Adj a b := ...` instead of `Adj := fun a b => ...`
  --  this is a convenient feature to improve readability, but both mean the same
  Adj a b := (a ≠ b) ∧ ((a ∣ b) ∨ (b ∣ a))
  --  use `dsimp at *` to get a better view of the assumptions/goal
  symm a b h := by
    dsimp at *
    cases h with
    | intro left right =>
      constructor
      · exact?
      · exact?
    done
  loopless a ha := by
    dsimp at ha
    cases ha with
    | intro left right =>
      exact?
    done

example : ¬ ⟦(3, 5)⟧ ∈ divisibilityGraph.edgeSet := by
  simp
  unfold Adj
  unfold divisibilityGraph
  simp
  done

example : ⟦(3, 6)⟧ ∈ divisibilityGraph.edgeSet := by
  simp
  unfold Adj
  unfold divisibilityGraph
  simp
  done

--  Try this for a potential challenge!
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ¬ ⟦(p, q)⟧ ∈ divisibilityGraph.edgeSet := by
  simp
  unfold Adj
  unfold divisibilityGraph
  simp
  intro pq
  rw [not_or]
  constructor <;> rw [Nat.prime_dvd_prime_iff_eq] <;> try assumption
  exact?
  --  if you want a more verbose and clearer proof, this also works
  --constructor
  --· rw [Nat.prime_dvd_prime_iff_eq] <;> assumption
  --· rw [Nat.prime_dvd_prime_iff_eq]
  --  · exact?
  --  · assumption
  --  · assumption
  done

end TPwL
