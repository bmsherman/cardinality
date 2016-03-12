# Type cardinalities

Reasoning about the size of finite types in Coq. Building on Ben's [Finite library](https://github.com/bmsherman/finite), we show inequality of types with different cardinalities.

Type cardinality is defined in terms of an isomorphism (`Iso.T`) between a type `A` and `Fin.t n`.

A crucial theorem with non-trivial proof is that if `Fin.t n` is ismorphic to `Fin.t m`, then `n = m`, which is proven by deriving a contradiction from an isomorphism from a smaller to a larger type. The inductive case is achieved by proving an injectivity of type successor (see `injective_plus` in [finite_iso.v](https://github.com/tchajed/cardinality/blob/master/finite_iso.v)), using the formulation of Finite.Fin of finite types (which are proven isomorphic to Fin.t).

In analogy to the proof of Cantor's diagonalization between natural numbers and sequences (the theorem `Cantor` in [Iso.v](https://github.com/bmsherman/finite/blob/master/Iso.v)), we prove there is no isomorphism between a type `A` and its (computable) subsets `A -> bool` using a similar diagonalization argument (see `powerset_bigger` in [type_neq.v](https://github.com/tchajed/cardinality/blob/master/type_neq.v)).
