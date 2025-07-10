# agda-container-plus

**Work in progress**

[Container](https://agda.github.io/agda-stdlib/v2.2/Data.Container.html) which is also [Applicative](https://agda.github.io/agda-stdlib/v2.2/Effect.Applicative.html) or
[Monad](https://agda.github.io/agda-stdlib/v2.2/Effect.Monad.html).

Built on [agda-stdlib](https://github.com/agda/agda-stdlib).

This library contains:

- A formalization of `Functor` and `Applicative` laws
  
  - [Effect.Functor.Law](src/Effect/Functor/Law.agda)
  - [Effect.Applicative.Law](src/Effect/Applicative/Law.agda)

- More on `Container` morphisms

  - [Container.Morphism.Equality](src/Container/Morphism/Equality.agda)
  - [Container.Morphism.Iso](src/Container/Morphism/Iso.agda)

- A data type representing `Container` which is also `Applicative` [^container-monads]

  - [Container.Algebra.Action](src/Container/Algebra/Action.agda)
  - [Container.Effect.Applicative.FromAction](src/Container/Effect/Applicative/FromAction.agda)
  - [Container.Effect.Applicative.ToAction](src/Container/Effect/Applicative/ToAction.agda)

  - [Container.Algebra.Action.Inv](src/Container/Algebra/Action/Inv.agda) for invertible applicative
    i.e. the monoid of shapes of the underlying `Functor` of `Applicative` is actually a group.

- A data type representing `Container` which is also `Moand` [^container-monads]

  - [Container.Algebra.Monad](src/Container/Algebra/Monad.agda)
  - [Container.Algebra.Monad.Uustalu](src/Container/Algebra/Monad/Uustalu.agda)

  - Representation of "monomial monads" i.e. monads on functors of shape
    `S × (I → _)`.

    - [Container.Algebra.Monad.Monomial](src/Container/Algebra/Monad/Monomial.agda)
    - [Container.Algebra.Monad.StateLike](src/Container/Algebra/Monad/StateLike.agda)
    - [Container.Algebra.Monad.Monomial.FinitePosition](src/Container/Algebra/Monad/Monomial/FinitePosition.agda)

Todo:

- `Effect.Monad` laws
- Making `Effect.Monad` out of `Container.Algebra.Monad`
- Containers ∩ Comonads [^directed-containers]
- Commutative Applicative and zippy (i.e. Commutative and Idempotent) Applicative.
  - Porting [semialign](https://hackage.haskell.org/package/semialign-1.2)

[^directed-containers]: [Directed Containers as Categories](https://arxiv.org/abs/1604.01187)
[^container-monads]: [Container combinatorics: monads and lax monoidal functors.](http://cs.ioc.ee/~tarmo/papers/uustalu-ttcs17.pdf)