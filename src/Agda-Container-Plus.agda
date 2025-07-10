import Container.Algebra.Action
import Container.Algebra.Action.Inv
import Container.Algebra.TensorMonoid
import Container.Algebra.Monad
import Container.Algebra.Monad.Uustalu
import Container.Algebra.Monad.Monomial
import Container.Algebra.Monad.StateLike
import Container.Algebra.Monad.Monomial.DecidableEquality
import Container.Algebra.Monad.Monomial.FinitePosition

import Container.Combinator.Compose
import Container.Combinator.Compose.Properties
import Container.Combinator.Tensor
import Container.Combinator.Tensor.Properties
import Container.Combinator.Monoidal

import Container.Morphism.Equality
import Container.Morphism.Iso

import Container.Effect.Functor
import Container.Effect.Applicative.FromAction
import Container.Effect.Applicative.ToAction

import Effect.Applicative.Law
import Effect.Applicative.Properties
import Effect.Functor.Law
import Effect.Functor.Day