/**
 * @file The `Bounded` type class represents totally ordered types that have an upper and lower boundary.
 *
 * Instances should satisfy the following law in addition to the `Ord` laws:
 *
 * - Bounded: `bottom <= a <= top`
 */
import { Ord, ordNumber }  from  './Ord.ts'

/**
 * @since 1.0.0
 */
export interface Bounded<A> extends Ord<A> {
  readonly top: A
  readonly bottom: A
}

/**
 * @since 1.0.0
 */
export const boundedNumber: Bounded<number> = {
  ...ordNumber,
  top: Infinity,
  bottom: -Infinity
}

/**
 * @file A `BoundedJoinSemilattice` must satisfy the following laws in addition to `JoinSemilattice` laws:
 *
 * - `a ∨ 0 == a`
 */
import { JoinSemilattice }  from  './JoinSemilattice.ts'

/**
 * @since 1.4.0
 */
export interface BoundedJoinSemilattice<A> extends JoinSemilattice<A> {
  readonly zero: A
}

/**
 * @file A `BoundedLattice` must satisfy the following in addition to `BoundedMeetSemilattice` and `BoundedJoinSemilattice` laws:
 *
 * - Absorbtion law for meet: `a ∧ (a ∨ b) == a`
 * - Absorbtion law for join: `a ∨ (a ∧ b) == a`
 */
import { BoundedJoinSemilattice }  from  './BoundedJoinSemilattice.ts'
import { BoundedMeetSemilattice }  from  './BoundedMeetSemilattice.ts'

/**
 * @since 1.4.0
 */
export interface BoundedLattice<A> extends BoundedJoinSemilattice<A>, BoundedMeetSemilattice<A> {}

/**
 * @file A `BoundedMeetSemilattice` must satisfy the following laws in addition to `MeetSemilattice` laws:
 *
 * - `a ∧ 1 = a`
 */
import { MeetSemilattice }  from  './MeetSemilattice.ts'

/**
 * @since 1.4.0
 */
export interface BoundedMeetSemilattice<A> extends MeetSemilattice<A> {
  readonly one: A
}

import { IO }  from  './IO.ts'

/**
 * Returns the current `Date`
 *
 * @since 1.10.0
 */
export const create: IO<Date> = new IO(() => new Date())

/**
 * Returns the number of milliseconds elapsed since January 1, 1970, 00:00:00 UTC
 *
 * @since 1.10.0
 */
export const now: IO<number> = new IO(() => new Date().getTime())

/**
 * @file A `Group` is a `Monoid` with inverses. Instances must satisfy the following law in addition to the monoid laws:
 *
 * - Inverse: `concat(inverse(a), a) = empty = concat(a, inverse(a))`
 */
import { Monoid }  from  './Monoid.ts'

/**
 * @since 1.13.0
 */
export interface Group<A> extends Monoid<A> {
  readonly inverse: (a: A) => A
}

/**
 * @file A join-semilattice (or upper semilattice) is a semilattice whose operation is called `join`, and which can be thought
 * of as a least upper bound.
 *
 * A `JoinSemilattice` must satisfy the following laws:
 *
 * - Associativity: `a ∨ (b ∨ c) = (a ∨ b) ∨ c`
 * - Commutativity: `a ∨ b = b ∨ a`
 * - Idempotency:   `a ∨ a = a`
 *
 */

/**
 * @since 1.4.0
 */
export interface JoinSemilattice<A> {
  readonly join: (x: A, y: A) => A
}

/**
 * @file A `Lattice` must satisfy the following in addition to `JoinSemilattice` and `MeetSemilattice` laws:
 *
 * - Absorbtion law for meet: `a ∧ (a ∨ b) == a`
 * - Absorbtion law for join: `a ∨ (a ∧ b) == a`
 */
import { JoinSemilattice }  from  './JoinSemilattice.ts'
import { MeetSemilattice }  from  './MeetSemilattice.ts'

/**
 * @since 1.4.0
 */
export interface Lattice<A> extends JoinSemilattice<A>, MeetSemilattice<A> {}

/**
 * A `Magma` is a pair `(A, concat)` in which `A` is a non-empty set and `concat` is a binary operation on `A`
 * @since 1.16.0
 */
export interface Magma<A> {
  readonly concat: (x: A, y: A) => A
}

/**
 * @file A meet-semilattice (or lower semilattice) is a semilattice whose operation is called `meet`, and which can be thought
 * of as a greatest lower bound.
 *
 * A `MeetSemilattice` must satisfy the following laws:
 *
 * - Associativity: `a ∧ (b ∧ c) = (a ∧ b) ∧ c`
 * - Commutativity: `a ∧ b = b ∧ a`
 * - Idempotency:   `a ∧ a = a`
 */

/**
 * @since 1.4.0
 */
export interface MeetSemilattice<A> {
  readonly meet: (x: A, y: A) => A
}

/**
 * @file The `Alt` type class identifies an associative operation on a type constructor.  It is similar to `Semigroup`, except
 * that it applies to types of kind `* -> *`, like `Array` or `Option`, rather than concrete types like `string` or
 * `number`.
 *
 * `Alt` instances are required to satisfy the following laws:
 *
 * 1. Associativity: `A.alt(A.alt(fa, ga), ha) = A.alt(fa, A.alt(ga, ha))`
 * 2. Distributivity: `A.map(A.alt(fa, ga), ab) = A.alt(A.map(fa, ab), A.map(ga, ab))`
 */
import { Functor, Functor1, Functor2, Functor2C, Functor3, Functor3C }  from  './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface Alt<F> extends Functor<F> {
  readonly alt: <A>(fx: HKT<F, A>, fy: HKT<F, A>) => HKT<F, A>
}

export interface Alt1<F extends URIS> extends Functor1<F> {
  readonly alt: <A>(fx: Type<F, A>, fy: Type<F, A>) => Type<F, A>
}

export interface Alt2<F extends URIS2> extends Functor2<F> {
  readonly alt: <L, A>(fx: Type2<F, L, A>, fy: Type2<F, L, A>) => Type2<F, L, A>
}

export interface Alt3<F extends URIS3> extends Functor3<F> {
  readonly alt: <U, L, A>(fx: Type3<F, U, L, A>, fy: Type3<F, U, L, A>) => Type3<F, U, L, A>
}

export interface Alt2C<F extends URIS2, L> extends Functor2C<F, L> {
  readonly alt: <A>(fx: Type2<F, L, A>, fy: Type2<F, L, A>) => Type2<F, L, A>
}

export interface Alt3C<F extends URIS3, U, L> extends Functor3C<F, U, L> {
  readonly alt: <A>(fx: Type3<F, U, L, A>, fy: Type3<F, U, L, A>) => Type3<F, U, L, A>
}

/**
 * @file The `Alternative` type class has no members of its own; it just specifies that the type constructor has both
 * `Applicative` and `Plus` instances.
 *
 * Types which have `Alternative` instances should also satisfy the following laws:
 *
 * 1. Distributivity: `A.ap(A.alt(fab, gab), fa) = A.alt(A.ap(fab, fa), A.ap(gab, fa))`
 * 2. Annihilation: `A.ap(zero, fa) = zero`
 */
import { Applicative, Applicative1, Applicative2, Applicative2C, Applicative3, Applicative3C }  from  './Applicative.ts'
import { URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Plus, Plus1, Plus2, Plus2C, Plus3, Plus3C }  from  './Plus.ts'

/**
 * @since 1.0.0
 */
export interface Alternative<F> extends Applicative<F>, Plus<F> {}

export interface Alternative1<F extends URIS> extends Applicative1<F>, Plus1<F> {}

export interface Alternative2<F extends URIS2> extends Applicative2<F>, Plus2<F> {}

export interface Alternative3<F extends URIS3> extends Applicative3<F>, Plus3<F> {}

export interface Alternative2C<F extends URIS2, L> extends Applicative2C<F, L>, Plus2C<F, L> {}

export interface Alternative3C<F extends URIS3, U, L> extends Applicative3C<F, U, L>, Plus3C<F, U, L> {}

import { HKT2, Type2, Type3, URIS2, URIS3 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface Bifunctor<F> {
  readonly URI: F
  readonly bimap: <L, A, M, B>(fla: HKT2<F, L, A>, f: (l: L) => M, g: (a: A) => B) => HKT2<F, M, B>
}

export interface Bifunctor2<F extends URIS2> {
  readonly URI: F
  readonly bimap: <L, A, M, B>(fla: Type2<F, L, A>, f: (l: L) => M, g: (a: A) => B) => Type2<F, M, B>
}

export interface Bifunctor2C<F extends URIS2, L> {
  readonly URI: F
  readonly _L: L
  readonly bimap: <A, M, B>(fla: Type2<F, L, A>, f: (l: L) => M, g: (a: A) => B) => Type2<F, M, B>
}

export interface Bifunctor3<F extends URIS3> {
  readonly URI: F
  readonly bimap: <U, L, A, M, B>(fla: Type3<F, U, L, A>, f: (l: L) => M, g: (a: A) => B) => Type3<F, U, M, B>
}

export interface Bifunctor3C<F extends URIS3, U> {
  readonly URI: F
  readonly _U: U
  readonly bimap: <L, A, M, B>(fla: Type3<F, U, L, A>, f: (l: L) => M, g: (a: A) => B) => Type3<F, U, M, B>
}

/**
 * @file A `BoundedDistributiveLattice` is a lattice that is both bounded and distributive
 */
import { BoundedLattice }  from  './BoundedLattice.ts'
import { DistributiveLattice, getMinMaxDistributiveLattice }  from  './DistributiveLattice.ts'
import { Ord }  from  './Ord.ts'

/**
 * @since 1.4.0
 */
export interface BoundedDistributiveLattice<A> extends BoundedLattice<A>, DistributiveLattice<A> {}

/**
 * @since 1.4.0
 */
export const getMinMaxBoundedDistributiveLattice = <A>(O: Ord<A>) => (
  min: A,
  max: A
): BoundedDistributiveLattice<A> => {
  return {
    ...getMinMaxDistributiveLattice(O),
    zero: min,
    one: max
  }
}

import { HKT2, Type2, Type3, URIS2, URIS3, URIS4, Type4 }  from  './HKT.ts'
import { Semigroupoid, Semigroupoid2, Semigroupoid3, Semigroupoid3C, Semigroupoid4 }  from  './Semigroupoid.ts'

/**
 * @since 1.0.0
 */
export interface Category<F> extends Semigroupoid<F> {
  readonly id: <A>() => HKT2<F, A, A>
}

export interface Category2<F extends URIS2> extends Semigroupoid2<F> {
  readonly id: <A>() => Type2<F, A, A>
}

export interface Category3<F extends URIS3> extends Semigroupoid3<F> {
  readonly id: <U, A>() => Type3<F, U, A, A>
}

export interface Category4<F extends URIS4> extends Semigroupoid4<F> {
  readonly id: <X, U, A>() => Type4<F, X, U, A, A>
}

export interface Category3C<F extends URIS3, U> extends Semigroupoid3C<F, U> {
  readonly id: <A>() => Type3<F, U, A, A>
}

import { Chain, Chain1, Chain2, Chain2C, Chain3, Chain3C }  from  './Chain.ts'
import { Either }  from  './Either.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface ChainRec<F> extends Chain<F> {
  readonly chainRec: <A, B>(a: A, f: (a: A) => HKT<F, Either<A, B>>) => HKT<F, B>
}

export interface ChainRec1<F extends URIS> extends Chain1<F> {
  readonly chainRec: <A, B>(a: A, f: (a: A) => Type<F, Either<A, B>>) => Type<F, B>
}

export interface ChainRec2<F extends URIS2> extends Chain2<F> {
  readonly chainRec: <L, A, B>(a: A, f: (a: A) => Type2<F, L, Either<A, B>>) => Type2<F, L, B>
}

export interface ChainRec3<F extends URIS3> extends Chain3<F> {
  readonly chainRec: <U, L, A, B>(a: A, f: (a: A) => Type3<F, U, L, Either<A, B>>) => Type3<F, U, L, B>
}

export interface ChainRec2C<F extends URIS2, L> extends Chain2C<F, L> {
  readonly chainRec: <A, B>(a: A, f: (a: A) => Type2<F, L, Either<A, B>>) => Type2<F, L, B>
}

export interface ChainRec3C<F extends URIS3, U, L> extends Chain3C<F, U, L> {
  readonly chainRec: <A, B>(a: A, f: (a: A) => Type3<F, U, L, Either<A, B>>) => Type3<F, U, L, B>
}

/**
 * @since 1.0.0
 */
export const tailRec = <A, B>(f: (a: A) => Either<A, B>, a: A): B => {
  let v = f(a)
  while (v.isLeft()) {
    v = f(v.value)
  }
  return v.value
}

import { Extend, Extend1, Extend2, Extend2C, Extend3, Extend3C }  from  './Extend.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface Comonad<F> extends Extend<F> {
  readonly extract: <A>(ca: HKT<F, A>) => A
}

export interface Comonad1<F extends URIS> extends Extend1<F> {
  readonly extract: <A>(ca: Type<F, A>) => A
}

export interface Comonad2<F extends URIS2> extends Extend2<F> {
  readonly extract: <L, A>(ca: Type2<F, L, A>) => A
}

export interface Comonad3<F extends URIS3> extends Extend3<F> {
  readonly extract: <U, L, A>(ca: Type3<F, U, L, A>) => A
}

export interface Comonad2C<F extends URIS2, L> extends Extend2C<F, L> {
  readonly extract: <A>(ca: Type2<F, L, A>) => A
}

export interface Comonad3C<F extends URIS3, U, L> extends Extend3C<F, U, L> {
  readonly extract: <A>(ca: Type3<F, U, L, A>) => A
}

/**
 * @file Adapted from https://github.com/purescript/purescript-console
 */
import { IO }  from  './IO.ts'

/**
 * @since 1.0.0
 */
export const log = (s: unknown): IO<void> => {
  return new IO(() => console.log(s)) // tslint:disable-line:no-console
}

/**
 * @since 1.0.0
 */
export const warn = (s: unknown): IO<void> => {
  return new IO(() => console.warn(s)) // tslint:disable-line:no-console
}

/**
 * @since 1.0.0
 */
export const error = (s: unknown): IO<void> => {
  return new IO(() => console.error(s)) // tslint:disable-line:no-console
}

/**
 * @since 1.0.0
 */
export const info = (s: unknown): IO<void> => {
  return new IO(() => console.info(s)) // tslint:disable-line:no-console
}

/**
 * @file A `DistributiveLattice` must satisfy the following laws in addition to `Lattice` laws:
 *
 * - Distributivity for meet: `a ∨ (b ∧ c) = (a ∨ b) ∧ (a ∨ c)`
 * - Distributivity for join: `a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)`
 */
import { Lattice }  from  './Lattice.ts'
import { Ord, max, min }  from  './Ord.ts'

/**
 * @since 1.4.0
 */
export interface DistributiveLattice<A> extends Lattice<A> {}

/**
 * @since 1.4.0
 */
export const getMinMaxDistributiveLattice = <A>(O: Ord<A>): DistributiveLattice<A> => {
  return {
    meet: min(O),
    join: max(O)
  }
}

/**
 * @file Adapted from https://github.com/purescript/purescript-prelude/blob/master/src/Data/Field.purs
 */
import { Ring }  from  './Ring.ts'
import { Setoid }  from  './Setoid.ts'

/**
 * @since 1.0.0
 */
export interface Field<A> extends Ring<A> {
  readonly degree: (a: A) => number
  readonly div: (x: A, y: A) => A
  readonly mod: (x: A, y: A) => A
}

/**
 * @since 1.0.0
 */
export const fieldNumber: Field<number> = {
  add: (x, y) => x + y,
  zero: 0,
  mul: (x, y) => x * y,
  one: 1,
  sub: (x, y) => x - y,
  degree: _ => 1,
  div: (x, y) => x / y,
  mod: (x, y) => x % y
}

/**
 * The *greatest common divisor* of two values
 *
 * @since 1.0.0
 */
export const gcd = <A>(S: Setoid<A>, field: Field<A>): ((x: A, y: A) => A) => {
  const zero = field.zero
  const f = (x: A, y: A): A => (S.equals(y, zero) ? x : f(y, field.mod(x, y)))
  return f
}

/**
 * The *least common multiple* of two values
 *
 * @since 1.0.0
 */
export const lcm = <A>(S: Setoid<A>, F: Field<A>): ((x: A, y: A) => A) => {
  const zero = F.zero
  const gcdSF = gcd(S, F)
  return (x, y) => (S.equals(x, zero) || S.equals(y, zero) ? zero : F.div(F.mul(x, y), gcdSF(x, y)))
}

/**
 * @file Heyting algebras are bounded (distributive) lattices that are also equipped with an additional binary operation
 * `implies` (also written as `→`). Heyting algebras also define a complement operation `not` (sometimes written as
 * `¬a`)
 *
 * However, in Heyting algebras this operation is only a pseudo-complement, since Heyting algebras do not necessarily
 * provide the law of the excluded middle. This means that there is no guarantee that `a ∨ ¬a = 1`.
 *
 * Heyting algebras model intuitionistic logic. For a model of classical logic, see the boolean algebra type class
 * implemented as `BooleanAlgebra`.
 *
 * A `HeytingAlgebra` must satisfy the following laws in addition to `BoundedDistributiveLattice` laws:
 *
 * - Implication:
 *   - `a → a = 1`
 *   - `a ∧ (a → b) = a ∧ b`
 *   - `b ∧ (a → b) = b`
 *   - `a → (b ∧ c) = (a → b) ∧ (a → c)`
 * - Complemented
 *   - `¬a = a → 0`
 */
import { BoundedDistributiveLattice }  from  './BoundedDistributiveLattice.ts'

/**
 * @since 1.4.0
 */
export interface HeytingAlgebra<A> extends BoundedDistributiveLattice<A> {
  readonly implies: (x: A, y: A) => A
  readonly not: (x: A) => A
}

import { HKT, HKT2, HKT3, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface Invariant<F> {
  readonly URI: F
  readonly imap: <A, B>(fa: HKT<F, A>, f: (a: A) => B, g: (b: B) => A) => HKT<F, B>
}

export interface Invariant1<F extends URIS> {
  readonly URI: F
  readonly imap: <A, B>(fa: HKT<F, A>, f: (a: A) => B, g: (b: B) => A) => Type<F, B>
}

export interface Invariant2<F extends URIS2> {
  readonly URI: F
  readonly imap: <L, A, B>(fa: HKT2<F, L, A>, f: (a: A) => B, g: (b: B) => A) => Type2<F, L, B>
}

export interface Invariant3<F extends URIS3> {
  readonly URI: F
  readonly imap: <U, L, A, B>(fa: HKT3<F, U, L, A>, f: (a: A) => B, g: (b: B) => A) => Type3<F, U, L, B>
}

export interface Invariant2C<F extends URIS2, L> {
  readonly URI: F
  readonly _L: L
  readonly imap: <A, B>(fa: HKT2<F, L, A>, f: (a: A) => B, g: (b: B) => A) => Type2<F, L, B>
}

export interface Invariant3C<F extends URIS3, U, L> {
  readonly URI: F
  readonly _L: L
  readonly _U: U
  readonly imap: <A, B>(fa: HKT3<F, U, L, A>, f: (a: A) => B, g: (b: B) => A) => Type3<F, U, L, B>
}

/**
 * @file Mutable references in the `IO` monad
 */
import { IO }  from  './IO.ts'

/**
 * @example
 * import { newIORef }  from  'fp-ts/lib/IORef.ts'
 *
 * assert.strictEqual(
 *   newIORef(1)
 *     .chain(ref => ref.write(2).chain(() => ref.read))
 *     .run(),
 *   2
 * )
 * @since 1.8.0
 */
export class IORef<A> {
  read: IO<A>
  constructor(private value: A) {
    this.read = new IO(() => this.value)
  }
  /**
   * @since 1.8.0
   */
  write(a: A): IO<void> {
    return new IO(() => {
      this.value = a
    })
  }
  /**
   * @since 1.8.0
   */
  modify(f: (a: A) => A): IO<void> {
    return new IO(() => {
      this.value = f(this.value)
    })
  }
}

/**
 * @since 1.8.0
 */
export const newIORef = <A>(a: A): IO<IORef<A>> => {
  return new IO(() => new IORef(a))
}

/**
 * @file The `Monad` type class combines the operations of the `Chain` and
 * `Applicative` type classes. Therefore, `Monad` instances represent type
 * constructors which support sequential composition, and also lifting of
 * functions of arbitrary arity.
 *
 * Instances must satisfy the following laws in addition to the `Applicative` and `Chain` laws:
 *
 * 1. Left identity: `M.chain(M.of(a), f) = f(a)`
 * 2. Right identity: `M.chain(fa, M.of) = fa`
 *
 * Note. `Functor`'s `map` can be derived: `A.map = (fa, f) => A.chain(fa, a => A.of(f(a)))`
 */
import { Applicative, Applicative1, Applicative2, Applicative2C, Applicative3, Applicative3C }  from  './Applicative.ts'
import { Chain, Chain1, Chain2, Chain2C, Chain3, Chain3C }  from  './Chain.ts'
import { URIS, URIS2, URIS3 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface Monad<F> extends Applicative<F>, Chain<F> {}

export interface Monad1<F extends URIS> extends Applicative1<F>, Chain1<F> {}

export interface Monad2<M extends URIS2> extends Applicative2<M>, Chain2<M> {}

export interface Monad3<M extends URIS3> extends Applicative3<M>, Chain3<M> {}

export interface Monad2C<M extends URIS2, L> extends Applicative2C<M, L>, Chain2C<M, L> {}

export interface Monad3C<M extends URIS3, U, L> extends Applicative3C<M, U, L>, Chain3C<M, U, L> {}

/**
 * @file Lift a computation from the `IO` monad
 */
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { IO }  from  './IO.ts'
import { Monad, Monad1, Monad2, Monad3, Monad2C, Monad3C }  from  './Monad.ts'

/**
 * @since 1.10.0
 */
export interface MonadIO<M> extends Monad<M> {
  readonly fromIO: <A>(fa: IO<A>) => HKT<M, A>
}

export interface MonadIO1<M extends URIS> extends Monad1<M> {
  readonly fromIO: <A>(fa: IO<A>) => Type<M, A>
}

export interface MonadIO2<M extends URIS2> extends Monad2<M> {
  readonly fromIO: <L, A>(fa: IO<A>) => Type2<M, L, A>
}

export interface MonadIO3<M extends URIS3> extends Monad3<M> {
  readonly fromIO: <U, L, A>(fa: IO<A>) => Type3<M, U, L, A>
}

export interface MonadIO2C<M extends URIS2, L> extends Monad2C<M, L> {
  readonly fromIO: <A>(fa: IO<A>) => Type2<M, L, A>
}

export interface MonadIO3C<M extends URIS3, U, L> extends Monad3C<M, U, L> {
  readonly fromIO: <A>(fa: IO<A>) => Type3<M, U, L, A>
}

/**
 * @file Lift a computation from the `Task` monad
 */
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Task }  from  './Task.ts'
import { Monad, Monad1, Monad2, Monad3, Monad2C, Monad3C }  from  './Monad.ts'

/**
 * @since 1.10.0
 */
export interface MonadTask<M> extends Monad<M> {
  readonly fromTask: <A>(fa: Task<A>) => HKT<M, A>
}

export interface MonadTask1<M extends URIS> extends Monad1<M> {
  readonly fromTask: <A>(fa: Task<A>) => Type<M, A>
}

export interface MonadTask2<M extends URIS2> extends Monad2<M> {
  readonly fromTask: <L, A>(fa: Task<A>) => Type2<M, L, A>
}

export interface MonadTask3<M extends URIS3> extends Monad3<M> {
  readonly fromTask: <U, L, A>(fa: Task<A>) => Type3<M, U, L, A>
}

export interface MonadTask2C<M extends URIS2, L> extends Monad2C<M, L> {
  readonly fromTask: <A>(fa: Task<A>) => Type2<M, L, A>
}

export interface MonadTask3C<M extends URIS3, U, L> extends Monad3C<M, U, L> {
  readonly fromTask: <A>(fa: Task<A>) => Type3<M, U, L, A>
}

import { Semigroup }  from  './Semigroup.ts'
import { Setoid }  from  './Setoid.ts'

export type Ordering = -1 | 0 | 1

/**
 * @since 1.0.0
 */
export const sign = (n: number): Ordering => {
  return n <= -1 ? -1 : n >= 1 ? 1 : 0
}

/**
 * @since 1.0.0
 */
export const setoidOrdering: Setoid<Ordering> = {
  equals: (x, y) => x === y
}

/**
 * @since 1.0.0
 */
export const semigroupOrdering: Semigroup<Ordering> = {
  concat: (x, y) => (x !== 0 ? x : y)
}

/**
 * @since 1.0.0
 */
export const invert = (O: Ordering): Ordering => {
  switch (O) {
    case -1:
      return 1
    case 1:
      return -1
    default:
      return 0
  }
}

/**
 * @file The `Plus` type class extends the `alt` type class with a value that should be the left and right identity for `alt`.
 *
 * It is similar to `Monoid`, except that it applies to types of kind `* -> *`, like `Array` or `Option`, rather than
 * concrete types like `string` or `number`.
 *
 * `Plus` instances should satisfy the following laws:
 *
 * 1. Left identity: `A.alt(zero, fa) == fa`
 * 2. Right identity: `A.alt(fa, zero) == fa`
 * 3. Annihilation: `A.map(zero, fa) == zero`
 */
import { Alt, Alt1, Alt2, Alt2C, Alt3, Alt3C }  from  './Alt.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface Plus<F> extends Alt<F> {
  readonly zero: <A>() => HKT<F, A>
}

export interface Plus1<F extends URIS> extends Alt1<F> {
  readonly zero: <A>() => Type<F, A>
}

export interface Plus2<F extends URIS2> extends Alt2<F> {
  readonly zero: <L, A>() => Type2<F, L, A>
}

export interface Plus3<F extends URIS3> extends Alt3<F> {
  readonly zero: <U, L, A>() => Type3<F, U, L, A>
}

export interface Plus2C<F extends URIS2, L> extends Alt2C<F, L> {
  readonly zero: <A>() => Type2<F, L, A>
}

export interface Plus3C<F extends URIS3, U, L> extends Alt3C<F, U, L> {
  readonly zero: <A>() => Type3<F, U, L, A>
}

/**
 * @file Adapted from https://github.com/purescript/purescript-random
 */
import { IO }  from  './IO.ts'

/**
 * Returns a random number between 0 (inclusive) and 1 (exclusive). This is a direct wrapper around JavaScript's
 * `Math.random()`.
 *
 * @since 1.0.0
 */
export const random: IO<number> = new IO(() => Math.random())

/**
 * Takes a range specified by `low` (the first argument) and `high` (the second), and returns a random integer uniformly
 * distributed in the closed interval `[low, high]`. It is unspecified what happens if `low > high`, or if either of
 * `low` or `high` is not an integer.
 *
 * @since 1.0.0
 */
export const randomInt = (low: number, high: number): IO<number> => {
  return random.map(n => Math.floor((high - low + 1) * n + low))
}

/**
 * Returns a random number between a minimum value (inclusive) and a maximum value (exclusive). It is unspecified what
 * happens if `maximum < minimum`.
 *
 * @since 1.0.0
 */
export const randomRange = (min: number, max: number): IO<number> => {
  return random.map(n => (max - min) * n + min)
}

/**
 * Returns a random boolean value with an equal chance of being `true` or `false`
 *
 * @since 1.0.0
 */
export const randomBool: IO<boolean> = random.map(n => n < 0.5)

import { HKT2, Type2, Type3, Type4, URIS2, URIS3, URIS4 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface Semigroupoid<F> {
  readonly URI: F
  readonly compose: <L, A, B>(ab: HKT2<F, A, B>, la: HKT2<F, L, A>) => HKT2<F, L, B>
}

export interface Semigroupoid2<F extends URIS2> {
  readonly URI: F
  readonly compose: <L, A, B>(ab: Type2<F, A, B>, la: Type2<F, L, A>) => Type2<F, L, B>
}

export interface Semigroupoid3<F extends URIS3> {
  readonly URI: F
  readonly compose: <U, L, A, B>(ab: Type3<F, U, A, B>, la: Type3<F, U, L, A>) => Type3<F, U, L, B>
}

export interface Semigroupoid4<F extends URIS4> {
  readonly URI: F
  readonly compose: <X, U, L, A, B>(ab: Type4<F, X, U, A, B>, la: Type4<F, X, U, L, A>) => Type4<F, X, U, L, B>
}

export interface Semigroupoid3C<F extends URIS3, U> {
  readonly URI: F
  readonly _U: U
  readonly compose: <L, A, B>(ab: Type3<F, U, A, B>, la: Type3<F, U, L, A>) => Type3<F, U, L, B>
}

/**
 * @file The `Semiring` class is for types that support an addition and multiplication operation.
 *
 * Instances must satisfy the following laws:
 *
 * - Commutative monoid under addition:
 *   - Associativity: `(a + b) + c = a + (b + c)`
 *   - Identity: `zero + a = a + zero = a`
 *   - Commutative: `a + b = b + a`
 * - Monoid under multiplication:
 *   - Associativity: `(a * b) * c = a * (b * c)`
 *   - Identity: `one * a = a * one = a`
 * - Multiplication distributes over addition:
 *   - Left distributivity: `a * (b + c) = (a * b) + (a * c)`
 *   - Right distributivity: `(a + b) * c = (a * c) + (b * c)`
 * - Annihilation: `zero * a = a * zero = zero`
 *
 * **Note:** The `number` type is not fully law abiding members of this class hierarchy due to the potential
 * for arithmetic overflows, and the presence of `NaN` and `Infinity` values. The behaviour is
 * unspecified in these cases.
 */

/**
 * @since 1.0.0
 */
export interface Semiring<A> {
  readonly add: (x: A, y: A) => A
  readonly zero: A
  readonly mul: (x: A, y: A) => A
  readonly one: A
}

/**
 * @since 1.0.0
 */
export const getFunctionSemiring = <A, B>(S: Semiring<B>): Semiring<(a: A) => B> => {
  return {
    add: (f, g) => x => S.add(f(x), g(x)),
    zero: () => S.zero,
    mul: (f, g) => x => S.mul(f(x), g(x)),
    one: () => S.one
  }
}

/**
 * The `Show` type class represents those types which can be converted into
 * a human-readable `string` representation.
 *
 * While not required, it is recommended that for any expression `x`, the
 * string `show x` be executable TypeScript code which evaluates to the same
 * value as the expression `x`.
 */
export interface Show<A> {
  show: (a: A) => string
}

/**
 * @since 1.17.0
 */
export const showString: Show<string> = {
  show: a => JSON.stringify(a)
}

/**
 * @since 1.17.0
 */
export const showNumber: Show<number> = {
  show: a => JSON.stringify(a)
}

/**
 * @since 1.17.0
 */
export const showBoolean: Show<boolean> = {
  show: a => JSON.stringify(a)
}

/**
 * @since 1.17.0
 */
export const getStructShow = <O extends { [key: string]: any }>(shows: { [K in keyof O]: Show<O[K]> }): Show<O> => {
  return {
    show: s =>
      `{ ${Object.keys(shows)
        .map(k => `${k}: ${shows[k].show(s[k])}`)
        .join(', ')} }`
  }
}

/**
 * @since 1.17.0
 */
export const getTupleShow = <T extends Array<Show<any>>>(
  ...shows: T
): Show<{ [K in keyof T]: T[K] extends Show<infer A> ? A : never }> => {
  return {
    show: t => `[${t.map((a, i) => shows[i].show(a)).join(', ')}]`
  }
}

/**
 * @file Boolean algebras are Heyting algebras with the additional constraint that the law of the excluded middle is true
 * (equivalently, double-negation is true).
 *
 * Instances should satisfy the following laws in addition to the `HeytingAlgebra` laws:
 *
 * - Excluded middle: `a ∨ ¬a = 1`
 *
 * Boolean algebras generalize classical logic: one is equivalent to "true" and zero is equivalent to "false".
 */
import { HeytingAlgebra }  from  './HeytingAlgebra.ts'

/**
 * @since 1.4.0
 */
export interface BooleanAlgebra<A> extends HeytingAlgebra<A> {}

/**
 * @since 1.4.0
 */
export const booleanAlgebraBoolean: BooleanAlgebra<boolean> = {
  meet: (x, y) => x && y,
  join: (x, y) => x || y,
  zero: false,
  one: true,
  implies: (x, y) => !x || y,
  not: x => !x
}

/**
 * @since 1.4.0
 */
export const booleanAlgebraVoid: BooleanAlgebra<void> = {
  meet: () => undefined,
  join: () => undefined,
  zero: undefined,
  one: undefined,
  implies: () => undefined,
  not: () => undefined
}

/**
 * @since 1.4.0
 */
export const getFunctionBooleanAlgebra = <B>(B: BooleanAlgebra<B>) => <A = never>(): BooleanAlgebra<(a: A) => B> => {
  return {
    meet: (x, y) => a => B.meet(x(a), y(a)),
    join: (x, y) => a => B.join(x(a), y(a)),
    zero: () => B.zero,
    one: () => B.one,
    implies: (x, y) => a => B.implies(x(a), y(a)),
    not: x => a => B.not(x(a))
  }
}

/**
 * Every boolean algebras has a dual algebra, which involves reversing one/zero as well as join/meet.
 *
 * @since 1.4.0
 */
export const getDualBooleanAlgebra = <A>(B: BooleanAlgebra<A>): BooleanAlgebra<A> => {
  return {
    meet: (x, y) => B.join(x, y),
    join: (x, y) => B.meet(x, y),
    zero: B.one,
    one: B.zero,
    implies: (x, y) => B.join(B.not(x), y),
    not: B.not
  }
}

/**
 * @file The `Chain` type class extends the `Apply` type class with a `chain` operation which composes computations in
 * sequence, using the return value of one computation to determine the next computation.
 *
 * Instances must satisfy the following law in addition to the `Apply` laws:
 *
 * 1. Associativity: `F.chain(F.chain(fa, afb), bfc) <-> F.chain(fa, a => F.chain(afb(a), bfc))`
 *
 * Note. `Apply`'s `ap` can be derived: `(fab, fa) => F.chain(fab, f => F.map(f, fa))`
 */
import { Apply, Apply1, Apply2, Apply2C, Apply3, Apply3C }  from  './Apply.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface Chain<F> extends Apply<F> {
  readonly chain: <A, B>(fa: HKT<F, A>, f: (a: A) => HKT<F, B>) => HKT<F, B>
}

export interface Chain1<F extends URIS> extends Apply1<F> {
  readonly chain: <A, B>(fa: Type<F, A>, f: (a: A) => Type<F, B>) => Type<F, B>
}

export interface Chain2<F extends URIS2> extends Apply2<F> {
  readonly chain: <L, A, B>(fa: Type2<F, L, A>, f: (a: A) => Type2<F, L, B>) => Type2<F, L, B>
}

export interface Chain3<F extends URIS3> extends Apply3<F> {
  readonly chain: <U, L, A, B>(fa: Type3<F, U, L, A>, f: (a: A) => Type3<F, U, L, B>) => Type3<F, U, L, B>
}

export interface Chain2C<F extends URIS2, L> extends Apply2C<F, L> {
  readonly chain: <A, B>(fa: Type2<F, L, A>, f: (a: A) => Type2<F, L, B>) => Type2<F, L, B>
}

export interface Chain3C<F extends URIS3, U, L> extends Apply3C<F, U, L> {
  readonly chain: <A, B>(fa: Type3<F, U, L, A>, f: (a: A) => Type3<F, U, L, B>) => Type3<F, U, L, B>
}

/**
 * @since 1.0.0
 */
export function flatten<F extends URIS3>(
  chain: Chain3<F>
): <U, L, A>(mma: Type3<F, U, L, Type3<F, U, L, A>>) => Type3<F, U, L, A>
export function flatten<F extends URIS3, U, L>(
  chain: Chain3C<F, U, L>
): <A>(mma: Type3<F, U, L, Type3<F, U, L, A>>) => Type3<F, U, L, A>
export function flatten<F extends URIS2>(chain: Chain2<F>): <L, A>(mma: Type2<F, L, Type2<F, L, A>>) => Type2<F, L, A>
export function flatten<F extends URIS2, L>(
  chain: Chain2C<F, L>
): <A>(mma: Type2<F, L, Type2<F, L, A>>) => Type2<F, L, A>
export function flatten<F extends URIS>(chain: Chain1<F>): <A>(mma: Type<F, Type<F, A>>) => Type<F, A>
export function flatten<F>(chain: Chain<F>): <A>(mma: HKT<F, HKT<F, A>>) => HKT<F, A>
export function flatten<F>(chain: Chain<F>): <A>(mma: HKT<F, HKT<F, A>>) => HKT<F, A> {
  return mma => chain.chain(mma, ma => ma)
}

import { Applicative2C }  from  './Applicative.ts'
import { Apply2C }  from  './Apply.ts'
import { Contravariant2 }  from  './Contravariant.ts'
import { Functor2 }  from  './Functor.ts'
import { Monoid }  from  './Monoid.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Setoid, fromEquals }  from  './Setoid.ts'
import { phantom, toString }  from  './function.ts'
import { Show }  from  './Show.ts'

declare module './HKT' {
  interface URI2HKT2<L, A> {
    Const: Const<L, A>
  }
}

export const URI = 'Const'

export type URI = typeof URI

/**
 * @data
 * @constructor Const
 * @since 1.0.0
 */
export class Const<L, A> {
  readonly _A!: A
  readonly _L!: L
  readonly _URI!: URI
  constructor(readonly value: L) {}
  map<B>(f: (a: A) => B): Const<L, B> {
    return this as any
  }
  contramap<B>(f: (b: B) => A): Const<L, B> {
    return this as any
  }
  fold<B>(f: (l: L) => B): B {
    return f(this.value)
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `new Const(${toString(this.value)})`
  }
}

/**
 * @since 1.17.0
 */
export const getShow = <L, A>(S: Show<L>): Show<Const<L, A>> => {
  return {
    show: c => `new Const(${S.show(c.value)})`
  }
}

/**
 * @since 1.0.0
 */
export const getSetoid = <L, A>(S: Setoid<L>): Setoid<Const<L, A>> => {
  return fromEquals((x, y) => S.equals(x.value, y.value))
}

const map = <L, A, B>(fa: Const<L, A>, f: (a: A) => B): Const<L, B> => {
  return fa.map(f)
}

const contramap = <L, A, B>(fa: Const<L, A>, f: (b: B) => A): Const<L, B> => {
  return fa.contramap(f)
}

const ap = <L>(S: Semigroup<L>) => <A, B>(fab: Const<L, (a: A) => B>, fa: Const<L, A>): Const<L, B> => {
  return new Const(S.concat(fab.value, fa.value))
}

/**
 * @since 1.0.0
 */
export const getApply = <L>(S: Semigroup<L>): Apply2C<URI, L> => {
  return {
    URI,
    _L: phantom,
    map,
    ap: ap(S)
  }
}

const of = <L>(M: Monoid<L>) => <A>(a: A): Const<L, A> => {
  return new Const(M.empty)
}

/**
 * @since 1.0.0
 */
export const getApplicative = <L>(M: Monoid<L>): Applicative2C<URI, L> => {
  return {
    ...getApply(M),
    of: of(M)
  }
}

/**
 * @since 1.0.0
 */
export const const_: Functor2<URI> & Contravariant2<URI> = {
  URI,
  map,
  contramap
}

import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface Contravariant<F> {
  readonly URI: F
  readonly contramap: <A, B>(fa: HKT<F, A>, f: (b: B) => A) => HKT<F, B>
}

export interface Contravariant1<F extends URIS> {
  readonly URI: F
  readonly contramap: <A, B>(fa: Type<F, A>, f: (b: B) => A) => Type<F, B>
}

export interface Contravariant2<F extends URIS2> {
  readonly URI: F
  readonly contramap: <L, A, B>(fa: Type2<F, L, A>, f: (b: B) => A) => Type2<F, L, B>
}

export interface Contravariant3<F extends URIS3> {
  readonly URI: F
  readonly contramap: <U, L, A, B>(fa: Type3<F, U, L, A>, f: (b: B) => A) => Type3<F, U, L, B>
}

export interface Contravariant2C<F extends URIS2, L> {
  readonly URI: F
  readonly _L: L
  readonly contramap: <A, B>(fa: Type2<F, L, A>, f: (b: B) => A) => Type2<F, L, B>
}

export interface Contravariant3C<F extends URIS3, U, L> {
  readonly URI: F
  readonly _L: L
  readonly _U: U
  readonly contramap: <A, B>(fa: Type3<F, U, L, A>, f: (b: B) => A) => Type3<F, U, L, B>
}

/**
 * @since 1.0.0
 */
export function lift<F extends URIS3>(
  contravariant: Contravariant3<F>
): <A, B>(f: (b: B) => A) => <U, L>(fa: Type3<F, U, L, A>) => Type3<F, U, L, B>
export function lift<F extends URIS3, U, L>(
  contravariant: Contravariant3C<F, U, L>
): <A, B>(f: (b: B) => A) => (fa: Type3<F, U, L, A>) => Type3<F, U, L, B>
export function lift<F extends URIS2>(
  contravariant: Contravariant2<F>
): <A, B>(f: (b: B) => A) => <L>(fa: Type2<F, L, A>) => Type2<F, L, B>
export function lift<F extends URIS2, L>(
  contravariant: Contravariant2C<F, L>
): <A, B>(f: (b: B) => A) => (fa: Type2<F, L, A>) => Type2<F, L, B>
export function lift<F extends URIS>(
  contravariant: Contravariant1<F>
): <A, B>(f: (b: B) => A) => (fa: Type<F, A>) => Type<F, B>
export function lift<F>(contravariant: Contravariant<F>): <A, B>(f: (b: B) => A) => (fa: HKT<F, A>) => HKT<F, B>
export function lift<F>(contravariant: Contravariant<F>): <A, B>(f: (b: B) => A) => (fa: HKT<F, A>) => HKT<F, B> {
  return f => fa => contravariant.contramap(fa, f)
}

/**
 * @file Adapted from https://github.com/purescript/purescript-exceptions
 */
import { Either, left, right }  from  './Either.ts'
import { IO, io }  from  './IO.ts'
import { Option, none, some }  from  './Option.ts'

/**
 * Create a JavaScript error, specifying a message
 *
 * @since 1.0.0
 */
export const error = (message: string): Error => {
  return new Error(message)
}

/**
 * Get the error message from a JavaScript error
 *
 * @since 1.0.0
 */
export const message = (e: Error): string => {
  return e.message
}

/**
 * Get the stack trace from a JavaScript error
 *
 * @since 1.0.0
 */
export const stack = (e: Error): Option<string> => {
  return typeof e.stack === 'string' ? some(e.stack) : none
}

/**
 * Throw an exception
 *
 * @since 1.0.0
 */
export const throwError = <A>(e: Error): IO<A> => {
  return new IO(() => {
    throw e
  })
}

/**
 * Catch an exception by providing an exception handler
 *
 * @since 1.0.0
 */
export const catchError = <A>(ma: IO<A>, handler: (e: Error) => IO<A>): IO<A> => {
  return new IO(() => {
    try {
      return ma.run()
    } catch (e) {
      if (e instanceof Error) {
        return handler(e).run()
      } else {
        return handler(new Error(e.toString())).run()
      }
    }
  })
}

/**
 * Runs an IO and returns eventual Exceptions as a `Left` value. If the computation succeeds the result gets wrapped in
 * a `Right`.
 *
 * @since 1.0.0
 */
export const tryCatch = <A>(ma: IO<A>): IO<Either<Error, A>> => {
  return catchError(ma.map<Either<Error, A>>(right), e => io.of(left<Error, A>(e)))
}

import { Functor, Functor1, Functor2, Functor2C, Functor3, Functor3C }  from  './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { identity }  from  './function.ts'

/**
 * @since 1.0.0
 */
export interface Extend<F> extends Functor<F> {
  readonly extend: <A, B>(ea: HKT<F, A>, f: (fa: HKT<F, A>) => B) => HKT<F, B>
}

export interface Extend1<F extends URIS> extends Functor1<F> {
  readonly extend: <A, B>(ea: Type<F, A>, f: (fa: Type<F, A>) => B) => Type<F, B>
}

export interface Extend2<F extends URIS2> extends Functor2<F> {
  readonly extend: <L, A, B>(ea: Type2<F, L, A>, f: (fa: Type2<F, L, A>) => B) => Type2<F, L, B>
}

export interface Extend3<F extends URIS3> extends Functor3<F> {
  readonly extend: <U, L, A, B>(ea: Type3<F, U, L, A>, f: (fa: Type3<F, U, L, A>) => B) => Type3<F, U, L, B>
}

export interface Extend2C<F extends URIS2, L> extends Functor2C<F, L> {
  readonly extend: <A, B>(ea: Type2<F, L, A>, f: (fa: Type2<F, L, A>) => B) => Type2<F, L, B>
}

export interface Extend3C<F extends URIS3, U, L> extends Functor3C<F, U, L> {
  readonly extend: <A, B>(ea: Type3<F, U, L, A>, f: (fa: Type3<F, U, L, A>) => B) => Type3<F, U, L, B>
}

/**
 * @since 1.0.0
 */
export function duplicate<F extends URIS3>(
  E: Extend3<F>
): <U, L, A>(ma: Type3<F, U, L, A>) => Type3<F, U, L, Type3<F, U, L, A>>
export function duplicate<F extends URIS3, U, L>(
  E: Extend3C<F, U, L>
): <A>(ma: Type3<F, U, L, A>) => Type3<F, U, L, Type3<F, U, L, A>>
export function duplicate<F extends URIS2>(E: Extend2<F>): <L, A>(ma: Type2<F, L, A>) => Type2<F, L, Type2<F, L, A>>
export function duplicate<F extends URIS2, L>(E: Extend2C<F, L>): <A>(ma: Type2<F, L, A>) => Type2<F, L, Type2<F, L, A>>
export function duplicate<F extends URIS>(E: Extend1<F>): <A>(ma: Type<F, A>) => Type<F, Type<F, A>>
export function duplicate<F>(E: Extend<F>): <A>(ma: HKT<F, A>) => HKT<F, HKT<F, A>>
export function duplicate<F>(E: Extend<F>): <A>(ma: HKT<F, A>) => HKT<F, HKT<F, A>> {
  return ma => E.extend(ma, identity)
}

/**
 * @file The free group generated by elements of `A`, up to equality. Note that the `Setoid` and `Monoid` instances differ
 * from the standard such instances for `Array<Either<A, A>>`; two elements of the free group are equal iff they are equal
 * after being reduced to "canonical form", i.e., cancelling adjacent inverses.
 *
 * Adapted from https://hackage.haskell.org/package/free-algebras-0.0.7.0/docs/Data-Group-Free.html
 */
import { empty as emptyArray, getMonoid as getArrayMonoid, getSetoid as getArraySetoid, array }  from  './Array.ts'
import { Either, getSetoid as getEitherSetoid, left, right }  from  './Either.ts'
import { Group }  from  './Group.ts'
import { Setoid, fromEquals }  from  './Setoid.ts'
import { Monad1 }  from  './Monad.ts'

declare module './HKT' {
  interface URI2HKT<A> {
    FreeGroup: FreeGroup<A>
  }
}

export const URI = 'FreeGroup'

export type URI = typeof URI

/**
 * @since 1.13.0
 */
export class FreeGroup<A> {
  readonly _A!: A
  readonly _URI!: URI
  constructor(readonly value: Array<Either<A, A>>) {}
  map<B>(f: (a: A) => B): FreeGroup<B> {
    return new FreeGroup(this.value.map(e => e.bimap(f, f)))
  }
  ap<B>(fab: FreeGroup<(a: A) => B>): FreeGroup<B> {
    return fab.chain(f => this.map(f)) // <- derived
  }
  ap_<B, C>(this: FreeGroup<(b: B) => C>, fb: FreeGroup<B>): FreeGroup<C> {
    return fb.ap(this)
  }
  chain<B>(f: (a: A) => FreeGroup<B>): FreeGroup<B> {
    return new FreeGroup(array.chain(this.value, e => e.bimap(f, f).value.value))
  }
}

const of = <A>(a: A): FreeGroup<A> => {
  return new FreeGroup([right(a)])
}

const map = <A, B>(fa: FreeGroup<A>, f: (a: A) => B): FreeGroup<B> => {
  return fa.map(f)
}

const ap = <A, B>(fab: FreeGroup<(a: A) => B>, fa: FreeGroup<A>): FreeGroup<B> => {
  return fa.ap(fab)
}

const chain = <A, B>(fa: FreeGroup<A>, f: (a: A) => FreeGroup<B>): FreeGroup<B> => {
  return fa.chain(f)
}

/**
 * Smart constructor which normalizes an array
 *
 * @since 1.13.0
 */
export const fromArray = <A>(S: Setoid<A>): ((as: Array<Either<A, A>>) => FreeGroup<A>) => {
  const normalizeS = normalize(S)
  return as => new FreeGroup(normalizeS(as))
}

/**
 * Reduce a term of a free group to canonical form, i.e. cancelling adjacent inverses.
 *
 * @since 1.13.0
 */
export const normalize = <A>(S: Setoid<A>) => (g: Array<Either<A, A>>): Array<Either<A, A>> => {
  return g.reduceRight((acc: Array<Either<A, A>>, s) => {
    if (acc.length > 0) {
      const head = acc[0]
      const tail = acc.slice(1)
      if (head._tag !== s._tag && S.equals(head.value, s.value)) {
        return tail
      }
    }
    acc.unshift(s)
    return acc
  }, [])
}

/**
 * @since 1.13.0
 */
export const getSetoid = <A>(S: Setoid<A>): Setoid<FreeGroup<A>> => {
  const AS = getArraySetoid(getEitherSetoid(S, S))
  const normalizeS = normalize(S)
  return fromEquals((x, y) => AS.equals(normalizeS(x.value), normalizeS(y.value)))
}

/**
 * @since 1.13.0
 */
export const empty: FreeGroup<never> = new FreeGroup(emptyArray)

/**
 * @since 1.13.0
 */
export const getGroup = <A>(S: Setoid<A>): Group<FreeGroup<A>> => {
  const M = getArrayMonoid<Either<A, A>>()
  const normalizeS = normalize(S)
  return {
    concat: (x, y) => new FreeGroup(normalizeS(M.concat(x.value, y.value))),
    empty,
    inverse: x => new FreeGroup(x.value.reverse().map(s => (s.isLeft() ? right(s.value) : left(s.value))))
  }
}

/**
 * @since 1.13.0
 */
export const freeGroup: Monad1<URI> = {
  URI,
  of,
  map,
  ap,
  chain
}

/**
 * @file Type defunctionalization (as describe in [Lightweight higher-kinded polymorphism](https://www.cl.cam.ac.uk/~jdy22/papers/lightweight-higher-kinded-polymorphism.pdf))
 */

/**
 * `* -> *` constructors
 */
export interface HKT<URI, A> {
  readonly _URI: URI
  readonly _A: A
}

/**
 * `* -> * -> *` constructors
 */
export interface HKT2<URI, L, A> extends HKT<URI, A> {
  readonly _L: L
}

/**
 * `* -> * -> * -> *` constructors
 */
export interface HKT3<URI, U, L, A> extends HKT2<URI, L, A> {
  readonly _U: U
}

/**
 * `* -> * -> * -> * -> *` constructors
 */
export interface HKT4<URI, X, U, L, A> extends HKT3<URI, U, L, A> {
  readonly _X: X
}

//
// inj: type-level dictionaries for HKTs: URI -> concrete type
//

/**
 * `* -> *` constructors
 */
export interface URI2HKT<A> {}
/**
 * `* -> * -> *` constructors
 */
export interface URI2HKT2<L, A> {}
/**
 * `* -> * -> * -> *` constructors
 */
export interface URI2HKT3<U, L, A> {}
/**
 * `* -> * -> * -> * -> *` constructors
 */
export interface URI2HKT4<X, U, L, A> {}

//
// unions of URIs
//

/**
 * `* -> *` constructors
 */
export type URIS = keyof URI2HKT<any>
/**
 * `* -> * -> *` constructors
 */
export type URIS2 = keyof URI2HKT2<any, any>
/**
 * `* -> * -> * -> *` constructors
 */
export type URIS3 = keyof URI2HKT3<any, any, any>
/**
 * `* -> * -> * -> * -> *` constructors
 */
export type URIS4 = keyof URI2HKT4<any, any, any, any>

//
// prj
//

/**
 * `* -> *` constructors
 */
export type Type<URI extends URIS, A> = URI extends URIS ? URI2HKT<A>[URI] : any
/**
 * `* -> * -> *` constructors
 */
export type Type2<URI extends URIS2, L, A> = URI extends URIS2 ? URI2HKT2<L, A>[URI] : any
/**
 * `* -> * -> * -> *` constructors
 */
export type Type3<URI extends URIS3, U, L, A> = URI extends URIS3 ? URI2HKT3<U, L, A>[URI] : any
/**
 * `* -> * -> * -> * -> *` constructors
 */
export type Type4<URI extends URIS4, X, U, L, A> = URI extends URIS4 ? URI2HKT4<X, U, L, A>[URI] : any

import { IO, io }  from  './IO.ts'
import { IxMonad3 }  from  './IxMonad.ts'
import { Monad3C }  from  './Monad.ts'
import { phantom }  from  './function.ts'

declare module './HKT' {
  interface URI2HKT3<U, L, A> {
    IxIO: IxIO<U, L, A>
  }
}

export const URI = 'IxIO'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export class IxIO<I, O, A> {
  readonly _A!: A
  readonly _L!: O
  readonly _U!: I
  readonly _URI!: URI
  constructor(readonly value: IO<A>) {}
  run(): A {
    return this.value.run()
  }
  ichain<Z, B>(f: (a: A) => IxIO<O, Z, B>): IxIO<I, Z, B> {
    return new IxIO<I, Z, B>(this.value.chain(a => f(a).value))
  }
  map<B>(f: (a: A) => B): IxIO<I, O, B> {
    return new IxIO<I, O, B>(this.value.map(f))
  }
  ap<B>(fab: IxIO<I, I, (a: A) => B>): IxIO<I, I, B> {
    return new IxIO<I, I, B>(this.value.ap(fab.value))
  }
  chain<B>(f: (a: A) => IxIO<I, I, B>): IxIO<I, I, B> {
    return new IxIO<I, I, B>(this.value.chain(a => f(a).value))
  }
}

/**
 * @since 1.0.0
 */
export const iof = <I, A>(a: A): IxIO<I, I, A> => {
  return new IxIO<I, I, A>(io.of(a))
}

const ichain = <I, O, Z, A, B>(fa: IxIO<I, O, A>, f: (a: A) => IxIO<O, Z, B>): IxIO<I, Z, B> => {
  return fa.ichain(f)
}

const map = <I, A, B>(fa: IxIO<I, I, A>, f: (a: A) => B): IxIO<I, I, B> => {
  return fa.map(f)
}

const of = iof

const ap = <I, A, B>(fab: IxIO<I, I, (a: A) => B>, fa: IxIO<I, I, A>): IxIO<I, I, B> => {
  return fa.ap(fab)
}

const chain = <I, A, B>(fa: IxIO<I, I, A>, f: (a: A) => IxIO<I, I, B>): IxIO<I, I, B> => {
  return fa.chain(f)
}

/**
 * @since 1.0.0
 */
export const getMonad = <I = never>(): Monad3C<URI, I, I> => {
  return {
    URI,
    _L: phantom,
    _U: phantom,
    map,
    of,
    ap,
    chain
  }
}

/**
 * @since 1.0.0
 */
export const ixIO: IxMonad3<URI> = {
  URI,
  iof,
  ichain
}

import { HKT3, Type3, URIS3 }  from  './HKT.ts'
import { constant }  from  './function.ts'

// Adapted from https://github.com/garyb/purescript-indexed-monad

/**
 * @typeclass
 * @since 1.0.0
 */
export interface IxMonad<F> {
  readonly URI: F
  readonly iof: <I, A>(a: A) => HKT3<F, I, I, A>
  readonly ichain: <I, O, Z, A, B>(fa: HKT3<F, I, O, A>, f: (a: A) => HKT3<F, O, Z, B>) => HKT3<F, I, Z, B>
}

export interface IxMonad3<F extends URIS3> {
  readonly URI: F
  readonly iof: <I, A>(a: A) => Type3<F, I, I, A>
  readonly ichain: <I, O, Z, A, B>(fa: Type3<F, I, O, A>, f: (a: A) => Type3<F, O, Z, B>) => Type3<F, I, Z, B>
}

/**
 * @since 1.0.0
 */
export function iapplyFirst<F extends URIS3>(
  ixmonad: IxMonad3<F>
): <I, O, A, Z, B>(fa: Type3<F, I, O, A>, fb: Type3<F, O, Z, B>) => Type3<F, I, Z, A>
export function iapplyFirst<F>(
  ixmonad: IxMonad<F>
): <I, O, A, Z, B>(fa: HKT3<F, I, O, A>, fb: HKT3<F, O, Z, B>) => HKT3<F, I, Z, A>
export function iapplyFirst<F>(
  ixmonad: IxMonad<F>
): <I, O, A, Z, B>(fa: HKT3<F, I, O, A>, fb: HKT3<F, O, Z, B>) => HKT3<F, I, Z, A> {
  return (fa, fb) => ixmonad.ichain(fa, a => ixmonad.ichain(fb, () => ixmonad.iof(a)))
}

/**
 * @since 1.0.0
 */
export function iapplySecond<F extends URIS3>(
  ixmonad: IxMonad3<F>
): <I, O, A, Z, B>(fa: Type3<F, I, O, A>, fb: Type3<F, O, Z, B>) => Type3<F, I, Z, B>
export function iapplySecond<F>(
  ixmonad: IxMonad<F>
): <I, O, A, Z, B>(fa: HKT3<F, I, O, A>, fb: HKT3<F, O, Z, B>) => HKT3<F, I, Z, B>
export function iapplySecond<F>(
  ixmonad: IxMonad<F>
): <I, O, A, Z, B>(fa: HKT3<F, I, O, A>, fb: HKT3<F, O, Z, B>) => HKT3<F, I, Z, B> {
  return (fa, fb) => ixmonad.ichain(fa, constant(fb))
}

import { HKT2, Type2, Type3, URIS2, URIS3 }  from  './HKT.ts'
import { Monad2, Monad3, Monad2C, Monad3C }  from  './Monad.ts'
import { Either }  from  './Either.ts'
import { Option }  from  './Option.ts'

/**
 * The `MonadThrow` type class represents those monads which support errors via
 * `throwError`, where `throwError(e)` halts, yielding the error `e`.
 *
 * Laws:
 *
 * - Left zero: `M.chain(M.throwError(e), f) = M.throwError(e)`
 *
 * @since 1.16.0
 */
export interface MonadThrow<M> {
  readonly URI: M
  readonly map: <L, A, B>(fa: HKT2<M, L, A>, f: (a: A) => B) => HKT2<M, L, B>
  readonly ap: <L, A, B>(fab: HKT2<M, L, (a: A) => B>, fa: HKT2<M, L, A>) => HKT2<M, L, B>
  readonly of: <L, A>(a: A) => HKT2<M, L, A>
  readonly chain: <L, A, B>(fa: HKT2<M, L, A>, f: (a: A) => HKT2<M, L, B>) => HKT2<M, L, B>
  readonly throwError: <E, A>(e: E) => HKT2<M, E, A>
  readonly fromEither: <E, A>(e: Either<E, A>) => HKT2<M, E, A>
  readonly fromOption: <E, A>(o: Option<A>, e: E) => HKT2<M, E, A>
}

export interface MonadThrow2<M extends URIS2> extends Monad2<M> {
  readonly throwError: <E, A>(e: E) => Type2<M, E, A>
  readonly fromEither: <E, A>(e: Either<E, A>) => Type2<M, E, A>
  readonly fromOption: <E, A>(o: Option<A>, e: E) => Type2<M, E, A>
}

export interface MonadThrow2C<M extends URIS2, E> extends Monad2C<M, E> {
  readonly throwError: <A>(e: E) => Type2<M, E, A>
  readonly fromEither: <A>(e: Either<E, A>) => Type2<M, E, A>
  readonly fromOption: <A>(o: Option<A>, e: E) => Type2<M, E, A>
}

export interface MonadThrow3<M extends URIS3> extends Monad3<M> {
  readonly throwError: <U, E, A>(e: E) => Type3<M, U, E, A>
  readonly fromEither: <U, E, A>(e: Either<E, A>) => Type3<M, U, E, A>
  readonly fromOption: <U, E, A>(o: Option<A>, e: E) => Type3<M, U, E, A>
}

export interface MonadThrow3C<M extends URIS3, U, E> extends Monad3C<M, U, E> {
  readonly throwError: <A>(e: E) => Type3<M, U, E, A>
  readonly fromEither: <A>(e: Either<E, A>) => Type3<M, U, E, A>
  readonly fromOption: <A>(o: Option<A>, e: E) => Type3<M, U, E, A>
}

/**
 * @file `Applicative` functors are equivalent to strong lax monoidal functors
 *
 * - https://wiki.haskell.org/Typeclassopedia#Alternative_formulation
 * - https://bartoszmilewski.com/2017/02/06/applicative-functors/
 */
import { Applicative, Applicative1, Applicative2, Applicative3 }  from  './Applicative.ts'
import { Functor, Functor1, Functor2, Functor2C, Functor3, Functor3C }  from  './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { constant }  from  './function.ts'

/**
 * @since 1.0.0
 */
export interface Monoidal<F> extends Functor<F> {
  readonly unit: () => HKT<F, void>
  readonly mult: <A, B>(fa: HKT<F, A>, fb: HKT<F, B>) => HKT<F, [A, B]>
}

export interface Monoidal1<F extends URIS> extends Functor1<F> {
  readonly unit: () => Type<F, void>
  readonly mult: <A, B>(fa: Type<F, A>, fb: Type<F, B>) => Type<F, [A, B]>
}

export interface Monoidal2<F extends URIS2> extends Functor2<F> {
  readonly unit: <L>() => Type2<F, L, void>
  readonly mult: <L, A, B>(fa: Type2<F, L, A>, fb: Type2<F, L, B>) => Type2<F, L, [A, B]>
}

export interface Monoidal3<F extends URIS3> extends Functor3<F> {
  readonly unit: <U, L>() => Type3<F, U, L, void>
  readonly mult: <U, L, A, B>(fa: Type3<F, U, L, A>, fb: Type3<F, U, L, B>) => Type3<F, U, L, [A, B]>
}

export interface Monoidal2C<F extends URIS2, L> extends Functor2C<F, L> {
  readonly unit: () => Type2<F, L, void>
  readonly mult: <A, B>(fa: Type2<F, L, A>, fb: Type2<F, L, B>) => Type2<F, L, [A, B]>
}

export interface Monoidal3C<F extends URIS3, U, L> extends Functor3C<F, U, L> {
  readonly unit: () => Type3<F, U, L, void>
  readonly mult: <A, B>(fa: Type3<F, U, L, A>, fb: Type3<F, U, L, B>) => Type3<F, U, L, [A, B]>
}

/**
 * @since 1.0.0
 */
export function fromApplicative<F extends URIS3>(F: Applicative3<F>): Monoidal3<F>
export function fromApplicative<F extends URIS2>(F: Applicative2<F>): Monoidal2<F>
export function fromApplicative<F extends URIS>(F: Applicative1<F>): Monoidal1<F>
export function fromApplicative<F>(F: Applicative<F>): Monoidal<F>
export function fromApplicative<F>(F: Applicative<F>): Monoidal<F> {
  const f = <A>(a: A) => <B>(b: B): [A, B] => [a, b]
  return {
    URI: F.URI,
    map: F.map,
    unit: () => F.of(undefined),
    mult: <A, B>(fa: HKT<F, A>, fb: HKT<F, B>) => F.ap(F.map<A, (b: B) => [A, B]>(fa, f), fb)
  }
}

/**
 * @since 1.0.0
 */
export function toApplicative<F extends URIS3>(M: Monoidal3<F>): Applicative3<F>
export function toApplicative<F extends URIS2>(M: Monoidal2<F>): Applicative2<F>
export function toApplicative<F extends URIS>(M: Monoidal1<F>): Applicative1<F>
export function toApplicative<F>(M: Monoidal<F>): Applicative<F>
export function toApplicative<F>(M: Monoidal<F>): Applicative<F> {
  return {
    URI: M.URI,
    map: M.map,
    of: a => M.map(M.unit(), constant(a)),
    ap: (fab, fa) => M.map(M.mult(fab, fa), ([f, a]) => f(a))
  }
}

import { Functor2, Functor2C, Functor3, Functor4 }  from  './Functor.ts'
import { HKT2, Type2, Type3, Type4, URIS2, URIS3, URIS4 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface Profunctor<F> {
  readonly URI: F
  readonly map: <L, A, B>(fa: HKT2<F, L, A>, f: (a: A) => B) => HKT2<F, L, B>
  readonly promap: <A, B, C, D>(fbc: HKT2<F, B, C>, f: (a: A) => B, g: (c: C) => D) => HKT2<F, A, D>
}

export interface Profunctor2<F extends URIS2> extends Functor2<F> {
  readonly promap: <A, B, C, D>(fbc: Type2<F, B, C>, f: (a: A) => B, g: (c: C) => D) => Type2<F, A, D>
}

export interface Profunctor2C<F extends URIS2, L> extends Functor2C<F, L> {
  readonly promap: <A, C, D>(flc: Type2<F, L, C>, f: (a: A) => L, g: (c: C) => D) => Type2<F, A, D>
}

export interface Profunctor3<F extends URIS3> extends Functor3<F> {
  readonly promap: <U, A, B, C, D>(fbc: Type3<F, U, B, C>, f: (a: A) => B, g: (c: C) => D) => Type3<F, U, A, D>
}

export interface Profunctor4<F extends URIS4> extends Functor4<F> {
  readonly promap: <X, U, A, B, C, D>(fbc: Type4<F, X, U, B, C>, f: (a: A) => B, g: (c: C) => D) => Type4<F, X, U, A, D>
}

/**
 * @since 1.0.0
 */
export function lmap<F extends URIS3>(
  profunctor: Profunctor3<F>
): <U, A, B, C>(fbc: Type3<F, U, B, C>, f: (a: A) => B) => Type3<F, U, A, C>
export function lmap<F extends URIS2>(
  profunctor: Profunctor2<F>
): <A, B, C>(fbc: Type2<F, B, C>, f: (a: A) => B) => Type2<F, A, C>
export function lmap<F>(profunctor: Profunctor<F>): <A, B, C>(fbc: HKT2<F, B, C>, f: (a: A) => B) => HKT2<F, A, C>
export function lmap<F>(profunctor: Profunctor<F>): <A, B, C>(fbc: HKT2<F, B, C>, f: (a: A) => B) => HKT2<F, A, C> {
  return (fbc, f) => profunctor.promap(fbc, f, c => c)
}

/**
 * @since 1.0.0
 */
export function rmap<F extends URIS3>(
  profunctor: Profunctor3<F>
): <U, B, C, D>(fbc: Type3<F, U, B, C>, g: (c: C) => D) => Type3<F, U, B, D>
export function rmap<F extends URIS2>(
  profunctor: Profunctor2<F>
): <B, C, D>(fbc: Type2<F, B, C>, g: (c: C) => D) => Type2<F, B, D>
export function rmap<F>(profunctor: Profunctor<F>): <B, C, D>(fbc: HKT2<F, B, C>, g: (c: C) => D) => HKT2<F, B, D>
export function rmap<F>(profunctor: Profunctor<F>): <B, C, D>(fbc: HKT2<F, B, C>, g: (c: C) => D) => HKT2<F, B, D> {
  return (fbc, g) => profunctor.promap(fbc, b => b, g)
}

/**
 * @file The `Ring` class is for types that support addition, multiplication, and subtraction operations.
 *
 * Instances must satisfy the following law in addition to the `Semiring` laws:
 *
 * - Additive inverse: `a - a = (zero - a) + a = zero`
 *
 * Adapted from https://github.com/purescript/purescript-prelude/blob/master/src/Data/Ring.purs
 */
import { Semiring, getFunctionSemiring }  from  './Semiring.ts'

/**
 * @since 1.0.0
 */
export interface Ring<A> extends Semiring<A> {
  readonly sub: (x: A, y: A) => A
}

/**
 * @since 1.0.0
 */
export const getFunctionRing = <A, B>(ring: Ring<B>): Ring<(a: A) => B> => {
  return {
    ...getFunctionSemiring(ring),
    sub: (f, g) => x => ring.sub(f(x), g(x))
  }
}

/**
 * `negate x` can be used as a shorthand for `zero - x`
 *
 * @since 1.0.0
 */
export const negate = <A>(ring: Ring<A>) => (a: A): A => {
  return ring.sub(ring.zero, a)
}

/**
 * Given a tuple of `Ring`s returns a `Ring` for the tuple
 *
 * @example
 * import { getTupleRing }  from  'fp-ts/lib/Ring.ts'
 * import { fieldNumber }  from  'fp-ts/lib/Field.ts'
 *
 * const R = getTupleRing(fieldNumber, fieldNumber, fieldNumber)
 * assert.deepStrictEqual(R.add([1, 2, 3], [4, 5, 6]), [5, 7, 9])
 * assert.deepStrictEqual(R.mul([1, 2, 3], [4, 5, 6]), [4, 10, 18])
 * assert.deepStrictEqual(R.one, [1, 1, 1])
 * assert.deepStrictEqual(R.sub([1, 2, 3], [4, 5, 6]), [-3, -3, -3])
 * assert.deepStrictEqual(R.zero, [0, 0, 0])
 *
 * @since 1.14.3
 */
export const getTupleRing = <T extends Array<Ring<any>>>(
  ...rings: T
): Ring<{ [K in keyof T]: T[K] extends Ring<infer A> ? A : never }> => {
  return {
    add: (x: any, y: any) => rings.map((R, i) => R.add(x[i], y[i])),
    zero: rings.map(R => R.zero),
    mul: (x: any, y: any) => rings.map((R, i) => R.mul(x[i], y[i])),
    one: rings.map(R => R.one),
    sub: (x: any, y: any) => rings.map((R, i) => R.sub(x[i], y[i]))
  } as any
}

/**
 * Use `getTupleRing` instead
 * @since 1.0.0
 * @deprecated
 */
export const getProductRing = <A, B>(RA: Ring<A>, RB: Ring<B>): Ring<[A, B]> => {
  return getTupleRing(RA, RB)
}

/**
 * @file The `Setoid` type class represents types which support decidable equality.
 *
 * Instances must satisfy the following laws:
 *
 * 1. Reflexivity: `S.equals(a, a) === true`
 * 2. Symmetry: `S.equals(a, b) === S.equals(b, a)`
 * 3. Transitivity: if `S.equals(a, b) === true` and `S.equals(b, c) === true`, then `S.equals(a, c) === true`
 *
 * See [Getting started with fp-ts: Setoid](https://dev.to/gcanti/getting-started-with-fp-ts-setoid-39f3)
 */

/**
 * @since 1.0.0
 */
export interface Setoid<A> {
  readonly equals: (x: A, y: A) => boolean
}

/**
 * @since 1.14.0
 */
export const fromEquals = <A>(equals: (x: A, y: A) => boolean): Setoid<A> => {
  return {
    equals: (x, y) => x === y || equals(x, y)
  }
}

/**
 * @since 1.0.0
 */
export const strictEqual = <A>(a: A, b: A): boolean => {
  return a === b
}

const setoidStrict = { equals: strictEqual }

/**
 * @since 1.0.0
 */
export const setoidString: Setoid<string> = setoidStrict

/**
 * @since 1.0.0
 */
export const setoidNumber: Setoid<number> = setoidStrict

/**
 * @since 1.0.0
 */
export const setoidBoolean: Setoid<boolean> = setoidStrict

/**
 * @since 1.0.0
 */
export const getArraySetoid = <A>(S: Setoid<A>): Setoid<Array<A>> => {
  return fromEquals((xs, ys) => xs.length === ys.length && xs.every((x, i) => S.equals(x, ys[i])))
}

/**
 * @since 1.14.2
 */
export const getStructSetoid = <O extends { [key: string]: any }>(
  setoids: { [K in keyof O]: Setoid<O[K]> }
): Setoid<O> => {
  return fromEquals((x, y) => {
    for (const k in setoids) {
      if (!setoids[k].equals(x[k], y[k])) {
        return false
      }
    }
    return true
  })
}

/**
 * Use `getStructSetoid` instead
 * @since 1.0.0
 * @deprecated
 */
export const getRecordSetoid = <O extends { [key: string]: any }>(
  setoids: { [K in keyof O]: Setoid<O[K]> }
): Setoid<O> => {
  return getStructSetoid(setoids)
}

/**
 * Given a tuple of `Setoid`s returns a `Setoid` for the tuple
 *
 * @example
 * import { getTupleSetoid, setoidString, setoidNumber, setoidBoolean }  from  'fp-ts/lib/Setoid.ts'
 *
 * const S = getTupleSetoid(setoidString, setoidNumber, setoidBoolean)
 * assert.strictEqual(S.equals(['a', 1, true], ['a', 1, true]), true)
 * assert.strictEqual(S.equals(['a', 1, true], ['b', 1, true]), false)
 * assert.strictEqual(S.equals(['a', 1, true], ['a', 2, true]), false)
 * assert.strictEqual(S.equals(['a', 1, true], ['a', 1, false]), false)
 *
 * @since 1.14.2
 */
export const getTupleSetoid = <T extends Array<Setoid<any>>>(
  ...setoids: T
): Setoid<{ [K in keyof T]: T[K] extends Setoid<infer A> ? A : never }> => {
  return fromEquals((x, y) => setoids.every((S, i) => S.equals(x[i], y[i])))
}

/**
 * Use `getTupleSetoid` instead
 * @since 1.0.0
 * @deprecated
 */
export const getProductSetoid = <A, B>(SA: Setoid<A>, SB: Setoid<B>): Setoid<[A, B]> => {
  return getTupleSetoid(SA, SB)
}

/**
 * Returns the `Setoid` corresponding to the partitions of `B` induced by `f`
 *
 * @since 1.2.0
 */
export const contramap = <A, B>(f: (b: B) => A, fa: Setoid<A>): Setoid<B> => {
  return fromEquals((x, y) => fa.equals(f(x), f(y)))
}

/**
 * @since 1.4.0
 */
export const setoidDate: Setoid<Date> = contramap(date => date.valueOf(), setoidNumber)

import { constant, constIdentity }  from  './function.ts'
import { Monad2 }  from  './Monad.ts'

declare module './HKT' {
  interface URI2HKT2<L, A> {
    State: State<L, A>
  }
}

export const URI = 'State'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export class State<S, A> {
  readonly _A!: A
  readonly _L!: S
  readonly _URI!: URI
  constructor(readonly run: (s: S) => [A, S]) {}
  eval(s: S): A {
    return this.run(s)[0]
  }
  exec(s: S): S {
    return this.run(s)[1]
  }
  map<B>(f: (a: A) => B): State<S, B> {
    return new State(s => {
      const [a, s1] = this.run(s)
      return [f(a), s1]
    })
  }
  ap<B>(fab: State<S, (a: A) => B>): State<S, B> {
    return fab.chain(f => this.map(f)) // <= derived
  }
  /**
   * Flipped version of `ap`
   */
  ap_<B, C>(this: State<S, (b: B) => C>, fb: State<S, B>): State<S, C> {
    return fb.ap(this)
  }
  /**
   * Combine two effectful actions, keeping only the result of the first
   * @since 1.7.0
   */
  applyFirst<B>(fb: State<S, B>): State<S, A> {
    return fb.ap(this.map(constant))
  }
  /**
   * Combine two effectful actions, keeping only the result of the second
   * @since 1.7.0
   */
  applySecond<B>(fb: State<S, B>): State<S, B> {
    return fb.ap(this.map(constIdentity as () => (b: B) => B))
  }
  chain<B>(f: (a: A) => State<S, B>): State<S, B> {
    return new State(s => {
      const [a, s1] = this.run(s)
      return f(a).run(s1)
    })
  }
}

const map = <S, A, B>(fa: State<S, A>, f: (a: A) => B): State<S, B> => {
  return fa.map(f)
}

const of = <S, A>(a: A): State<S, A> => {
  return new State(s => [a, s])
}

const ap = <S, A, B>(fab: State<S, (a: A) => B>, fa: State<S, A>): State<S, B> => {
  return fa.ap(fab)
}

const chain = <S, A, B>(fa: State<S, A>, f: (a: A) => State<S, B>): State<S, B> => {
  return fa.chain(f)
}

/**
 * Get the current state
 *
 * @since 1.0.0
 */
export const get = <S>(): State<S, S> => {
  return new State(s => [s, s])
}

/**
 * Set the state
 *
 * @since 1.0.0
 */
export const put = <S>(s: S): State<S, void> => {
  return new State(() => [undefined, s])
}

/**
 * Modify the state by applying a function to the current state
 *
 * @since 1.0.0
 */
export const modify = <S>(f: (s: S) => S): State<S, undefined> => {
  return new State(s => [undefined, f(s)])
}

/**
 * Get a value which depends on the current state
 *
 * @since 1.0.0
 */
export const gets = <S, A>(f: (s: S) => A): State<S, A> => {
  return new State(s => [f(s), s])
}

/**
 * @since 1.0.0
 */
export const state: Monad2<URI> = {
  URI,
  map,
  of,
  ap,
  chain
}

import { Comonad2 }  from  './Comonad.ts'
import { Functor, Functor2, Functor3 }  from  './Functor.ts'
import { HKT, HKT2, HKT3, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Endomorphism, toString }  from  './function.ts'

declare module './HKT' {
  interface URI2HKT2<L, A> {
    Store: Store<L, A>
  }
}

export const URI = 'Store'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export class Store<S, A> {
  readonly _A!: A
  readonly _L!: S
  readonly _URI!: URI
  constructor(readonly peek: (s: S) => A, readonly pos: S) {}
  /** Reposition the focus at the specified position */
  seek(s: S): Store<S, A> {
    return new Store(this.peek, s)
  }
  map<B>(f: (a: A) => B): Store<S, B> {
    return new Store(s => f(this.peek(s)), this.pos)
  }
  extract(): A {
    return this.peek(this.pos)
  }
  extend<B>(f: (sa: Store<S, A>) => B): Store<S, B> {
    return new Store(s => f(this.seek(s)), this.pos)
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `new Store(${toString(this.peek)}, ${toString(this.pos)})`
  }
}

const map = <S, A, B>(sa: Store<S, A>, f: (a: A) => B): Store<S, B> => {
  return sa.map(f)
}

const extract = <S, A>(sa: Store<S, A>): A => {
  return sa.extract()
}

const extend = <S, A, B>(sa: Store<S, A>, f: (sa: Store<S, A>) => B): Store<S, B> => {
  return sa.extend(f)
}

/**
 * Extract a value from a position which depends on the current position
 *
 * @since 1.0.0
 */
export const peeks = <S>(f: Endomorphism<S>) => <A>(sa: Store<S, A>) => (s: S): A => {
  return sa.peek(f(sa.pos))
}

/**
 * Reposition the focus at the specified position, which depends on the current position
 *
 * @since 1.0.0
 */
export const seeks = <S>(f: Endomorphism<S>) => <A>(sa: Store<S, A>): Store<S, A> => {
  return new Store(sa.peek, f(sa.pos))
}

/**
 * Extract a collection of values from positions which depend on the current position
 *
 * @since 1.0.0
 */
export function experiment<F extends URIS3>(
  F: Functor3<F>
): <U, L, S>(f: (s: S) => HKT3<F, U, L, S>) => <A>(sa: Store<S, A>) => Type3<F, U, L, A>
export function experiment<F extends URIS2>(
  F: Functor2<F>
): <L, S>(f: (s: S) => HKT2<F, L, S>) => <A>(sa: Store<S, A>) => Type2<F, L, A>
export function experiment<F extends URIS>(
  F: Functor<F>
): <S>(f: (s: S) => HKT<F, S>) => <A>(sa: Store<S, A>) => Type<F, A>
export function experiment<F>(F: Functor<F>): <S>(f: (s: S) => HKT<F, S>) => <A>(sa: Store<S, A>) => HKT<F, A>
export function experiment<F>(F: Functor<F>): <S>(f: (s: S) => HKT<F, S>) => <A>(sa: Store<S, A>) => HKT<F, A> {
  return f => sa => F.map(f(sa.pos), s => sa.peek(s))
}

/**
 * @since 1.0.0
 */
export const store: Comonad2<URI> = {
  URI,
  map,
  extract,
  extend
}

/**
 * @file Adapted from https://github.com/garyb/purescript-debug
 */
import { Applicative, Applicative1, Applicative2, Applicative2C, Applicative3, Applicative3C }  from  './Applicative.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monad, Monad1, Monad2, Monad2C, Monad3, Monad3C }  from  './Monad.ts'
import { Lazy }  from  './function.ts'

/**
 * Log any value to the console for debugging purposes and then return a value. This will log the value's underlying
 * representation for low-level debugging
 *
 * @since 1.0.0
 */
export const trace = <A>(message: unknown, out: Lazy<A>): A => {
  console.log(message) // tslint:disable-line:no-console
  return out()
}

/**
 * Log any value and return it
 *
 * @since 1.0.0
 */
export const spy = <A>(a: A): A => {
  return trace(a, () => a)
}

/**
 * Log a message to the console for debugging purposes and then return the unit value of the Applicative `F`
 *
 * @since 1.0.0
 */
export function traceA<F extends URIS3>(F: Applicative3<F>): <U, L>(message: unknown) => Type3<F, U, L, void>
export function traceA<F extends URIS3, U, L>(F: Applicative3C<F, U, L>): (message: unknown) => Type3<F, U, L, void>
export function traceA<F extends URIS2>(F: Applicative2<F>): <L>(message: unknown) => Type2<F, L, void>
export function traceA<F extends URIS2, L>(F: Applicative2C<F, L>): (message: unknown) => Type2<F, L, void>
export function traceA<F extends URIS>(F: Applicative1<F>): (message: unknown) => Type<F, void>
export function traceA<F>(F: Applicative<F>): (message: unknown) => HKT<F, void> {
  return x => trace(x, () => F.of(undefined))
}

/**
 * Log any value to the console and return it in `Monad` useful when one has monadic chains
 *
 * @since 1.0.0
 */
export function traceM<F extends URIS3>(F: Monad3<F>): <U, L, A>(a: A) => Type3<F, U, L, A>
export function traceM<F extends URIS3, U, L>(F: Monad3C<F, U, L>): <A>(a: A) => Type3<F, U, L, A>
export function traceM<F extends URIS2>(F: Monad2<F>): <L, A>(a: A) => Type2<F, L, A>
export function traceM<F extends URIS2, L>(F: Monad2C<F, L>): <A>(a: A) => Type2<F, L, A>
export function traceM<F extends URIS>(F: Monad1<F>): <A>(a: A) => Type<F, A>
export function traceM<F>(F: Monad<F>): <A>(a: A) => HKT<F, A> {
  return a => trace(a, () => F.of(a))
}

import { Comonad2C }  from  './Comonad.ts'
import { Monoid }  from  './Monoid.ts'
import { Functor2 }  from  './Functor.ts'
import { phantom, tuple }  from  './function.ts'

declare module './HKT' {
  interface URI2HKT2<L, A> {
    Traced: Traced<L, A>
  }
}

export const URI = 'Traced'

export type URI = typeof URI

/**
 * @since 1.16.0
 */
export class Traced<P, A> {
  readonly _A!: A
  readonly _L!: P
  readonly _URI!: URI
  constructor(readonly run: (p: P) => A) {}
  map<B>(f: (a: A) => B): Traced<P, B> {
    return new Traced((p: P) => f(this.run(p)))
  }
}

/**
 * Extracts a value at a relative position which depends on the current value.
 * @since 1.16.0
 */
export const tracks = <P, A>(M: Monoid<P>, f: (a: A) => P) => (wa: Traced<P, A>): A => {
  return wa.run(f(wa.run(M.empty)))
}

/**
 * Get the current position
 * @since 1.16.0
 */
export const listen = <P, A>(wa: Traced<P, A>): Traced<P, [A, P]> => {
  return new Traced(e => tuple(wa.run(e), e))
}

/**
 * Get a value which depends on the current position
 * @since 1.16.0
 */
export const listens = <P, A, B>(wa: Traced<P, A>, f: (p: P) => B): Traced<P, [A, B]> => {
  return new Traced(e => tuple(wa.run(e), f(e)))
}

/**
 * Apply a function to the current position
 * @since 1.16.0
 */
export const censor = <P, A>(wa: Traced<P, A>, f: (p: P) => P): Traced<P, A> => {
  return new Traced(e => wa.run(f(e)))
}

/**
 * @since 1.16.0
 */
export function getComonad<P>(monoid: Monoid<P>): Comonad2C<URI, P> {
  function extend<A, B>(wa: Traced<P, A>, f: (wa: Traced<P, A>) => B): Traced<P, B> {
    return new Traced((p1: P) => f(new Traced((p2: P) => wa.run(monoid.concat(p1, p2)))))
  }

  function extract<A>(wa: Traced<P, A>): A {
    return wa.run(monoid.empty)
  }

  return {
    URI,
    _L: phantom,
    map,
    extend,
    extract
  }
}

function map<P, A, B>(wa: Traced<P, A>, f: (a: A) => B): Traced<P, B> {
  return wa.map(f)
}

/**
 * @since 1.16.0
 */
export const traced: Functor2<URI> = {
  URI,
  map
}

import { Functor2 }  from  './Functor.ts'
import { Monad2C }  from  './Monad.ts'
import { Monoid }  from  './Monoid.ts'
import { Semigroup }  from  './Semigroup.ts'
import { phantom }  from  './function.ts'

declare module './HKT' {
  interface URI2HKT2<L, A> {
    Writer: Writer<L, A>
  }
}

export const URI = 'Writer'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export class Writer<W, A> {
  readonly _A!: A
  readonly _L!: W
  readonly _URI!: URI
  constructor(readonly run: () => [A, W]) {}
  eval(): A {
    return this.run()[0]
  }
  exec(): W {
    return this.run()[1]
  }
  map<B>(f: (a: A) => B): Writer<W, B> {
    return new Writer(() => {
      const [a, w] = this.run()
      return [f(a), w]
    })
  }
}

const map = <W, A, B>(fa: Writer<W, A>, f: (a: A) => B): Writer<W, B> => {
  return fa.map(f)
}

const of = <W>(M: Monoid<W>) => <A>(a: A): Writer<W, A> => {
  return new Writer(() => [a, M.empty])
}

const ap = <W>(S: Semigroup<W>) => <A, B>(fab: Writer<W, (a: A) => B>, fa: Writer<W, A>): Writer<W, B> => {
  return new Writer(() => {
    const [f, w1] = fab.run()
    const [a, w2] = fa.run()
    return [f(a), S.concat(w1, w2)]
  })
}

const chain = <W>(S: Semigroup<W>) => <A, B>(fa: Writer<W, A>, f: (a: A) => Writer<W, B>): Writer<W, B> => {
  return new Writer(() => {
    const [a, w1] = fa.run()
    const [b, w2] = f(a).run()
    return [b, S.concat(w1, w2)]
  })
}

/**
 * Appends a value to the accumulator
 *
 * @since 1.0.0
 */
export const tell = <W>(w: W): Writer<W, void> => {
  return new Writer(() => [undefined, w])
}

/**
 * Modifies the result to include the changes to the accumulator
 *
 * @since 1.3.0
 */
export const listen = <W, A>(fa: Writer<W, A>): Writer<W, [A, W]> => {
  return new Writer(() => {
    const [a, w] = fa.run()
    return [[a, w], w]
  })
}

/**
 * Applies the returned function to the accumulator
 *
 * @since 1.3.0
 */
export const pass = <W, A>(fa: Writer<W, [A, (w: W) => W]>): Writer<W, A> => {
  return new Writer(() => {
    const [[a, f], w] = fa.run()
    return [a, f(w)]
  })
}

/**
 * Projects a value from modifications made to the accumulator during an action
 *
 * @since 1.3.0
 */
export const listens = <W, A, B>(fa: Writer<W, A>, f: (w: W) => B): Writer<W, [A, B]> => {
  return new Writer(() => {
    const [a, w] = fa.run()
    return [[a, f(w)], w]
  })
}

/**
 * Modify the final accumulator value by applying a function
 *
 * @since 1.3.0
 */
export const censor = <W, A>(fa: Writer<W, A>, f: (w: W) => W): Writer<W, A> => {
  return new Writer(() => {
    const [a, w] = fa.run()
    return [a, f(w)]
  })
}

/**
 *
 * @since 1.0.0
 */
export const getMonad = <W>(M: Monoid<W>): Monad2C<URI, W> => {
  return {
    URI,
    _L: phantom,
    map,
    of: of(M),
    ap: ap(M),
    chain: chain(M)
  }
}

/**
 * @since 1.0.0
 */
export const writer: Functor2<URI> = {
  URI,
  map
}

/**
 * @file The `Choice` class extends `Profunctor` with combinators for working with
 * sum types.
 *
 * `left` and `right` lift values in a `Profunctor` to act on the `Left` and
 * `Right` components of a sum, respectively.
 *
 * Looking at `Choice` through the intuition of inputs and outputs
 * yields the following type signature:
 *
 * ```purescript
 * left ::  forall input output a. p input output -> p (Either input a) (Either output a)
 * right :: forall input output a. p input output -> p (Either a input) (Either a output)
 * ```
 *
 * If we specialize the profunctor `p` to the `function` arrow, we get the following type
 * signatures:
 *
 * ```purescript
 * left ::  forall input output a. (input -> output) -> (Either input a) -> (Either output a)
 * right :: forall input output a. (input -> output) -> (Either a input) -> (Either a output)
 * ```
 *
 * When the `profunctor` is `Function` application, `left` allows you to map a function over the
 * left side of an `Either`, and `right` maps it over the right side (same as `map` would do).
 *
 * Adapted from https://github.com/purescript/purescript-profunctor/blob/master/src/Data/Profunctor/Choice.purs
 */
import { Either }  from  './Either.ts'
import { HKT2, Type2, Type3, URIS2, URIS3, URIS4, Type4 }  from  './HKT.ts'
import { Profunctor, Profunctor2, Profunctor3, Profunctor4 }  from  './Profunctor.ts'
import { Category, Category2, Category3 }  from  './Category.ts'
import { identity }  from  './function.ts'

/**
 * @since 1.11.0
 */
export interface Choice<F> extends Profunctor<F> {
  readonly left: <A, B, C>(pab: HKT2<F, A, B>) => HKT2<F, Either<A, C>, Either<B, C>>
  readonly right: <A, B, C>(pbc: HKT2<F, B, C>) => HKT2<F, Either<A, B>, Either<A, C>>
}

export interface Choice2<F extends URIS2> extends Profunctor2<F> {
  readonly left: <A, B, C>(pab: Type2<F, A, B>) => Type2<F, Either<A, C>, Either<B, C>>
  readonly right: <A, B, C>(pbc: Type2<F, B, C>) => Type2<F, Either<A, B>, Either<A, C>>
}

export interface Choice3<F extends URIS3> extends Profunctor3<F> {
  readonly left: <U, A, B, C>(pab: Type3<F, U, A, B>) => Type3<F, U, Either<A, C>, Either<B, C>>
  readonly right: <U, A, B, C>(pbc: Type3<F, U, B, C>) => Type3<F, U, Either<A, B>, Either<A, C>>
}

export interface Choice4<F extends URIS4> extends Profunctor4<F> {
  readonly left: <X, U, A, B, C>(pab: Type4<F, X, U, A, B>) => Type4<F, X, U, Either<A, C>, Either<B, C>>
  readonly right: <X, U, A, B, C>(pbc: Type4<F, X, U, B, C>) => Type4<F, X, U, Either<A, B>, Either<A, C>>
}

/**
 * Compose a value acting on a sum from two values, each acting on one of
 * the components of the sum.
 *
 * Specializing `(+++)` to function application would look like this:
 *
 * ```purescript
 * (+++) :: forall a b c d. (a -> b) -> (c -> d) -> (Either a c) -> (Either b d)
 * ```
 *
 * We take two functions, `f` and `g`, and we transform them into a single function which
 * takes an `Either`and maps `f` over the left side and `g` over the right side.  Just like
 * `bi-map` would do for the `bi-functor` instance of `Either`.
 *
 * @since 1.11.0
 */
export function splitChoice<F extends URIS3>(
  F: Category3<F> & Choice3<F>
): <U, A, B, C, D>(pab: Type3<F, U, A, B>, pcd: Type3<F, U, C, D>) => Type3<F, U, Either<A, C>, Either<B, D>>
export function splitChoice<F extends URIS2>(
  F: Category2<F> & Choice2<F>
): <A, B, C, D>(pab: Type2<F, A, B>, pcd: Type2<F, C, D>) => Type2<F, Either<A, C>, Either<B, D>>
export function splitChoice<F>(
  F: Category<F> & Choice<F>
): <A, B, C, D>(pab: HKT2<F, A, B>, pcd: HKT2<F, C, D>) => HKT2<F, Either<A, C>, Either<B, D>>
export function splitChoice<F>(
  F: Category<F> & Choice<F>
): <A, B, C, D>(pab: HKT2<F, A, B>, pcd: HKT2<F, C, D>) => HKT2<F, Either<A, C>, Either<B, D>> {
  return (pab, pcd) =>
    F.compose(
      F.left(pab),
      F.right(pcd)
    )
}

/**
 * Compose a value which eliminates a sum from two values, each eliminating
 * one side of the sum.
 *
 * This combinator is useful when assembling values from smaller components,
 * because it provides a way to support two different types of input.
 *
 * Specializing `(|||)` to function application would look like this:
 *
 * ```purescript
 * (|||) :: forall a b c d. (a -> c) -> (b -> c) -> Either a b -> c
 * ```
 *
 * We take two functions, `f` and `g`, which both return the same type `c` and we transform them into a
 * single function which takes an `Either` value with the parameter type of `f` on the left side and
 * the parameter type of `g` on the right side. The function then runs either `f` or `g`, depending on
 * whether the `Either` value is a `Left` or a `Right`.
 * This allows us to bundle two different computations which both have the same result type into one
 * function which will run the approriate computation based on the parameter supplied in the `Either` value.
 *
 * @since 1.11.0
 */
export function fanin<F extends URIS3>(
  F: Category3<F> & Choice3<F>
): <U, A, B, C>(pac: Type3<F, U, A, C>, pbc: Type3<F, U, B, C>) => Type3<F, U, Either<A, B>, C>
export function fanin<F extends URIS2>(
  F: Category2<F> & Choice2<F>
): <A, B, C>(pac: Type2<F, A, C>, pbc: Type2<F, B, C>) => Type2<F, Either<A, B>, C>
export function fanin<F>(
  F: Category<F> & Choice<F>
): <A, B, C>(pac: HKT2<F, A, C>, pbc: HKT2<F, B, C>) => HKT2<F, Either<A, B>, C>
export function fanin<F>(
  F: Category<F> & Choice<F>
): <A, B, C>(pac: HKT2<F, A, C>, pbc: HKT2<F, B, C>) => HKT2<F, Either<A, B>, C> {
  const splitChoiceF = splitChoice(F)
  return <A, B, C>(pac: HKT2<F, A, C>, pbc: HKT2<F, B, C>): HKT2<F, Either<A, B>, C> => {
    const join: HKT2<F, Either<C, C>, C> = F.promap(F.id<C>(), e => e.fold(identity, identity), identity)
    return F.compose(
      join,
      splitChoiceF(pac, pbc)
    )
  }
}

import {
  Applicative,
  Applicative1,
  Applicative2,
  ApplicativeComposition,
  ApplicativeComposition12,
  ApplicativeComposition22,
  getApplicativeComposition
} from './Applicative'
import { Either, URI, either, left as eitherLeft, right as eitherRight }  from  './Either.ts'
import { Functor, Functor1, Functor2 }  from  './Functor.ts'
import { HKT, Type, Type2, URIS, URIS2 }  from  './HKT.ts'
import { Monad, Monad1, Monad2 }  from  './Monad.ts'

export interface EitherT2v<F> extends ApplicativeComposition<F, URI> {
  readonly chain: <L, A, B>(fa: HKT<F, Either<L, A>>, f: (a: A) => HKT<F, Either<L, B>>) => HKT<F, Either<L, B>>
}

export interface EitherT2v1<F extends URIS> extends ApplicativeComposition12<F, URI> {
  readonly chain: <L, A, B>(fa: Type<F, Either<L, A>>, f: (a: A) => Type<F, Either<L, B>>) => Type<F, Either<L, B>>
}

export interface EitherT2v2<F extends URIS2> extends ApplicativeComposition22<F, URI> {
  readonly chain: <L, M, A, B>(
    fa: Type2<F, M, Either<L, A>>,
    f: (a: A) => Type2<F, M, Either<L, B>>
  ) => Type2<F, M, Either<L, B>>
}

/**
 * @since 1.0.0
 */
export function fold<F extends URIS2>(
  F: Functor2<F>
): <R, L, M, A>(left: (l: L) => R, right: (a: A) => R, fa: Type2<F, M, Either<L, A>>) => Type2<F, M, R>
export function fold<F extends URIS>(
  F: Functor1<F>
): <R, L, A>(left: (l: L) => R, right: (a: A) => R, fa: Type<F, Either<L, A>>) => Type<F, R>
export function fold<F>(
  F: Functor<F>
): <R, L, A>(left: (l: L) => R, right: (a: A) => R, fa: HKT<F, Either<L, A>>) => HKT<F, R>
export function fold<F>(
  F: Functor<F>
): <R, L, A>(left: (l: L) => R, right: (a: A) => R, fa: HKT<F, Either<L, A>>) => HKT<F, R> {
  return (left, right, fa) => F.map(fa, e => (e.isLeft() ? left(e.value) : right(e.value)))
}

/**
 * @since 1.14.0
 */
export function getEitherT2v<M extends URIS2>(M: Monad2<M>): EitherT2v2<M>
export function getEitherT2v<M extends URIS>(M: Monad1<M>): EitherT2v1<M>
export function getEitherT2v<M>(M: Monad<M>): EitherT2v<M>
export function getEitherT2v<M>(M: Monad<M>): EitherT2v<M> {
  const applicativeComposition = getApplicativeComposition(M, either)

  return {
    ...applicativeComposition,
    chain: (fa, f) => M.chain(fa, e => (e.isLeft() ? M.of(eitherLeft(e.value)) : f(e.value)))
  }
}

/** @deprecated */
export interface EitherT<F> extends ApplicativeComposition<F, URI> {
  readonly chain: <L, A, B>(f: (a: A) => HKT<F, Either<L, B>>, fa: HKT<F, Either<L, A>>) => HKT<F, Either<L, B>>
}

/** @deprecated */
export interface EitherT1<F extends URIS> extends ApplicativeComposition12<F, URI> {
  readonly chain: <L, A, B>(f: (a: A) => Type<F, Either<L, B>>, fa: Type<F, Either<L, A>>) => Type<F, Either<L, B>>
}

/** @deprecated */
export interface EitherT2<F extends URIS2> extends ApplicativeComposition22<F, URI> {
  readonly chain: <L, M, A, B>(
    f: (a: A) => Type2<F, M, Either<L, B>>,
    fa: Type2<F, M, Either<L, A>>
  ) => Type2<F, M, Either<L, B>>
}

/**
 * Use `getEitherT2v` instead
 * @since 1.0.0
 * @deprecated
 */
// tslint:disable-next-line: deprecation
export function chain<F extends URIS2>(F: Monad2<F>): EitherT2<F>['chain']
/** @deprecated */
// tslint:disable-next-line: deprecation
export function chain<F extends URIS>(F: Monad1<F>): EitherT1<F>['chain']
/** @deprecated */
// tslint:disable-next-line: deprecation
export function chain<F>(F: Monad<F>): EitherT<F>['chain']
/** @deprecated */
// tslint:disable-next-line: deprecation
export function chain<F>(F: Monad<F>): EitherT<F>['chain'] {
  return (f, fa) => F.chain(fa, e => (e.isLeft() ? F.of(eitherLeft(e.value)) : f(e.value)))
}

/**
 * Use `getEitherT2v` instead
 * @since 1.0.0
 * @deprecated
 */
// tslint:disable-next-line: deprecation
export function getEitherT<M extends URIS2>(M: Monad2<M>): EitherT2<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getEitherT<M extends URIS>(M: Monad1<M>): EitherT1<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getEitherT<M>(M: Monad<M>): EitherT<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getEitherT<M>(M: Monad<M>): EitherT<M> {
  const applicativeComposition = getApplicativeComposition(M, either)

  return {
    ...applicativeComposition,
    // tslint:disable-next-line: deprecation
    chain: chain(M)
  }
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function right<F extends URIS2>(F: Functor2<F>): <L, M, A>(fa: Type2<F, M, A>) => Type2<F, M, Either<L, A>>
/** @deprecated */
export function right<F extends URIS>(F: Functor1<F>): <L, A>(fa: Type<F, A>) => Type<F, Either<L, A>>
/** @deprecated */
export function right<F>(F: Functor<F>): <L, A>(fa: HKT<F, A>) => HKT<F, Either<L, A>>
/** @deprecated */
export function right<F>(F: Functor<F>): <L, A>(fa: HKT<F, A>) => HKT<F, Either<L, A>> {
  return <L, A>(fa: HKT<F, A>) => F.map<A, Either<L, A>>(fa, eitherRight)
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function left<F extends URIS2>(F: Functor2<F>): <L, M, A>(fl: Type2<F, M, L>) => Type2<F, M, Either<L, A>>
/** @deprecated */
export function left<F extends URIS>(F: Functor1<F>): <L, A>(fl: Type<F, L>) => Type<F, Either<L, A>>
/** @deprecated */
export function left<F>(F: Functor<F>): <L, A>(fl: HKT<F, L>) => HKT<F, Either<L, A>>
/** @deprecated */
export function left<F>(F: Functor<F>): <L, A>(fl: HKT<F, L>) => HKT<F, Either<L, A>> {
  return <L, A>(fl: HKT<F, L>) => F.map<L, Either<L, A>>(fl, eitherLeft)
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function fromEither<F extends URIS2>(
  F: Applicative2<F>
): <L, M, A>(fa: Either<L, A>) => Type2<F, M, Either<L, A>>
/** @deprecated */
export function fromEither<F extends URIS>(F: Applicative1<F>): <L, A>(fa: Either<L, A>) => Type<F, Either<L, A>>
/** @deprecated */
export function fromEither<F>(F: Applicative<F>): <L, A>(fa: Either<L, A>) => HKT<F, Either<L, A>>
/** @deprecated */
export function fromEither<F>(F: Applicative<F>): <L, A>(fa: Either<L, A>) => HKT<F, Either<L, A>> {
  return F.of
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function mapLeft<F extends URIS2>(
  F: Functor2<F>
): <N, L, M>(f: (l: L) => N) => <A>(fa: Type2<F, M, Either<L, A>>) => Type2<F, M, Either<N, A>>
/** @deprecated */
export function mapLeft<F extends URIS>(
  F: Functor1<F>
): <N, L>(f: (l: L) => N) => <A>(fa: Type<F, Either<L, A>>) => Type<F, Either<N, A>>
/** @deprecated */
export function mapLeft<F>(
  F: Functor<F>
): <N, L>(f: (l: L) => N) => <A>(fa: HKT<F, Either<L, A>>) => HKT<F, Either<N, A>>
/** @deprecated */
export function mapLeft<F>(
  F: Functor<F>
): <N, L>(f: (l: L) => N) => <A>(fa: HKT<F, Either<L, A>>) => HKT<F, Either<N, A>> {
  return f => fa => F.map(fa, e => e.mapLeft(f))
}

/**
 * @since 1.2.0
 * @deprecated
 */
export function bimap<F extends URIS2>(
  F: Functor2<F>
): <M, L, V, A, B>(fa: Type2<F, M, Either<L, A>>, f: (l: L) => V, g: (a: A) => B) => Type2<F, M, Either<V, B>>
/** @deprecated */
export function bimap<F extends URIS>(
  F: Functor1<F>
): <L, V, A, B>(fa: Type<F, Either<L, A>>, f: (l: L) => V, g: (a: A) => B) => Type<F, Either<V, B>>
/** @deprecated */
export function bimap<F>(
  F: Functor<F>
): <L, V, A, B>(fa: HKT<F, Either<L, A>>, f: (l: L) => V, g: (a: A) => B) => HKT<F, Either<V, B>>
/** @deprecated */
export function bimap<F>(
  F: Functor<F>
): <L, V, A, B>(fa: HKT<F, Either<L, A>>, f: (l: L) => V, g: (a: A) => B) => HKT<F, Either<V, B>> {
  return (fa, f, g) => F.map(fa, e => e.bimap(f, g))
}

import { Separated }  from  './Compactable.ts'
import { Either }  from  './Either.ts'
import { Filterable, Filterable1, Filterable2, Filterable2C, Filterable3, Filterable3C }  from  './Filterable.ts'
import {
  FunctorWithIndex,
  FunctorWithIndex1,
  FunctorWithIndex2,
  FunctorWithIndex2C,
  FunctorWithIndex3,
  FunctorWithIndex3C
} from './FunctorWithIndex'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Option }  from  './Option.ts'

type RefinementWithIndex<I, A, B extends A> = (i: I, a: A) => a is B
type PredicateWithIndex<I, A> = (i: I, a: A) => boolean

interface FilterWithIndex<F, I> {
  <A, B extends A>(fa: HKT<F, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): HKT<F, B>
  <A>(fa: HKT<F, A>, predicateWithIndex: PredicateWithIndex<I, A>): HKT<F, A>
}

interface PartitionWithIndex<F, I> {
  <A, B extends A>(fa: HKT<F, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): Separated<HKT<F, A>, HKT<F, B>>
  <A>(fa: HKT<F, A>, predicateWithIndex: PredicateWithIndex<I, A>): Separated<HKT<F, A>, HKT<F, A>>
}

/**
 * @since 1.12.0
 */
export interface FilterableWithIndex<F, I> extends FunctorWithIndex<F, I>, Filterable<F> {
  readonly partitionMapWithIndex: <RL, RR, A>(
    fa: HKT<F, A>,
    f: (i: I, a: A) => Either<RL, RR>
  ) => Separated<HKT<F, RL>, HKT<F, RR>>
  readonly partitionWithIndex: PartitionWithIndex<F, I>
  readonly filterMapWithIndex: <A, B>(fa: HKT<F, A>, f: (i: I, a: A) => Option<B>) => HKT<F, B>
  readonly filterWithIndex: FilterWithIndex<F, I>
}

interface FilterWithIndex1<F extends URIS, I> {
  <A, B extends A>(fa: Type<F, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): Type<F, B>
  <A>(fa: Type<F, A>, predicateWithIndex: PredicateWithIndex<I, A>): Type<F, A>
}

interface PartitionWithIndex1<F extends URIS, I> {
  <A, B extends A>(fa: Type<F, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): Separated<Type<F, A>, Type<F, B>>
  <A>(fa: Type<F, A>, predicateWithIndex: PredicateWithIndex<I, A>): Separated<Type<F, A>, Type<F, A>>
}

export interface FilterableWithIndex1<F extends URIS, I> extends FunctorWithIndex1<F, I>, Filterable1<F> {
  readonly partitionMapWithIndex: <RL, RR, A>(
    fa: Type<F, A>,
    f: (i: I, a: A) => Either<RL, RR>
  ) => Separated<Type<F, RL>, Type<F, RR>>
  readonly partitionWithIndex: PartitionWithIndex1<F, I>
  readonly filterMapWithIndex: <A, B>(fa: Type<F, A>, f: (i: I, a: A) => Option<B>) => Type<F, B>
  readonly filterWithIndex: FilterWithIndex1<F, I>
}

interface FilterWithIndex2<F extends URIS2, I> {
  <L, A, B extends A>(fa: Type2<F, L, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): Type2<F, L, B>
  <L, A>(fa: Type2<F, L, A>, predicateWithIndex: PredicateWithIndex<I, A>): Type2<F, L, A>
}

interface PartitionWithIndex2<F extends URIS2, I> {
  <L, A, B extends A>(fa: Type2<F, L, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): Separated<
    Type2<F, L, A>,
    Type2<F, L, B>
  >
  <L, A>(fa: Type2<F, L, A>, predicateWithIndex: PredicateWithIndex<I, A>): Separated<Type2<F, L, A>, Type2<F, L, A>>
}

export interface FilterableWithIndex2<F extends URIS2, I> extends FunctorWithIndex2<F, I>, Filterable2<F> {
  readonly partitionMapWithIndex: <RL, RR, L, A>(
    fa: Type2<F, L, A>,
    f: (i: I, a: A) => Either<RL, RR>
  ) => Separated<Type2<F, L, RL>, Type2<F, L, RR>>
  readonly partitionWithIndex: PartitionWithIndex2<F, I>
  readonly filterMapWithIndex: <L, A, B>(fa: Type2<F, L, A>, f: (i: I, a: A) => Option<B>) => Type2<F, L, B>
  readonly filterWithIndex: FilterWithIndex2<F, I>
}

interface FilterWithIndex2C<F extends URIS2, I, L> {
  <A, B extends A>(fa: Type2<F, L, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): Type2<F, L, B>
  <A>(fa: Type2<F, L, A>, predicateWithIndex: PredicateWithIndex<I, A>): Type2<F, L, A>
}

interface PartitionWithIndex2C<F extends URIS2, I, L> {
  <A, B extends A>(fa: Type2<F, L, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): Separated<
    Type2<F, L, A>,
    Type2<F, L, B>
  >
  <A>(fa: Type2<F, L, A>, predicateWithIndex: PredicateWithIndex<I, A>): Separated<Type2<F, L, A>, Type2<F, L, A>>
}

export interface FilterableWithIndex2C<F extends URIS2, I, L> extends FunctorWithIndex2C<F, I, L>, Filterable2C<F, L> {
  readonly partitionMapWithIndex: <RL, RR, A>(
    fa: Type2<F, L, A>,
    f: (i: I, a: A) => Either<RL, RR>
  ) => Separated<Type2<F, L, RL>, Type2<F, L, RR>>
  readonly partitionWithIndex: PartitionWithIndex2C<F, I, L>
  readonly filterMapWithIndex: <A, B>(fa: Type2<F, L, A>, f: (i: I, a: A) => Option<B>) => Type2<F, L, B>
  readonly filterWithIndex: FilterWithIndex2C<F, I, L>
}

interface FilterWithIndex3<F extends URIS3, I> {
  <U, L, A, B extends A>(fa: Type3<F, U, L, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): Type3<F, U, L, B>
  <U, L, A>(fa: Type3<F, U, L, A>, predicateWithIndex: PredicateWithIndex<I, A>): Type3<F, U, L, A>
}

interface PartitionWithIndex3<F extends URIS3, I> {
  <U, L, A, B extends A>(fa: Type3<F, U, L, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): Separated<
    Type3<F, U, L, A>,
    Type3<F, U, L, B>
  >
  <U, L, A>(fa: Type3<F, U, L, A>, predicateWithIndex: PredicateWithIndex<I, A>): Separated<
    Type3<F, U, L, A>,
    Type3<F, U, L, A>
  >
}

export interface FilterableWithIndex3<F extends URIS3, I> extends FunctorWithIndex3<F, I>, Filterable3<F> {
  readonly partitionMapWithIndex: <RL, RR, U, L, A>(
    fa: Type3<F, U, L, A>,
    f: (i: I, a: A) => Either<RL, RR>
  ) => Separated<Type3<F, U, L, RL>, Type3<F, U, L, RR>>
  readonly partitionWithIndex: PartitionWithIndex3<F, I>
  readonly filterMapWithIndex: <U, L, A, B>(fa: Type3<F, U, L, A>, f: (i: I, a: A) => Option<B>) => Type3<F, U, L, B>
  readonly filterWithIndex: FilterWithIndex3<F, I>
}

interface FilterWithIndex3C<F extends URIS3, I, U, L> {
  <A, B extends A>(fa: Type3<F, U, L, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): Type3<F, U, L, B>
  <A>(fa: Type3<F, U, L, A>, predicateWithIndex: PredicateWithIndex<I, A>): Type3<F, U, L, A>
}

interface PartitionWithIndex3C<F extends URIS3, I, U, L> {
  <A, B extends A>(fa: Type3<F, U, L, A>, refinementWithIndex: RefinementWithIndex<I, A, B>): Separated<
    Type3<F, U, L, A>,
    Type3<F, U, L, B>
  >
  <A>(fa: Type3<F, U, L, A>, predicateWithIndex: PredicateWithIndex<I, A>): Separated<
    Type3<F, U, L, A>,
    Type3<F, U, L, A>
  >
}

export interface FilterableWithIndex3C<F extends URIS3, I, U, L>
  extends FunctorWithIndex3C<F, I, U, L>,
    Filterable3C<F, U, L> {
  readonly partitionMapWithIndex: <RL, RR, A>(
    fa: Type3<F, U, L, A>,
    f: (i: I, a: A) => Either<RL, RR>
  ) => Separated<Type3<F, U, L, RL>, Type3<F, U, L, RR>>
  readonly partitionWithIndex: PartitionWithIndex3C<F, I, U, L>
  readonly filterMapWithIndex: <A, B>(fa: Type3<F, U, L, A>, f: (i: I, a: A) => Option<B>) => Type3<F, U, L, B>
  readonly filterWithIndex: FilterWithIndex3C<F, I, U, L>
}

/**
 * @file Adapted from http://okmij.org/ftp/Computation/free-monad.html and https://github.com/purescript/purescript-free
 */
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monad, Monad1, Monad2, Monad2C, Monad3, Monad3C }  from  './Monad.ts'
import { toString }  from  './function.ts'

export const URI = 'Free'

export type URI = typeof URI

declare module './HKT' {
  interface URI2HKT2<L, A> {
    Free: Free<L, A>
  }
}

/**
 * @data
 * @constructor Pure
 * @constructor Impure
 * @since 1.0.0
 */
export type Free<F, A> = Pure<F, A> | Impure<F, A, any>

export class Pure<F, A> {
  readonly _tag: 'Pure' = 'Pure'
  readonly _A!: A
  readonly _L!: F
  readonly _URI!: URI
  constructor(readonly value: A) {}
  map<B>(f: (a: A) => B): Free<F, B> {
    return new Pure(f(this.value))
  }
  ap<B>(fab: Free<F, (a: A) => B>): Free<F, B> {
    return fab.chain(f => this.map(f)) // <- derived
  }
  /**
   * Flipped version of `ap`
   */
  ap_<B, C>(this: Free<F, (b: B) => C>, fb: Free<F, B>): Free<F, C> {
    return fb.ap(this)
  }
  chain<B>(f: (a: A) => Free<F, B>): Free<F, B> {
    return f(this.value)
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `new Pure(${toString(this.value)})`
  }
  isPure(): this is Pure<F, A> {
    return true
  }
  isImpure(): this is Impure<F, A, any> {
    return false
  }
}

export class Impure<F, A, X> {
  readonly _tag: 'Impure' = 'Impure'
  readonly _A!: A
  readonly _L!: F
  readonly _URI!: URI
  constructor(readonly fx: HKT<F, X>, readonly f: (x: X) => Free<F, A>) {}
  map<B>(f: (a: A) => B): Free<F, B> {
    return new Impure(this.fx, x => this.f(x).map(f))
  }
  ap<B>(fab: Free<F, (a: A) => B>): Free<F, B> {
    return fab.chain(f => this.map(f)) // <- derived
  }
  ap_<B, C>(this: Free<F, (b: B) => C>, fb: Free<F, B>): Free<F, C> {
    return fb.ap(this)
  }
  chain<B>(f: (a: A) => Free<F, B>): Free<F, B> {
    return new Impure(this.fx, x => this.f(x).chain(f))
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `new Impure(${(toString(this.fx), toString(this.f))})`
  }
  isPure(): this is Pure<F, A> {
    return false
  }
  isImpure(): this is Impure<F, A, X> {
    return true
  }
}

/**
 * @since 1.0.0
 */
export const of = <F, A>(a: A): Free<F, A> => {
  return new Pure(a)
}

/**
 * Lift an impure value described by the generating type constructor `F` into the free monad
 *
 * @since 1.0.0
 */
export const liftF = <F, A>(fa: HKT<F, A>): Free<F, A> => {
  return new Impure(fa, a => of(a))
}

const substFree = <F, G>(f: <A>(fa: HKT<F, A>) => Free<G, A>): (<A>(fa: Free<F, A>) => Free<G, A>) => {
  function go<A>(fa: Free<F, A>): Free<G, A> {
    switch (fa._tag) {
      case 'Pure':
        return of(fa.value)
      case 'Impure':
        return f(fa.fx).chain(x => go(fa.f(x)))
    }
  }
  return go
}

/**
 * Use a natural transformation to change the generating type constructor of a free monad
 *
 * @since 1.0.0
 */
export function hoistFree<F extends URIS3 = never, G extends URIS3 = never>(
  nt: <U, L, A>(fa: Type3<F, U, L, A>) => Type3<G, U, L, A>
): <A>(fa: Free<F, A>) => Free<G, A>
export function hoistFree<F extends URIS2 = never, G extends URIS2 = never>(
  nt: <L, A>(fa: Type2<F, L, A>) => Type2<G, L, A>
): <A>(fa: Free<F, A>) => Free<G, A>
export function hoistFree<F extends URIS = never, G extends URIS = never>(
  nt: <A>(fa: Type<F, A>) => Type<G, A>
): <A>(fa: Free<F, A>) => Free<G, A>
export function hoistFree<F, G>(nt: <A>(fa: HKT<F, A>) => HKT<G, A>): <A>(fa: Free<F, A>) => Free<G, A>
export function hoistFree<F, G>(nt: <A>(fa: HKT<F, A>) => HKT<G, A>): <A>(fa: Free<F, A>) => Free<G, A> {
  return substFree(fa => liftF(nt(fa)))
}

export interface FoldFree3<M extends URIS3> {
  <F extends URIS3, U, L, A>(nt: <X>(fa: Type3<F, U, L, X>) => Type3<M, U, L, X>, fa: Free<F, A>): Type3<M, U, L, A>
  <F extends URIS2, U, L, A>(nt: <X>(fa: Type2<F, L, X>) => Type3<M, U, L, X>, fa: Free<F, A>): Type3<M, U, L, A>
  <F extends URIS, U, L, A>(nt: <X>(fa: Type<F, X>) => Type3<M, U, L, X>, fa: Free<F, A>): Type3<M, U, L, A>
}

export interface FoldFree3C<M extends URIS3, U, L> {
  <F extends URIS3, A>(nt: <X>(fa: Type3<F, U, L, X>) => Type3<M, U, L, X>, fa: Free<F, A>): Type3<M, U, L, A>
  <F extends URIS2, A>(nt: <X>(fa: Type2<F, L, X>) => Type3<M, U, L, X>, fa: Free<F, A>): Type3<M, U, L, A>
  <F extends URIS, A>(nt: <X>(fa: Type<F, X>) => Type3<M, U, L, X>, fa: Free<F, A>): Type3<M, U, L, A>
}

export interface FoldFree2<M extends URIS2> {
  <F extends URIS2, L, A>(nt: <X>(fa: Type2<F, L, X>) => Type2<M, L, X>, fa: Free<F, A>): Type2<M, L, A>
  <F extends URIS, L, A>(nt: <X>(fa: Type<F, X>) => Type2<M, L, X>, fa: Free<F, A>): Type2<M, L, A>
}

export interface FoldFree2C<M extends URIS2, L> {
  <F extends URIS2, A>(nt: <X>(fa: Type2<F, L, X>) => Type2<M, L, X>, fa: Free<F, A>): Type2<M, L, A>
  <F extends URIS, A>(nt: <X>(fa: Type<F, X>) => Type2<M, L, X>, fa: Free<F, A>): Type2<M, L, A>
}

/**
 * @since 1.0.0
 */
export function foldFree<M extends URIS3>(M: Monad3<M>): FoldFree3<M>
export function foldFree<M extends URIS3, U, L>(M: Monad3C<M, U, L>): FoldFree3C<M, U, L>
export function foldFree<M extends URIS2>(M: Monad2<M>): FoldFree2<M>
export function foldFree<M extends URIS2, L>(M: Monad2C<M, L>): FoldFree2C<M, L>
export function foldFree<M extends URIS>(
  M: Monad1<M>
): <F extends URIS, A>(nt: <X>(fa: Type<F, X>) => Type<M, X>, fa: Free<F, A>) => Type<M, A>
export function foldFree<M>(M: Monad<M>): <F, A>(nt: <X>(fa: HKT<F, X>) => HKT<M, X>, fa: Free<F, A>) => HKT<M, A>
export function foldFree<M>(M: Monad<M>): <F, A>(nt: any, fa: Free<F, A>) => HKT<M, A> {
  return (nt, fa) => {
    if (fa.isPure()) {
      return M.of(fa.value)
    } else {
      return M.chain(nt(fa.fx), x => foldFree(M)(nt, fa.f(x)))
    }
  }
}

