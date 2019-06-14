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

