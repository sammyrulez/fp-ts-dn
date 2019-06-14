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

declare module './HKT.ts'
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

declare module './HKT.ts'
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

declare module './HKT.ts'
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

declare module './HKT.ts'
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

declare module './HKT.ts'
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

declare module './HKT.ts'
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

declare module './HKT.ts'
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
} from './Applicative.ts'
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
} from './FunctorWithIndex.ts'
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

declare module './HKT.ts'
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

/**
 * @file A `FunctorWithIndex` is a type constructor which supports a mapping operation `mapWithIndex`.
 *
 * `mapWithIndex` can be used to turn functions `i -> a -> b` into functions `f a -> f b` whose argument and return types use the type
 * constructor `f` to represent some computational context.
 *
 * Instances must satisfy the following laws:
 *
 * 1. Identity: `F.mapWithIndex(fa, (_i, a) => a) = fa`
 * 2. Composition: `F.mapWithIndex(fa, (_i, a) => bc(ab(a))) = F.mapWithIndex(F.mapWithIndex(fa, ab), bc)`
 */
import { HKT, Type, Type2, Type3, Type4, URIS, URIS2, URIS3, URIS4 }  from  './HKT.ts'
import {
  Functor,
  Functor1,
  Functor2,
  Functor3,
  Functor4,
  Functor2C,
  Functor3C,
  FunctorComposition,
  FunctorComposition11,
  FunctorComposition12,
  FunctorComposition12C,
  FunctorComposition21,
  FunctorComposition2C1,
  FunctorComposition22,
  FunctorComposition22C,
  FunctorComposition3C1,
  getFunctorComposition
} from './Functor.ts'

/**
 * @since 1.12.0
 */
export interface FunctorWithIndex<F, I> extends Functor<F> {
  readonly mapWithIndex: <A, B>(fa: HKT<F, A>, f: (i: I, a: A) => B) => HKT<F, B>
}

export interface FunctorWithIndex1<F extends URIS, I> extends Functor1<F> {
  readonly mapWithIndex: <A, B>(fa: Type<F, A>, f: (i: I, a: A) => B) => Type<F, B>
}

export interface FunctorWithIndex2<F extends URIS2, I> extends Functor2<F> {
  readonly mapWithIndex: <L, A, B>(fa: Type2<F, L, A>, f: (i: I, a: A) => B) => Type2<F, L, B>
}

export interface FunctorWithIndex3<F extends URIS3, I> extends Functor3<F> {
  readonly mapWithIndex: <U, L, A, B>(fa: Type3<F, U, L, A>, f: (i: I, a: A) => B) => Type3<F, U, L, B>
}

export interface FunctorWithIndex4<F extends URIS4, I> extends Functor4<F> {
  readonly mapWithIndex: <X, U, L, A, B>(fa: Type4<F, X, U, L, A>, f: (i: I, a: A) => B) => Type4<F, X, U, L, B>
}

export interface FunctorWithIndex2C<F extends URIS2, I, L> extends Functor2C<F, L> {
  readonly mapWithIndex: <A, B>(fa: Type2<F, L, A>, f: (i: I, a: A) => B) => Type2<F, L, B>
}

export interface FunctorWithIndex3C<F extends URIS3, I, U, L> extends Functor3C<F, U, L> {
  readonly mapWithIndex: <A, B>(fa: Type3<F, U, L, A>, f: (i: I, a: A) => B) => Type3<F, U, L, B>
}

export interface FunctorWithIndexComposition<F, FI, G, GI> extends FunctorComposition<F, G> {
  readonly mapWithIndex: <A, B>(fga: HKT<F, HKT<G, A>>, f: (i: [FI, GI], a: A) => B) => HKT<F, HKT<G, B>>
}

export interface FunctorWithIndexComposition11<F extends URIS, FI, G extends URIS, GI>
  extends FunctorComposition11<F, G> {
  readonly mapWithIndex: <A, B>(fa: Type<F, Type<G, A>>, f: (i: [FI, GI], a: A) => B) => Type<F, Type<G, B>>
}

export interface FunctorWithIndexComposition12<F extends URIS, FI, G extends URIS2, GI>
  extends FunctorComposition12<F, G> {
  readonly mapWithIndex: <L, A, B>(fa: Type<F, Type2<G, L, A>>, f: (i: [FI, GI], a: A) => B) => Type<F, Type2<G, L, B>>
}

export interface FunctorWithIndexComposition12C<F extends URIS, FI, G extends URIS2, GI, L>
  extends FunctorComposition12C<F, G, L> {
  readonly mapWithIndex: <A, B>(fa: Type<F, Type2<G, L, A>>, f: (i: [FI, GI], a: A) => B) => Type<F, Type2<G, L, B>>
}

export interface FunctorWithIndexComposition21<F extends URIS2, FI, G extends URIS, GI>
  extends FunctorComposition21<F, G> {
  readonly mapWithIndex: <L, A, B>(fa: Type2<F, L, Type<G, A>>, f: (i: [FI, GI], a: A) => B) => Type2<F, L, Type<G, B>>
}

export interface FunctorWithIndexComposition2C1<F extends URIS2, FI, G extends URIS, GI, L>
  extends FunctorComposition2C1<F, G, L> {
  readonly mapWithIndex: <A, B>(fa: Type2<F, L, Type<G, A>>, f: (i: [FI, GI], a: A) => B) => Type2<F, L, Type<G, B>>
}

export interface FunctorWithIndexComposition22<F extends URIS2, FI, G extends URIS2, GI>
  extends FunctorComposition22<F, G> {
  readonly mapWithIndex: <L, M, A, B>(
    fa: Type2<F, L, Type2<G, M, A>>,
    f: (i: [FI, GI], a: A) => B
  ) => Type2<F, L, Type2<G, M, B>>
}

export interface FunctorWithIndexComposition22C<F extends URIS2, FI, G extends URIS2, GI, LG>
  extends FunctorComposition22C<F, G, LG> {
  readonly mapWithIndex: <L, A, B>(
    fa: Type2<F, L, Type2<G, LG, A>>,
    f: (i: [FI, GI], a: A) => B
  ) => Type2<F, L, Type2<G, LG, B>>
}

export interface FunctorWithIndexComposition3C1<F extends URIS3, FI, G extends URIS, GI, UF, LF>
  extends FunctorComposition3C1<F, G, UF, LF> {
  readonly mapWithIndex: <A, B>(
    fa: Type3<F, UF, LF, Type<G, A>>,
    f: (i: [FI, GI], a: A) => B
  ) => Type3<F, UF, LF, Type<G, B>>
}

/**
 * @since 1.12.0
 */
export function getFunctorWithIndexComposition<F extends URIS3, FI, G extends URIS, GI, U, L>(
  F: FunctorWithIndex3C<F, FI, U, L>,
  G: FunctorWithIndex1<G, FI>
): FunctorWithIndexComposition3C1<F, FI, G, GI, U, L>
export function getFunctorWithIndexComposition<F extends URIS2, FI, G extends URIS2, GI, L>(
  F: FunctorWithIndex2<F, FI>,
  G: FunctorWithIndex2C<G, FI, L>
): FunctorWithIndexComposition22C<F, FI, G, GI, L>
export function getFunctorWithIndexComposition<F extends URIS2, FI, G extends URIS2, GI>(
  F: FunctorWithIndex2<F, FI>,
  G: FunctorWithIndex2<G, FI>
): FunctorWithIndexComposition22<F, FI, G, GI>
export function getFunctorWithIndexComposition<F extends URIS2, FI, G extends URIS, GI, L>(
  F: FunctorWithIndex2C<F, FI, L>,
  G: FunctorWithIndex1<G, GI>
): FunctorWithIndexComposition2C1<F, FI, G, GI, L>
export function getFunctorWithIndexComposition<F extends URIS2, FI, G extends URIS, GI>(
  F: FunctorWithIndex2<F, FI>,
  G: FunctorWithIndex1<G, GI>
): FunctorWithIndexComposition21<F, FI, G, GI>
export function getFunctorWithIndexComposition<F extends URIS, FI, G extends URIS2, GI, L>(
  F: FunctorWithIndex1<F, FI>,
  G: FunctorWithIndex2C<G, GI, L>
): FunctorWithIndexComposition12C<F, FI, G, GI, L>
export function getFunctorWithIndexComposition<F extends URIS, FI, G extends URIS2, GI>(
  F: FunctorWithIndex1<F, FI>,
  G: FunctorWithIndex2<G, GI>
): FunctorWithIndexComposition12<F, FI, G, GI>
export function getFunctorWithIndexComposition<F extends URIS, FI, G extends URIS, GI>(
  F: FunctorWithIndex1<F, FI>,
  G: FunctorWithIndex1<G, GI>
): FunctorWithIndexComposition11<F, FI, G, GI>
export function getFunctorWithIndexComposition<F, FI, G, GI>(
  F: FunctorWithIndex<F, FI>,
  G: FunctorWithIndex<G, GI>
): FunctorWithIndexComposition<F, FI, G, GI>
export function getFunctorWithIndexComposition<F, FI, G, GI>(
  F: FunctorWithIndex<F, FI>,
  G: FunctorWithIndex<G, GI>
): FunctorWithIndexComposition<F, FI, G, GI> {
  return {
    ...getFunctorComposition(F, G),
    mapWithIndex: (fga, f) => F.mapWithIndex(fga, (fi, ga) => G.mapWithIndex(ga, (gi, a) => f([fi, gi], a)))
  }
}

import { Alt1 }  from  './Alt.ts'
import { Applicative }  from  './Applicative.ts'
import { ChainRec1, tailRec }  from  './ChainRec.ts'
import { Comonad1 }  from  './Comonad.ts'
import { Either }  from  './Either.ts'
import { Foldable2v1 }  from  './Foldable2v.ts'
import { Lazy, toString }  from  './function.ts'
import { HKT }  from  './HKT.ts'
import { Monad1 }  from  './Monad.ts'
import { Monoid }  from  './Monoid.ts'
import { Setoid, fromEquals }  from  './Setoid.ts'
import { Traversable2v1 }  from  './Traversable2v.ts'
import { Show }  from  './Show.ts'

declare module './HKT.ts'
  interface URI2HKT<A> {
    Identity: Identity<A>
  }
}

export const URI = 'Identity'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export class Identity<A> {
  readonly _A!: A
  readonly _URI!: URI
  constructor(readonly value: A) {}
  map<B>(f: (a: A) => B): Identity<B> {
    return new Identity(f(this.value))
  }
  ap<B>(fab: Identity<(a: A) => B>): Identity<B> {
    return this.map(fab.value)
  }
  /**
   * Flipped version of `ap`
   */
  ap_<B, C>(this: Identity<(b: B) => C>, fb: Identity<B>): Identity<C> {
    return fb.ap(this)
  }
  chain<B>(f: (a: A) => Identity<B>): Identity<B> {
    return f(this.value)
  }
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    return f(b, this.value)
  }
  alt(fx: Identity<A>): Identity<A> {
    return this
  }

  /**
   * Lazy version of `alt`
   *
   * @example
   * import { Identity }  from  'fp-ts/lib/Identity.ts'
   *
   * const a = new Identity(1)
   * assert.deepStrictEqual(a.orElse(() => new Identity(2)), a)
   *
   * @since 1.6.0
   */
  orElse(fx: Lazy<Identity<A>>): Identity<A> {
    return this
  }
  extract(): A {
    return this.value
  }
  extend<B>(f: (ea: Identity<A>) => B): Identity<B> {
    return of(f(this))
  }
  fold<B>(f: (a: A) => B): B {
    return f(this.value)
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `new Identity(${toString(this.value)})`
  }
}

/**
 * @since 1.17.0
 */
export const getShow = <A>(S: Show<A>): Show<Identity<A>> => {
  return {
    show: i => `new Identity(${S.show(i.value)})`
  }
}

/**
 * @since 1.0.0
 */
export const getSetoid = <A>(S: Setoid<A>): Setoid<Identity<A>> => {
  return fromEquals((x, y) => S.equals(x.value, y.value))
}

const map = <A, B>(fa: Identity<A>, f: (a: A) => B): Identity<B> => {
  return fa.map(f)
}

const of = <A>(a: A): Identity<A> => {
  return new Identity(a)
}

const ap = <A, B>(fab: Identity<(a: A) => B>, fa: Identity<A>): Identity<B> => {
  return fa.ap(fab)
}

const chain = <A, B>(fa: Identity<A>, f: (a: A) => Identity<B>): Identity<B> => {
  return fa.chain(f)
}

const reduce = <A, B>(fa: Identity<A>, b: B, f: (b: B, a: A) => B): B => {
  return fa.reduce(b, f)
}

const foldMap = <M>(M: Monoid<M>) => <A>(fa: Identity<A>, f: (a: A) => M): M => {
  return f(fa.value)
}

const foldr = <A, B>(fa: Identity<A>, b: B, f: (a: A, b: B) => B): B => {
  return f(fa.value, b)
}

const alt = <A>(fx: Identity<A>, fy: Identity<A>): Identity<A> => {
  return fx.alt(fy)
}

const extend = <A, B>(ea: Identity<A>, f: (ea: Identity<A>) => B): Identity<B> => {
  return ea.extend(f)
}

const extract = <A>(fa: Identity<A>): A => {
  return fa.value
}

const chainRec = <A, B>(a: A, f: (a: A) => Identity<Either<A, B>>): Identity<B> => {
  return new Identity(tailRec(a => f(a).value, a))
}

const traverse = <F>(F: Applicative<F>) => <A, B>(ta: Identity<A>, f: (a: A) => HKT<F, B>): HKT<F, Identity<B>> => {
  return F.map(f(ta.value), of)
}

const sequence = <F>(F: Applicative<F>) => <A>(ta: Identity<HKT<F, A>>): HKT<F, Identity<A>> => {
  return F.map(ta.value, of)
}

/**
 * @since 1.0.0
 */
export const identity: Monad1<URI> &
  Foldable2v1<URI> &
  Traversable2v1<URI> &
  Alt1<URI> &
  Comonad1<URI> &
  ChainRec1<URI> = {
  URI,
  map,
  of,
  ap,
  chain,
  reduce,
  foldMap,
  foldr,
  traverse,
  sequence,
  alt,
  extract,
  extend,
  chainRec
}

import * as alt  from  './Alt.ts'
export { alt }
import * as alternative  from  './Alternative.ts'
export { alternative }
import * as applicative  from  './Applicative.ts'
export { applicative }
import * as apply  from  './Apply.ts'
export { apply }
import * as array  from  './Array.ts'
export { array }
import * as bifunctor  from  './Bifunctor.ts'
export { bifunctor }
import * as booleanAlgebra  from  './BooleanAlgebra.ts'
export { booleanAlgebra }
import * as bounded  from  './Bounded.ts'
export { bounded }
import * as boundedDistributiveLattice  from  './BoundedDistributiveLattice.ts'
export { boundedDistributiveLattice }
import * as boundedJoinSemilattice  from  './BoundedJoinSemilattice.ts'
export { boundedJoinSemilattice }
import * as boundedLattice  from  './BoundedLattice.ts'
export { boundedLattice }
import * as boundedMeetSemilattice  from  './BoundedMeetSemilattice.ts'
export { boundedMeetSemilattice }
import * as category  from  './Category.ts'
export { category }
import * as chain  from  './Chain.ts'
export { chain }
import * as chainRec  from  './ChainRec.ts'
export { chainRec }
import * as choice  from  './Choice.ts'
export { choice }
import * as comonad  from  './Comonad.ts'
export { comonad }
import * as console  from  './Console.ts'
export { console }
import * as const_  from  './Const.ts'
export { const_ as const }
import * as contravariant  from  './Contravariant.ts'
export { contravariant }
import * as date  from  './Date.ts'
export { date }
import * as distributiveLattice  from  './DistributiveLattice.ts'
export { distributiveLattice }
import * as either  from  './Either.ts'
export { either }
import * as eitherT  from  './EitherT.ts'
export { eitherT }
import * as exception  from  './Exception.ts'
export { exception }
import * as extend  from  './Extend.ts'
export { extend }
import * as field  from  './Field.ts'
export { field }
import * as filterable  from  './Filterable.ts'
export { filterable }
import * as filterableWithIndex  from  './FilterableWithIndex.ts'
export { filterableWithIndex }
import * as foldable  from  './Foldable.ts'
export { foldable }
import * as foldable2v  from  './Foldable2v.ts'
export { foldable2v }
import * as foldableWithIndex  from  './FoldableWithIndex.ts'
export { foldableWithIndex }
import * as free  from  './Free.ts'
export { free }
import * as freeGroup  from  './FreeGroup.ts'
export { freeGroup }
import * as function_  from  './function.ts'
export { function_ as function }
import * as functor  from  './Functor.ts'
export { functor }
import * as functorWithIndex  from  './FunctorWithIndex.ts'
export { functorWithIndex }
import * as group  from  './Group.ts'
export { group }
import * as heytingAlgebra  from  './HeytingAlgebra.ts'
export { heytingAlgebra }
import * as hkt  from  './HKT.ts'
export { hkt }
import * as identity  from  './Identity.ts'
export { identity }
import * as invariant  from  './Invariant.ts'
export { invariant }
import * as io  from  './IO.ts'
export { io }
import * as ioEither  from  './IOEither.ts'
export { ioEither }
import * as ioRef  from  './IORef.ts'
export { ioRef }
import * as ixIO  from  './IxIO.ts'
export { ixIO }
import * as ixMonad  from  './IxMonad.ts'
export { ixMonad }
import * as joinSemilattice  from  './JoinSemilattice.ts'
export { joinSemilattice }
import * as lattice  from  './Lattice.ts'
export { lattice }
import * as magma  from  './Magma.ts'
export { magma }
import * as map  from  './Map.ts'
export { map }
import * as meetSemilattice  from  './MeetSemilattice.ts'
export { meetSemilattice }
import * as monad  from  './Monad.ts'
export { monad }
import * as monadIO  from  './MonadIO.ts'
export { monadIO }
import * as monadTask  from  './MonadTask.ts'
export { monadTask }
import * as monadThrow  from  './MonadThrow.ts'
export { monadThrow }
import * as monoid  from  './Monoid.ts'
export { monoid }
import * as monoidal  from  './Monoidal.ts'
export { monoidal }
import * as nonEmptyArray  from  './NonEmptyArray.ts'
export { nonEmptyArray }
import * as nonEmptyArray2v  from  './NonEmptyArray2v.ts'
export { nonEmptyArray2v }
import * as option  from  './Option.ts'
export { option }
import * as optionT  from  './OptionT.ts'
export { optionT }
import * as ord  from  './Ord.ts'
export { ord }
import * as ordering  from  './Ordering.ts'
export { ordering }
import * as pair  from  './Pair.ts'
export { pair }
import * as plus  from  './Plus.ts'
export { plus }
import * as profunctor  from  './Profunctor.ts'
export { profunctor }
import * as random  from  './Random.ts'
export { random }
import * as reader  from  './Reader.ts'
export { reader }
import * as readerT  from  './ReaderT.ts'
export { readerT }
import * as readerTaskEither  from  './ReaderTaskEither.ts'
export { readerTaskEither }
import * as record  from  './Record.ts'
export { record }
import * as ring  from  './Ring.ts'
export { ring }
import * as semigroup  from  './Semigroup.ts'
export { semigroup }
import * as semigroupoid  from  './Semigroupoid.ts'
export { semigroupoid }
import * as semiring  from  './Semiring.ts'
export { semiring }
import * as set  from  './Set.ts'
export { set }
import * as setoid  from  './Setoid.ts'
export { setoid }
import * as show  from  './Show.ts'
export { show }
import * as state  from  './State.ts'
export { state }
import * as stateT  from  './StateT.ts'
export { stateT }
import * as store  from  './Store.ts'
export { store }
import * as strmap  from  './StrMap.ts'
export { strmap }
import * as strong  from  './Strong.ts'
export { strong }
import * as task  from  './Task.ts'
export { task }
import * as taskEither  from  './TaskEither.ts'
export { taskEither }
import * as these  from  './These.ts'
export { these }
import * as trace  from  './Trace.ts'
export { trace }
import * as traced  from  './Traced.ts'
export { traced }
import * as traversable  from  './Traversable.ts'
export { traversable }
import * as traversable2v  from  './Traversable2v.ts'
export { traversable2v }
import * as traversableWithIndex  from  './TraversableWithIndex.ts'
export { traversableWithIndex }
import * as tree  from  './Tree.ts'
export { tree }
import * as tuple  from  './Tuple.ts'
export { tuple }
import * as unfoldable  from  './Unfoldable.ts'
export { unfoldable }
import * as validation  from  './Validation.ts'
export { validation }
import * as writer  from  './Writer.ts'
export { writer }
import * as compactable  from  './Compactable.ts'
export { compactable }
import * as witherable  from  './Witherable.ts'
export { witherable }
import * as zipper  from  './Zipper.ts'
export { zipper }

/**
 * @file `IO<A>` represents a non-deterministic synchronous computation that can cause side effects, yields a value of
 * type `A` and **never fails**. If you want to represent a synchronous computation that may fail, please see
 * `IOEither`.
 *
 * IO actions are terminated by calling their `run()` method that executes the computation and returns the result.
 * Ideally each application should call `run()` only once for a root value of type `Task` or `IO` that represents the entire
 * application. However, this might vary a bit depending on how you construct your application.  An application
 * framework with fp-ts types might take care of calling `run()` for you, while another application framework without
 * fp-ts typing might force you to call `run()` at multiple locations whenever the framework demands less strictly typed
 * values as inputs for its method calls.
 *
 * Below are some basic examples of how you can wrap values and function calls with `IO`.
 *
 * ```ts
 * import { IO, io }  from  'fp-ts/lib/IO.ts'
 *
 * const constant: IO<number> = io.of(123);
 * constant.run()  // returns 123
 *
 * const random: IO<number> = new IO(() => Math.random())
 * random.run()  // returns a random number
 * random.run()  // returns another random number
 *
 * const log = (...args): IO<void> => new IO(() => console.log(...args));
 * log('hello world').run()  // returns undefined and outputs "hello world" to console
 * ```
 *
 * In the example above we implemented type safe alternatives for `Math.random()` and `console.log()`. The main
 * motivation was to explain how you can wrap values. However, fp-ts provides type safe alternatives for such basic
 * tools through `Console` and `Random` modules. So you don't need to constantly redefine them.
 *
 * The next code snippet below is an example of a case where type safety affects the end result. Using `console.log()`
 * directly would break the code, resulting in both logging actions being executed when the value is not `null`.  You
 * can confirm this by removing `.run()` from the end of the example code and replacing calls to `log()` with
 * standard`console.log()`.
 *
 * ```ts
 * import { IO }  from  'fp-ts/lib/IO.ts'
 * import { fromNullable }  from  'fp-ts/lib/Option.ts'
 * import { log }  from  'fp-ts/lib/Console.ts'
 *
 * const logger = (input: number|null) => fromNullable(input).fold(
 *   log('Received null'),
 *   (value) => log(`Received ${value}`),
 * );
 *
 * logger(123).run();  // returns undefined and outputs "Received 123" to console
 * ```
 *
 * In addition to creating IO actions we need a way to combine them to build the application.  For example we might have
 * several `IO<void>` actions that only cause side effects without returning a result.  We  can combine several `IO<void>`
 * actions into one for sequential execution with `sequence_(io, array)` as follows. This is useful when you care about
 * the execution order but do not care about the results.
 *
 * ```ts
 * import { IO, io }  from  'fp-ts/lib/IO.ts'
 * import { array }  from  'fp-ts/lib/Array.ts'
 * import { sequence_ }  from  'fp-ts/lib/Foldable2v.ts'
 * import { log }  from  'fp-ts/lib/Console.ts'
 *
 * const logGiraffe: IO<void> = log('giraffe');
 * const logZebra: IO<void> = log('zebra');
 *
 * const logGiraffeThenZebra: IO<void> = sequence_(io, array)([ logGiraffe, logZebra ])
 *
 * logGiraffeThenZebra.run();  // returns undefined and outputs words "giraffe" and "zebra" to console
 * ```
 *
 * We might also have several IO actions that yield some values that we want to capture. We can combine them by
 * using `sequenceS(io)` over an object matching the structure of the expected result. This is useful when you care
 * about the results but do not care about the execution order.
 *
 * ```ts
 * import { IO, io }  from  'fp-ts/lib/IO.ts'
 * import { sequenceS }  from  'fp-ts/lib/Apply.ts'
 *
 * interface Result {
 *   name: string,
 *   age: number,
 * }
 *
 * const computations: { [K in keyof Result]: IO<Result[K]> } = {
 *   name: io.of('Aristotle'),
 *   age: io.of(60),
 * }
 *
 * const computation: IO<Result> = sequenceS(io)(computations)
 *
 * computation.run()  // returns { name: 'Aristotle', age: 60 }
 * ```
 */
import { Monad1 }  from  './Monad.ts'
import { Monoid }  from  './Monoid.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Lazy, constIdentity, toString, constant, identity }  from  './function.ts'
import { MonadIO1 }  from  './MonadIO.ts'

declare module './HKT.ts'
  interface URI2HKT<A> {
    IO: IO<A>
  }
}

export const URI = 'IO'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export class IO<A> {
  readonly _A!: A
  readonly _URI!: URI
  constructor(readonly run: Lazy<A>) {}
  map<B>(f: (a: A) => B): IO<B> {
    return new IO(() => f(this.run()))
  }
  ap<B>(fab: IO<(a: A) => B>): IO<B> {
    return new IO(() => fab.run()(this.run()))
  }
  /**
   * Flipped version of `ap`
   */
  ap_<B, C>(this: IO<(b: B) => C>, fb: IO<B>): IO<C> {
    return fb.ap(this)
  }
  /**
   * Combine two effectful actions, keeping only the result of the first
   * @since 1.6.0
   */
  applyFirst<B>(fb: IO<B>): IO<A> {
    return fb.ap(this.map(constant))
  }
  /**
   * Combine two effectful actions, keeping only the result of the second
   * @since 1.5.0
   */
  applySecond<B>(fb: IO<B>): IO<B> {
    return fb.ap(this.map(constIdentity as () => (b: B) => B))
  }
  chain<B>(f: (a: A) => IO<B>): IO<B> {
    return new IO(() => f(this.run()).run())
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `new IO(${toString(this.run)})`
  }
}

const map = <A, B>(fa: IO<A>, f: (a: A) => B): IO<B> => {
  return fa.map(f)
}

const of = <A>(a: A): IO<A> => {
  return new IO(() => a)
}

const ap = <A, B>(fab: IO<(a: A) => B>, fa: IO<A>): IO<B> => {
  return fa.ap(fab)
}

const chain = <A, B>(fa: IO<A>, f: (a: A) => IO<B>): IO<B> => {
  return fa.chain(f)
}

/**
 * @since 1.0.0
 */
export const getSemigroup = <A>(S: Semigroup<A>): Semigroup<IO<A>> => {
  return {
    concat: (x, y) =>
      new IO(() => {
        const xr = x.run()
        const yr = y.run()
        return S.concat(xr, yr)
      })
  }
}

/**
 * @since 1.0.0
 */
export const getMonoid = <A>(M: Monoid<A>): Monoid<IO<A>> => {
  return { ...getSemigroup(M), empty: of(M.empty) }
}

const fromIO = identity

/**
 * @since 1.0.0
 */
export const io: Monad1<URI> & MonadIO1<URI> = {
  URI,
  map,
  of,
  ap,
  chain,
  fromIO
}

/**
 * @file `IOEither<L, A>` represents a synchronous computation that either yields a value of type `A` or fails yielding an
 * error of type `L`. If you want to represent a synchronous computation that never fails, please see `IO`.
 */
import { Alt2 }  from  './Alt.ts'
import { Bifunctor2 }  from  './Bifunctor.ts'
import { Either, left as eitherLeft, right as eitherRight, toError, tryCatch2v as eitherTryCatch2v }  from  './Either.ts'
import * as eitherT  from  './EitherT.ts'
import { constant, constIdentity, Lazy }  from  './function.ts'
import { IO, io }  from  './IO.ts'
import { Monad2 }  from  './Monad.ts'
import { MonadThrow2 }  from  './MonadThrow.ts'

declare module './HKT.ts'
  interface URI2HKT2<L, A> {
    IOEither: IOEither<L, A>
  }
}

export const URI = 'IOEither'

export type URI = typeof URI

const T = eitherT.getEitherT2v(io)
const foldT = eitherT.fold(io)

/**
 * @since 1.6.0
 */
export class IOEither<L, A> {
  readonly _A!: A
  readonly _L!: L
  readonly _URI!: URI
  constructor(readonly value: IO<Either<L, A>>) {}
  /**
   * Runs the inner io
   */
  run(): Either<L, A> {
    return this.value.run()
  }
  map<B>(f: (a: A) => B): IOEither<L, B> {
    return new IOEither(T.map(this.value, f))
  }
  ap<B>(fab: IOEither<L, (a: A) => B>): IOEither<L, B> {
    return new IOEither(T.ap(fab.value, this.value))
  }
  /**
   * Flipped version of `ap`
   */
  ap_<B, C>(this: IOEither<L, (b: B) => C>, fb: IOEither<L, B>): IOEither<L, C> {
    return fb.ap(this)
  }
  /**
   * Combine two effectful actions, keeping only the result of the first
   */
  applyFirst<B>(fb: IOEither<L, B>): IOEither<L, A> {
    return fb.ap(this.map(constant))
  }
  /**
   * Combine two effectful actions, keeping only the result of the second
   */
  applySecond<B>(fb: IOEither<L, B>): IOEither<L, B> {
    return fb.ap(this.map(constIdentity as () => (b: B) => B))
  }
  chain<B>(f: (a: A) => IOEither<L, B>): IOEither<L, B> {
    return new IOEither(T.chain(this.value, a => f(a).value))
  }
  fold<R>(left: (l: L) => R, right: (a: A) => R): IO<R> {
    return foldT(left, right, this.value)
  }
  /**
   * Similar to `fold`, but the result is flattened.
   */
  foldIO<R>(left: (l: L) => IO<R>, right: (a: A) => IO<R>): IO<R> {
    return this.value.chain(fa => fa.fold(left, right))
  }
  /**
   * Similar to `fold`, but the result is flattened.
   */
  foldIOEither<M, B>(onLeft: (l: L) => IOEither<M, B>, onRight: (a: A) => IOEither<M, B>): IOEither<M, B> {
    return new IOEither(this.value.chain(e => e.fold(onLeft, onRight).value))
  }
  mapLeft<M>(f: (l: L) => M): IOEither<M, A> {
    return new IOEither(this.value.map(e => e.mapLeft(f)))
  }
  orElse<M>(f: (l: L) => IOEither<M, A>): IOEither<M, A> {
    return new IOEither(this.value.chain(e => e.fold(l => f(l).value, a => T.of(a))))
  }
  alt(fy: IOEither<L, A>): IOEither<L, A> {
    return this.orElse(() => fy)
  }
  bimap<V, B>(f: (l: L) => V, g: (a: A) => B): IOEither<V, B> {
    return new IOEither(this.value.map(e => e.bimap(f, g)))
  }
}

const map = <L, A, B>(fa: IOEither<L, A>, f: (a: A) => B): IOEither<L, B> => {
  return fa.map(f)
}

const of = <L, A>(a: A): IOEither<L, A> => {
  return new IOEither(T.of(a))
}

const ap = <L, A, B>(fab: IOEither<L, (a: A) => B>, fa: IOEither<L, A>): IOEither<L, B> => {
  return fa.ap(fab)
}

const chain = <L, A, B>(fa: IOEither<L, A>, f: (a: A) => IOEither<L, B>): IOEither<L, B> => {
  return fa.chain(f)
}

const alt = <L, A>(fx: IOEither<L, A>, fy: IOEither<L, A>): IOEither<L, A> => {
  return fx.alt(fy)
}

const bimap = <L, V, A, B>(fa: IOEither<L, A>, f: (l: L) => V, g: (a: A) => B): IOEither<V, B> => {
  return fa.bimap(f, g)
}

/**
 * @since 1.6.0
 */
export const right = <L, A>(fa: IO<A>): IOEither<L, A> => {
  return new IOEither(fa.map<Either<L, A>>(eitherRight))
}

/**
 * @since 1.6.0
 */
export const left = <L, A>(fa: IO<L>): IOEither<L, A> => {
  return new IOEither(fa.map<Either<L, A>>(eitherLeft))
}

/**
 * @since 1.6.0
 */
export const fromEither = <L, A>(fa: Either<L, A>): IOEither<L, A> => {
  return new IOEither(io.of(fa))
}

/**
 * @since 1.6.0
 */
export const fromLeft = <L, A>(l: L): IOEither<L, A> => {
  return fromEither(eitherLeft(l))
}

/**
 * Use `tryCatch2v` instead
 *
 * @since 1.6.0
 * @deprecated
 */
export const tryCatch = <A>(f: Lazy<A>, onerror: (reason: unknown) => Error = toError): IOEither<Error, A> => {
  return tryCatch2v(f, onerror)
}

/**
 * @since 1.11.0
 */
export const tryCatch2v = <L, A>(f: Lazy<A>, onerror: (reason: unknown) => L): IOEither<L, A> => {
  return new IOEither(new IO(() => eitherTryCatch2v(f, onerror)))
}

const throwError = fromLeft

/**
 * @since 1.6.0
 */
export const ioEither: Monad2<URI> & Bifunctor2<URI> & Alt2<URI> & MonadThrow2<URI> = {
  URI,
  bimap,
  map,
  of,
  ap,
  chain,
  alt,
  throwError,
  fromEither,
  fromOption: (o, e) => (o.isNone() ? throwError(e) : of(o.value))
}

import { Bounded }  from  './Bounded.ts'
import { Endomorphism, identity, concat }  from  './function.ts'
import {
  fold as foldSemigroup,
  getDictionarySemigroup,
  getDualSemigroup,
  getFunctionSemigroup,
  getJoinSemigroup,
  getMeetSemigroup,
  Semigroup,
  semigroupAll,
  semigroupAny,
  semigroupProduct,
  semigroupString,
  semigroupSum,
  semigroupVoid,
  getStructSemigroup,
  getTupleSemigroup
} from './Semigroup.ts'

/**
 * @since 1.0.0
 */
export interface Monoid<A> extends Semigroup<A> {
  readonly empty: A
}

/**
 * @since 1.0.0
 */
export const fold = <A>(M: Monoid<A>): ((as: Array<A>) => A) => {
  return foldSemigroup(M)(M.empty)
}

/**
 * Given a tuple of monoids returns a monoid for the tuple
 *
 * @example
 * import { getTupleMonoid, monoidString, monoidSum, monoidAll }  from  'fp-ts/lib/Monoid.ts'
 *
 * const M1 = getTupleMonoid(monoidString, monoidSum)
 * assert.deepStrictEqual(M1.concat(['a', 1], ['b', 2]), ['ab', 3])
 *
 * const M2 = getTupleMonoid(monoidString, monoidSum, monoidAll)
 * assert.deepStrictEqual(M2.concat(['a', 1, true], ['b', 2, false]), ['ab', 3, false])
 *
 * @since 1.0.0
 */
export const getTupleMonoid = <T extends Array<Monoid<any>>>(
  ...monoids: T
): Monoid<{ [K in keyof T]: T[K] extends Semigroup<infer A> ? A : never }> => {
  return {
    ...getTupleSemigroup(...monoids),
    empty: monoids.map(m => m.empty)
  } as any
}

/**
 * Use `getTupleMonoid` instead
 * @since 1.0.0
 * @deprecated
 */
export const getProductMonoid = <A, B>(MA: Monoid<A>, MB: Monoid<B>): Monoid<[A, B]> => {
  return getTupleMonoid(MA, MB)
}

/**
 * @since 1.0.0
 */
export const getDualMonoid = <A>(M: Monoid<A>): Monoid<A> => {
  return {
    ...getDualSemigroup(M),
    empty: M.empty
  }
}

/**
 * Boolean monoid under conjunction
 * @since 1.0.0
 */
export const monoidAll: Monoid<boolean> = {
  ...semigroupAll,
  empty: true
}

/**
 * Boolean monoid under disjunction
 * @since 1.0.0
 */
export const monoidAny: Monoid<boolean> = {
  ...semigroupAny,
  empty: false
}

const emptyArray: Array<any> = []

/**
 * @since 1.0.0
 */
export const unsafeMonoidArray: Monoid<Array<any>> = {
  concat,
  empty: emptyArray
}

/**
 * `Monoid` under array concatenation
 *
 * @since 1.0.0
 */
export const getArrayMonoid = <A = never>(): Monoid<Array<A>> => {
  return unsafeMonoidArray
}

const emptyObject = {}

/**
 * Use `Record`'s `getMonoid`
 * @since 1.4.0
 * @deprecated
 */
export function getDictionaryMonoid<K extends string, A>(S: Semigroup<A>): Monoid<Record<K, A>>
export function getDictionaryMonoid<A>(S: Semigroup<A>): Monoid<{ [key: string]: A }>
export function getDictionaryMonoid<A>(S: Semigroup<A>): Monoid<{ [key: string]: A }> {
  return {
    // tslint:disable-next-line: deprecation
    ...getDictionarySemigroup(S),
    empty: emptyObject
  }
}

/**
 * Number monoid under addition
 * @since 1.0.0
 */
export const monoidSum: Monoid<number> = {
  ...semigroupSum,
  empty: 0
}

/**
 * Number monoid under multiplication
 * @since 1.0.0
 */
export const monoidProduct: Monoid<number> = {
  ...semigroupProduct,
  empty: 1
}

/**
 * @since 1.0.0
 */
export const monoidString: Monoid<string> = {
  ...semigroupString,
  empty: ''
}

/**
 * @since 1.0.0
 */
export const monoidVoid: Monoid<void> = {
  ...semigroupVoid,
  empty: undefined
}

/**
 * @since 1.0.0
 */
export const getFunctionMonoid = <M>(M: Monoid<M>) => <A = never>(): Monoid<(a: A) => M> => {
  return {
    ...getFunctionSemigroup(M)<A>(),
    empty: () => M.empty
  }
}

/**
 * @since 1.0.0
 */
export const getEndomorphismMonoid = <A = never>(): Monoid<Endomorphism<A>> => {
  return {
    concat: (x, y) => a => x(y(a)),
    empty: identity
  }
}

/**
 * @since 1.14.0
 */
export const getStructMonoid = <O extends { [key: string]: any }>(
  monoids: { [K in keyof O]: Monoid<O[K]> }
): Monoid<O> => {
  const empty: any = {}
  for (const key of Object.keys(monoids)) {
    empty[key] = monoids[key].empty
  }
  return {
    ...getStructSemigroup<O>(monoids),
    empty
  }
}

/**
 * Use `getStructMonoid` instead
 * @since 1.0.0
 * @deprecated
 */
export const getRecordMonoid = <O extends { [key: string]: any }>(
  monoids: { [K in keyof O]: Monoid<O[K]> }
): Monoid<O> => {
  return getStructMonoid(monoids)
}

/**
 * @since 1.9.0
 */
export const getMeetMonoid = <A>(B: Bounded<A>): Monoid<A> => {
  return {
    ...getMeetSemigroup(B),
    empty: B.top
  }
}

/**
 * @since 1.9.0
 */
export const getJoinMonoid = <A>(B: Bounded<A>): Monoid<A> => {
  return {
    ...getJoinSemigroup(B),
    empty: B.bottom
  }
}

/**
 * @file The `Ord` type class represents types which support comparisons with a _total order_.
 *
 * Instances should satisfy the laws of total orderings:
 *
 * 1. Reflexivity: `S.compare(a, a) <= 0`
 * 2. Antisymmetry: if `S.compare(a, b) <= 0` and `S.compare(b, a) <= 0` then `a <-> b`
 * 3. Transitivity: if `S.compare(a, b) <= 0` and `S.compare(b, c) <= 0` then `S.compare(a, c) <= 0`
 *
 * See [Getting started with fp-ts: Ord](https://dev.to/gcanti/getting-started-with-fp-ts-ord-5f1e)
 */
import { Ordering, semigroupOrdering }  from  './Ordering.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Setoid, setoidBoolean, setoidNumber, setoidString }  from  './Setoid.ts'
import { on }  from  './function.ts'

/**
 * @since 1.0.0
 */
export interface Ord<A> extends Setoid<A> {
  readonly compare: (x: A, y: A) => Ordering
}

/**
 * @since 1.0.0
 */
export const unsafeCompare = (x: any, y: any): Ordering => {
  return x < y ? -1 : x > y ? 1 : 0
}

/**
 * @since 1.0.0
 */
export const ordString: Ord<string> = {
  ...setoidString,
  compare: unsafeCompare
}

/**
 * @since 1.0.0
 */
export const ordNumber: Ord<number> = {
  ...setoidNumber,
  compare: unsafeCompare
}

/**
 * @since 1.0.0
 */
export const ordBoolean: Ord<boolean> = {
  ...setoidBoolean,
  compare: unsafeCompare
}

/**
 * Test whether one value is _strictly less than_ another
 *
 * @since 1.0.0
 */
export const lessThan = <A>(O: Ord<A>) => (x: A, y: A): boolean => {
  return O.compare(x, y) === -1
}

/**
 * Test whether one value is _strictly greater than_ another
 *
 * @since 1.0.0
 */
export const greaterThan = <A>(O: Ord<A>) => (x: A, y: A): boolean => {
  return O.compare(x, y) === 1
}

/**
 * Test whether one value is _non-strictly less than_ another
 *
 * @since 1.0.0
 */
export const lessThanOrEq = <A>(O: Ord<A>) => (x: A, y: A): boolean => {
  return O.compare(x, y) !== 1
}

/**
 * Test whether one value is _non-strictly greater than_ another
 *
 * @since 1.0.0
 */
export const greaterThanOrEq = <A>(O: Ord<A>) => (x: A, y: A): boolean => {
  return O.compare(x, y) !== -1
}

/**
 * Take the minimum of two values. If they are considered equal, the first argument is chosen
 *
 * @since 1.0.0
 */
export const min = <A>(O: Ord<A>) => (x: A, y: A): A => {
  return O.compare(x, y) === 1 ? y : x
}

/**
 * Take the maximum of two values. If they are considered equal, the first argument is chosen
 *
 * @since 1.0.0
 */
export const max = <A>(O: Ord<A>) => (x: A, y: A): A => {
  return O.compare(x, y) === -1 ? y : x
}

/**
 * Clamp a value between a minimum and a maximum
 *
 * @since 1.0.0
 */
export const clamp = <A>(O: Ord<A>): ((low: A, hi: A) => (x: A) => A) => {
  const minO = min(O)
  const maxO = max(O)
  return (low, hi) => x => maxO(minO(x, hi), low)
}

/**
 * Test whether a value is between a minimum and a maximum (inclusive)
 *
 * @since 1.0.0
 */
export const between = <A>(O: Ord<A>): ((low: A, hi: A) => (x: A) => boolean) => {
  const lessThanO = lessThan(O)
  const greaterThanO = greaterThan(O)
  return (low, hi) => x => (lessThanO(x, low) || greaterThanO(x, hi) ? false : true)
}

/**
 * @since 1.0.0
 */
export const fromCompare = <A>(compare: (x: A, y: A) => Ordering): Ord<A> => {
  const optimizedCompare = (x: A, y: A): Ordering => (x === y ? 0 : compare(x, y))
  return {
    equals: (x, y) => optimizedCompare(x, y) === 0,
    compare: optimizedCompare
  }
}

/**
 * @since 1.0.0
 */
export const contramap = <A, B>(f: (b: B) => A, fa: Ord<A>): Ord<B> => {
  return fromCompare(on(fa.compare)(f))
}

/**
 * @since 1.0.0
 */
export const getSemigroup = <A = never>(): Semigroup<Ord<A>> => {
  return {
    concat: (x, y) => fromCompare((a, b) => semigroupOrdering.concat(x.compare(a, b), y.compare(a, b)))
  }
}

/**
 * Given a tuple of `Ord`s returns an `Ord` for the tuple
 *
 * @example
 * import { getTupleOrd, ordString, ordNumber, ordBoolean }  from  'fp-ts/lib/Ord.ts'
 *
 * const O = getTupleOrd(ordString, ordNumber, ordBoolean)
 * assert.strictEqual(O.compare(['a', 1, true], ['b', 2, true]), -1)
 * assert.strictEqual(O.compare(['a', 1, true], ['a', 2, true]), -1)
 * assert.strictEqual(O.compare(['a', 1, true], ['a', 1, false]), 1)
 *
 * @since 1.14.3
 */
export const getTupleOrd = <T extends Array<Ord<any>>>(
  ...ords: T
): Ord<{ [K in keyof T]: T[K] extends Ord<infer A> ? A : never }> => {
  const len = ords.length
  return fromCompare((x, y) => {
    let i = 0
    for (; i < len - 1; i++) {
      const r = ords[i].compare(x[i], y[i])
      if (r !== 0) {
        return r
      }
    }
    return ords[i].compare(x[i], y[i])
  })
}

/**
 * Use `getTupleOrd` instead
 * @since 1.0.0
 * @deprecated
 */
export const getProductOrd = <A, B>(OA: Ord<A>, OB: Ord<B>): Ord<[A, B]> => {
  return getTupleOrd(OA, OB)
}

/**
 * @since 1.3.0
 */
export const getDualOrd = <A>(O: Ord<A>): Ord<A> => {
  return fromCompare((x, y) => O.compare(y, x))
}

/**
 * @since 1.4.0
 */
export const ordDate: Ord<Date> = contramap(date => date.valueOf(), ordNumber)

/**
 * @file Adapted from https://github.com/parsonsmatt/purescript-pair
 */
import { Applicative, Applicative1 }  from  './Applicative.ts'
import { Comonad1 }  from  './Comonad.ts'
import { Foldable2v1 }  from  './Foldable2v.ts'
import { Endomorphism }  from  './function.ts'
import { HKT }  from  './HKT.ts'
import { Monoid }  from  './Monoid.ts'
import { Ord, fromCompare }  from  './Ord.ts'
import { semigroupOrdering }  from  './Ordering.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Setoid, fromEquals }  from  './Setoid.ts'
import { Traversable2v1 }  from  './Traversable2v.ts'
import { Show }  from  './Show.ts'

declare module './HKT.ts'
  interface URI2HKT<A> {
    Pair: Pair<A>
  }
}

export const URI = 'Pair'

export type URI = typeof URI

/**
 * @data
 * @constructor Pair
 * @since 1.0.0
 */
export class Pair<A> {
  readonly _A!: A
  readonly _URI!: URI
  constructor(readonly fst: A, readonly snd: A) {}
  /** Map a function over the first field of a pair */
  first(f: Endomorphism<A>): Pair<A> {
    return new Pair(f(this.fst), this.snd)
  }
  /** Map a function over the second field of a pair */
  second(f: Endomorphism<A>): Pair<A> {
    return new Pair(this.fst, f(this.snd))
  }
  /** Swaps the elements in a pair */
  swap(): Pair<A> {
    return new Pair(this.snd, this.fst)
  }
  map<B>(f: (a: A) => B): Pair<B> {
    return new Pair(f(this.fst), f(this.snd))
  }
  ap<B>(fab: Pair<(a: A) => B>): Pair<B> {
    return new Pair(fab.fst(this.fst), fab.snd(this.snd))
  }
  /**
   * Flipped version of `ap`
   */
  ap_<B, C>(this: Pair<(b: B) => C>, fb: Pair<B>): Pair<C> {
    return fb.ap(this)
  }
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    return f(f(b, this.fst), this.snd)
  }
  extract(): A {
    return this.fst
  }
  extend<B>(f: (fb: Pair<A>) => B): Pair<B> {
    return new Pair(f(this), f(this.swap()))
  }
}

/**
 * @since 1.17.0
 */
export const getShow = <L, A>(S: Show<A>): Show<Pair<A>> => {
  return {
    show: p => `new Pair(${S.show(p.fst)}, ${S.show(p.snd)})`
  }
}

const map = <A, B>(fa: Pair<A>, f: (a: A) => B): Pair<B> => {
  return fa.map(f)
}

const of = <A>(a: A): Pair<A> => {
  return new Pair(a, a)
}

const ap = <A, B>(fab: Pair<(a: A) => B>, fa: Pair<A>): Pair<B> => {
  return fa.ap(fab)
}

const reduce = <A, B>(fa: Pair<A>, b: B, f: (b: B, a: A) => B): B => {
  return fa.reduce(b, f)
}

const foldMap = <M>(M: Monoid<M>) => <A>(fa: Pair<A>, f: (a: A) => M): M => {
  return M.concat(f(fa.fst), f(fa.snd))
}

const foldr = <A, B>(fa: Pair<A>, b: B, f: (a: A, b: B) => B): B => {
  return f(fa.fst, f(fa.snd, b))
}

const extract = <A>(fa: Pair<A>): A => {
  return fa.extract()
}

const extend = <A, B>(fa: Pair<A>, f: (fb: Pair<A>) => B): Pair<B> => {
  return fa.extend(f)
}

/**
 * @since 1.0.0
 */
export const getSetoid = <A>(S: Setoid<A>): Setoid<Pair<A>> => {
  return fromEquals((x, y) => S.equals(x.fst, y.fst) && S.equals(x.snd, y.snd))
}

/**
 * @since 1.0.0
 */
export const getOrd = <A>(O: Ord<A>): Ord<Pair<A>> => {
  return fromCompare((x, y) => semigroupOrdering.concat(O.compare(x.fst, y.fst), O.compare(x.snd, y.snd)))
}

/**
 * @since 1.0.0
 */
export const getSemigroup = <A>(S: Semigroup<A>): Semigroup<Pair<A>> => {
  return {
    concat: (x, y) => new Pair(S.concat(x.fst, y.fst), S.concat(x.snd, y.snd))
  }
}

/**
 * @since 1.0.0
 */
export const getMonoid = <A>(M: Monoid<A>): Monoid<Pair<A>> => {
  return {
    ...getSemigroup(M),
    empty: new Pair(M.empty, M.empty)
  }
}

const traverse = <F>(F: Applicative<F>) => <A, B>(ta: Pair<A>, f: (a: A) => HKT<F, B>): HKT<F, Pair<B>> => {
  return F.ap(F.map(f(ta.fst), (b1: B) => (b2: B) => new Pair(b1, b2)), f(ta.snd))
}

const sequence = <F>(F: Applicative<F>) => <A>(ta: Pair<HKT<F, A>>): HKT<F, Pair<A>> => {
  return F.ap(F.map(ta.fst, (a1: A) => (a2: A) => new Pair(a1, a2)), ta.snd)
}

/**
 * @since 1.0.0
 */
export const pair: Applicative1<URI> & Foldable2v1<URI> & Traversable2v1<URI> & Comonad1<URI> = {
  URI,
  map,
  of,
  ap,
  reduce,
  foldMap,
  foldr,
  traverse,
  sequence,
  extend,
  extract
}

import { Category2 }  from  './Category.ts'
import { identity }  from  './function.ts'
import { Monad2 }  from  './Monad.ts'
import { Profunctor2 }  from  './Profunctor.ts'
import { Strong2 }  from  './Strong.ts'
import { Choice2 }  from  './Choice.ts'
import { Either, left as eitherLeft, right as eitherRight }  from  './Either.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Monoid }  from  './Monoid.ts'

declare module './HKT.ts'
  interface URI2HKT2<L, A> {
    Reader: Reader<L, A>
  }
}

export const URI = 'Reader'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export class Reader<E, A> {
  readonly _A!: A
  readonly _L!: E
  readonly _URI!: URI
  constructor(readonly run: (e: E) => A) {}
  map<B>(f: (a: A) => B): Reader<E, B> {
    return new Reader((e: E) => f(this.run(e)))
  }
  ap<B>(fab: Reader<E, (a: A) => B>): Reader<E, B> {
    return new Reader((e: E) => fab.run(e)(this.run(e)))
  }
  /**
   * Flipped version of `ap`
   */
  ap_<B, C>(this: Reader<E, (b: B) => C>, fb: Reader<E, B>): Reader<E, C> {
    return fb.ap(this)
  }
  chain<B>(f: (a: A) => Reader<E, B>): Reader<E, B> {
    return new Reader((e: E) => f(this.run(e)).run(e))
  }
  /**
   * @since 1.6.1
   */
  local<E2 = E>(f: (e: E2) => E): Reader<E2, A> {
    return new Reader(e => this.run(f(e)))
  }
}

const map = <E, A, B>(fa: Reader<E, A>, f: (a: A) => B): Reader<E, B> => {
  return fa.map(f)
}

const of = <E, A>(a: A): Reader<E, A> => {
  return new Reader(() => a)
}

const ap = <E, A, B>(fab: Reader<E, (a: A) => B>, fa: Reader<E, A>): Reader<E, B> => {
  return fa.ap(fab)
}

const chain = <E, A, B>(fa: Reader<E, A>, f: (a: A) => Reader<E, B>): Reader<E, B> => {
  return fa.chain(f)
}

/**
 * reads the current context
 *
 * @since 1.0.0
 */
export const ask = <E>(): Reader<E, E> => {
  return new Reader(identity)
}

/**
 * Projects a value from the global context in a Reader
 *
 * @since 1.0.0
 */
export const asks = <E, A>(f: (e: E) => A): Reader<E, A> => {
  return new Reader(f)
}

/**
 * changes the value of the local context during the execution of the action `fa`
 *
 * @since 1.0.0
 */
export const local = <E, E2 = E>(f: (e: E2) => E) => <A>(fa: Reader<E, A>): Reader<E2, A> => {
  return fa.local(f)
}

const promap = <A, B, C, D>(fbc: Reader<B, C>, f: (a: A) => B, g: (c: C) => D): Reader<A, D> => {
  return new Reader(a => g(fbc.run(f(a))))
}

const compose = <L, A, B>(ab: Reader<A, B>, la: Reader<L, A>): Reader<L, B> => {
  return new Reader(l => ab.run(la.run(l)))
}

const id = <A>(): Reader<A, A> => {
  return new Reader(identity)
}

const first = <A, B, C>(pab: Reader<A, B>): Reader<[A, C], [B, C]> => {
  return new Reader(([a, c]) => [pab.run(a), c])
}

const second = <A, B, C>(pbc: Reader<B, C>): Reader<[A, B], [A, C]> => {
  return new Reader(([a, b]) => [a, pbc.run(b)])
}

const left = <A, B, C>(pab: Reader<A, B>): Reader<Either<A, C>, Either<B, C>> => {
  return new Reader(e => e.fold<Either<B, C>>(a => eitherLeft(pab.run(a)), eitherRight))
}

const right = <A, B, C>(pbc: Reader<B, C>): Reader<Either<A, B>, Either<A, C>> => {
  return new Reader(e => e.fold<Either<A, C>>(eitherLeft, b => eitherRight(pbc.run(b))))
}

/**
 * @since 1.14.0
 */
export const getSemigroup = <E, A>(S: Semigroup<A>): Semigroup<Reader<E, A>> => {
  return {
    concat: (x, y) => new Reader(e => S.concat(x.run(e), y.run(e)))
  }
}

/**
 * @since 1.14.0
 */
export const getMonoid = <E, A>(M: Monoid<A>): Monoid<Reader<E, A>> => {
  return {
    ...getSemigroup(M),
    empty: of(M.empty)
  }
}

/**
 * @since 1.0.0
 */
export const reader: Monad2<URI> & Profunctor2<URI> & Category2<URI> & Strong2<URI> & Choice2<URI> = {
  URI,
  map,
  of,
  ap,
  chain,
  promap,
  compose,
  id,
  first,
  second,
  left,
  right
}

import { Alt3 }  from  './Alt.ts'
import { Bifunctor3 }  from  './Bifunctor.ts'
import { Either }  from  './Either.ts'
import { constant, constIdentity, Predicate, Refinement }  from  './function.ts'
import { IO }  from  './IO.ts'
import { IOEither }  from  './IOEither.ts'
import { Monad3 }  from  './Monad.ts'
import { MonadIO3 }  from  './MonadIO.ts'
import { Reader }  from  './Reader.ts'
import * as readerT  from  './ReaderT.ts'
import { Task }  from  './Task.ts'
import * as taskEither  from  './TaskEither.ts'
import  from  'TaskEither.ts'
import { MonadTask3 }  from  './MonadTask.ts'
import { MonadThrow3 }  from  './MonadThrow.ts'

const readerTTaskEither = readerT.getReaderT2v(taskEither.taskEither)

declare module './HKT.ts'
  interface URI2HKT3<U, L, A> {
    ReaderTaskEither: ReaderTaskEither<U, L, A>
  }
}

export const URI = 'ReaderTaskEither'

export type URI = typeof URI

/**
 * @since 1.6.0
 */
export class ReaderTaskEither<E, L, A> {
  readonly _A!: A
  readonly _L!: L
  readonly _U!: E
  readonly _URI!: URI
  constructor(readonly value: (e: E) => TaskEither<L, A>) {}
  /** Runs the inner `TaskEither` */
  run(e: E): Promise<Either<L, A>> {
    return this.value(e).run()
  }
  map<B>(f: (a: A) => B): ReaderTaskEither<E, L, B> {
    return new ReaderTaskEither(readerTTaskEither.map(this.value, f))
  }
  ap<B>(fab: ReaderTaskEither<E, L, (a: A) => B>): ReaderTaskEither<E, L, B> {
    return new ReaderTaskEither(readerTTaskEither.ap(fab.value, this.value))
  }
  /**
   * Flipped version of `ap`
   */
  ap_<B, C>(this: ReaderTaskEither<E, L, (b: B) => C>, fb: ReaderTaskEither<E, L, B>): ReaderTaskEither<E, L, C> {
    return fb.ap(this)
  }
  /**
   * Combine two effectful actions, keeping only the result of the first
   */
  applyFirst<B>(fb: ReaderTaskEither<E, L, B>): ReaderTaskEither<E, L, A> {
    return fb.ap(this.map(constant))
  }
  /**
   * Combine two effectful actions, keeping only the result of the second
   */
  applySecond<B>(fb: ReaderTaskEither<E, L, B>): ReaderTaskEither<E, L, B> {
    return fb.ap(this.map(constIdentity as () => (b: B) => B))
  }
  chain<B>(f: (a: A) => ReaderTaskEither<E, L, B>): ReaderTaskEither<E, L, B> {
    return new ReaderTaskEither(readerTTaskEither.chain(this.value, a => f(a).value))
  }
  fold<R>(left: (l: L) => R, right: (a: A) => R): Reader<E, Task<R>> {
    return new Reader(e => this.value(e).fold(left, right))
  }
  mapLeft<M>(f: (l: L) => M): ReaderTaskEither<E, M, A> {
    return new ReaderTaskEither(e => this.value(e).mapLeft(f))
  }
  /**
   * Transforms the failure value of the `ReaderTaskEither` into a new `ReaderTaskEither`
   */
  orElse<M>(f: (l: L) => ReaderTaskEither<E, M, A>): ReaderTaskEither<E, M, A> {
    return new ReaderTaskEither(e => this.value(e).orElse(l => f(l).value(e)))
  }
  alt(fy: ReaderTaskEither<E, L, A>): ReaderTaskEither<E, L, A> {
    return this.orElse(() => fy)
  }
  bimap<V, B>(f: (l: L) => V, g: (a: A) => B): ReaderTaskEither<E, V, B> {
    return new ReaderTaskEither(e => this.value(e).bimap(f, g))
  }
  /**
   * @since 1.6.1
   */
  local<E2 = E>(f: (e: E2) => E): ReaderTaskEither<E2, L, A> {
    return new ReaderTaskEither(e => this.value(f(e)))
  }
}

const map = <E, L, A, B>(fa: ReaderTaskEither<E, L, A>, f: (a: A) => B): ReaderTaskEither<E, L, B> => {
  return fa.map(f)
}

const of = <E, L, A>(a: A): ReaderTaskEither<E, L, A> => {
  return new ReaderTaskEither(readerTTaskEither.of(a))
}

const ap = <E, L, A, B>(
  fab: ReaderTaskEither<E, L, (a: A) => B>,
  fa: ReaderTaskEither<E, L, A>
): ReaderTaskEither<E, L, B> => {
  return fa.ap(fab)
}

const chain = <E, L, A, B>(
  fa: ReaderTaskEither<E, L, A>,
  f: (a: A) => ReaderTaskEither<E, L, B>
): ReaderTaskEither<E, L, B> => {
  return fa.chain(f)
}

const alt = <E, L, A>(fx: ReaderTaskEither<E, L, A>, fy: ReaderTaskEither<E, L, A>): ReaderTaskEither<E, L, A> => {
  return fx.alt(fy)
}

const bimap = <E, L, V, A, B>(
  fa: ReaderTaskEither<E, L, A>,
  f: (l: L) => V,
  g: (a: A) => B
): ReaderTaskEither<E, V, B> => {
  return fa.bimap(f, g)
}

/**
 * @since 1.6.0
 */
export const ask = <E, L>(): ReaderTaskEither<E, L, E> => {
  return new ReaderTaskEither(e => taskEither.taskEither.of(e))
}

/**
 * @since 1.6.0
 */
export const asks = <E, L, A>(f: (e: E) => A): ReaderTaskEither<E, L, A> => {
  return new ReaderTaskEither(e => taskEither.taskEither.of(f(e)))
}

/**
 * @since 1.6.0
 */
export const local = <E, E2 = E>(f: (e: E2) => E) => <L, A>(
  fa: ReaderTaskEither<E, L, A>
): ReaderTaskEither<E2, L, A> => {
  return fa.local(f)
}

/**
 * @since 1.6.0
 */
export const right = <E, L, A>(fa: Task<A>): ReaderTaskEither<E, L, A> => {
  return new ReaderTaskEither(() => taskEither.right(fa))
}

/**
 * @since 1.6.0
 */
export const left = <E, L, A>(fa: Task<L>): ReaderTaskEither<E, L, A> => {
  return new ReaderTaskEither(() => taskEither.left(fa))
}

/**
 * @since 1.6.0
 */
export const fromTaskEither = <E, L, A>(fa: TaskEither<L, A>): ReaderTaskEither<E, L, A> => {
  return new ReaderTaskEither(() => fa)
}

const readerTfromReader = readerT.fromReader(taskEither.taskEither)
/**
 * @since 1.6.0
 */
export const fromReader = <E, L, A>(fa: Reader<E, A>): ReaderTaskEither<E, L, A> => {
  return new ReaderTaskEither(readerTfromReader(fa))
}

/**
 * @since 1.6.0
 */
export const fromEither = <E, L, A>(fa: Either<L, A>): ReaderTaskEither<E, L, A> => {
  return fromTaskEither(taskEither.fromEither(fa))
}

/**
 * @since 1.6.0
 */
export const fromIO = <E, L, A>(fa: IO<A>): ReaderTaskEither<E, L, A> => {
  return fromTaskEither(taskEither.fromIO(fa))
}

/**
 * @since 1.6.0
 */
export const fromLeft = <E, L, A>(l: L): ReaderTaskEither<E, L, A> => {
  return fromTaskEither(taskEither.fromLeft(l))
}

/**
 * @since 1.6.0
 */
export const fromIOEither = <E, L, A>(fa: IOEither<L, A>): ReaderTaskEither<E, L, A> => {
  return fromTaskEither(taskEither.fromIOEither(fa))
}

/**
 * @since 1.6.0
 */
export function fromPredicate<E, L, A, B extends A>(
  predicate: Refinement<A, B>,
  onFalse: (a: A) => L
): (a: A) => ReaderTaskEither<E, L, B>
export function fromPredicate<E, L, A>(
  predicate: Predicate<A>,
  onFalse: (a: A) => L
): (a: A) => ReaderTaskEither<E, L, A>
export function fromPredicate<E, L, A>(
  predicate: Predicate<A>,
  onFalse: (a: A) => L
): (a: A) => ReaderTaskEither<E, L, A> {
  const f = taskEither.fromPredicate(predicate, onFalse)
  return a => fromTaskEither(f(a))
}

/**
 * @since 1.6.0
 */
export const tryCatch = <E, L, A>(
  f: (e: E) => Promise<A>,
  onrejected: (reason: unknown, e: E) => L
): ReaderTaskEither<E, L, A> => {
  return new ReaderTaskEither(e => taskEither.tryCatch(() => f(e), (reason: unknown) => onrejected(reason, e)))
}

const fromTask = right

const throwError = fromLeft

/**
 * @since 1.6.0
 */
export const readerTaskEither: Monad3<URI> &
  Bifunctor3<URI> &
  Alt3<URI> &
  MonadIO3<URI> &
  MonadTask3<URI> &
  MonadThrow3<URI> = {
  URI,
  map,
  of,
  ap,
  chain,
  alt,
  bimap,
  fromIO,
  fromTask,
  throwError,
  fromEither,
  fromOption: (o, e) => (o.isNone() ? throwError(e) : of(o.value))
}

/**
 * Like `readerTaskEither` but `ap` is sequential
 * @since 1.10.0
 */
export const readerTaskEitherSeq: typeof readerTaskEither = {
  ...readerTaskEither,
  ap: (fab, fa) => fab.chain(f => fa.map(f))
}

/**
 * @file See [Getting started with fp-ts: Semigroup](https://dev.to/gcanti/getting-started-with-fp-ts-semigroup-2mf7)
 */
import { Ord, max, min }  from  './Ord.ts'
import { concat, identity }  from  './function.ts'
import { Magma }  from  './Magma.ts'

/**
 * A `Semigroup` is a `Magma` where `concat` is associative, that is:
 *
 * Associativiy: `concat(concat(x, y), z) = concat(x, concat(y, z))`
 *
 * @since 1.0.0
 */
export interface Semigroup<A> extends Magma<A> {}

/**
 * @since 1.0.0
 */
export const fold = <A>(S: Semigroup<A>) => (a: A) => (as: Array<A>): A => {
  return as.reduce(S.concat, a)
}

/**
 * @since 1.0.0
 */
export const getFirstSemigroup = <A = never>(): Semigroup<A> => {
  return { concat: identity }
}

/**
 * @since 1.0.0
 */
export const getLastSemigroup = <A = never>(): Semigroup<A> => {
  return { concat: (_, y) => y }
}

/**
 * Given a tuple of semigroups returns a semigroup for the tuple
 *
 * @example
 * import { getTupleSemigroup, semigroupString, semigroupSum, semigroupAll }  from  'fp-ts/lib/Semigroup.ts'
 *
 * const S1 = getTupleSemigroup(semigroupString, semigroupSum)
 * assert.deepStrictEqual(S1.concat(['a', 1], ['b', 2]), ['ab', 3])
 *
 * const S2 = getTupleSemigroup(semigroupString, semigroupSum, semigroupAll)
 * assert.deepStrictEqual(S2.concat(['a', 1, true], ['b', 2, false]), ['ab', 3, false])
 *
 * @since 1.14.0
 */
export const getTupleSemigroup = <T extends Array<Semigroup<any>>>(
  ...semigroups: T
): Semigroup<{ [K in keyof T]: T[K] extends Semigroup<infer A> ? A : never }> => {
  return {
    concat: (x, y) => semigroups.map((s, i) => s.concat(x[i], y[i])) as any
  }
}

/**
 * Use `getTupleSemigroup` instead
 * @since 1.0.0
 * @deprecated
 */
export const getProductSemigroup = <A, B>(SA: Semigroup<A>, SB: Semigroup<B>): Semigroup<[A, B]> => {
  return getTupleSemigroup(SA, SB)
}

/**
 * @since 1.0.0
 */
export const getDualSemigroup = <A>(S: Semigroup<A>): Semigroup<A> => {
  return {
    concat: (x, y) => S.concat(y, x)
  }
}

/**
 * @since 1.0.0
 */
export const getFunctionSemigroup = <S>(S: Semigroup<S>) => <A = never>(): Semigroup<(a: A) => S> => {
  return {
    concat: (f, g) => a => S.concat(f(a), g(a))
  }
}

/**
 * @since 1.14.0
 */
export const getStructSemigroup = <O extends { [key: string]: any }>(
  semigroups: { [K in keyof O]: Semigroup<O[K]> }
): Semigroup<O> => {
  return {
    concat: (x, y) => {
      const r: any = {}
      for (const key of Object.keys(semigroups)) {
        r[key] = semigroups[key].concat(x[key], y[key])
      }
      return r
    }
  }
}

/**
 * Use `getStructSemigroup` instead
 * @since 1.0.0
 * @deprecated
 */
export const getRecordSemigroup = <O extends { [key: string]: any }>(
  semigroups: { [K in keyof O]: Semigroup<O[K]> }
): Semigroup<O> => {
  return getStructSemigroup(semigroups)
}

/**
 * @since 1.0.0
 */
export const getMeetSemigroup = <A>(O: Ord<A>): Semigroup<A> => {
  return {
    concat: min(O)
  }
}

/**
 * @since 1.0.0
 */
export const getJoinSemigroup = <A>(O: Ord<A>): Semigroup<A> => {
  return {
    concat: max(O)
  }
}

/**
 * Boolean semigroup under conjunction
 * @since 1.0.0
 */
export const semigroupAll: Semigroup<boolean> = {
  concat: (x, y) => x && y
}

/**
 * Boolean semigroup under disjunction
 * @since 1.0.0
 */
export const semigroupAny: Semigroup<boolean> = {
  concat: (x, y) => x || y
}

/**
 * Use `Monoid`'s `getArrayMonoid` instead
 * @since 1.0.0
 * @deprecated
 */
export const getArraySemigroup = <A = never>(): Semigroup<Array<A>> => {
  return { concat }
}

/**
 * Use `Record`'s `getMonoid`
 * @since 1.4.0
 * @deprecated
 */
export function getDictionarySemigroup<K extends string, A>(S: Semigroup<A>): Semigroup<Record<K, A>>
export function getDictionarySemigroup<A>(S: Semigroup<A>): Semigroup<{ [key: string]: A }>
export function getDictionarySemigroup<A>(S: Semigroup<A>): Semigroup<{ [key: string]: A }> {
  return {
    concat: (x, y) => {
      const r: { [key: string]: A } = { ...x }
      const keys = Object.keys(y)
      const len = keys.length
      for (let i = 0; i < len; i++) {
        const k = keys[i]
        r[k] = x.hasOwnProperty(k) ? S.concat(x[k], y[k]) : y[k]
      }
      return r
    }
  }
}

// tslint:disable-next-line: deprecation
const semigroupAnyDictionary = getDictionarySemigroup(getLastSemigroup())

/**
 * Returns a `Semigroup` instance for objects preserving their type
 *
 * @example
 * import { getObjectSemigroup }  from  'fp-ts/lib/Semigroup.ts'
 *
 * interface Person {
 *   name: string
 *   age: number
 * }
 *
 * const S = getObjectSemigroup<Person>()
 * assert.deepStrictEqual(S.concat({ name: 'name', age: 23 }, { name: 'name', age: 24 }), { name: 'name', age: 24 })
 *
 * @since 1.4.0
 */
export const getObjectSemigroup = <A extends object = never>(): Semigroup<A> => {
  return semigroupAnyDictionary as any
}

/**
 * Number `Semigroup` under addition
 * @since 1.0.0
 */
export const semigroupSum: Semigroup<number> = {
  concat: (x, y) => x + y
}

/**
 * Number `Semigroup` under multiplication
 * @since 1.0.0
 */
export const semigroupProduct: Semigroup<number> = {
  concat: (x, y) => x * y
}

/**
 * @since 1.0.0
 */
export const semigroupString: Semigroup<string> = {
  concat: (x, y) => x + y
}

/**
 * @since 1.0.0
 */
export const semigroupVoid: Semigroup<void> = {
  concat: () => undefined
}

/**
 * @file The `Strong` class extends `Profunctor` with combinators for working with product types.
 *
 * `first` and `second` lift values in a `Profunctor` to act on the first and second components of a tuple,
 * respectively.
 *
 * Another way to think about Strong is to piggyback on the intuition of
 * inputs and outputs.  Rewriting the type signature in this light then yields:
 *
 * ```purescript
 * first ::  forall input output a. p input output -> p (Tuple input a) (Tuple output a)
 * second :: forall input output a. p input output -> p (Tuple a input) (Tuple a output)
 * ```
 *
 * If we specialize the profunctor p to the function arrow, we get the following type
 * signatures, which may look a bit more familiar:
 *
 * ```purescript
 * first ::  forall input output a. (input -> output) -> (Tuple input a) -> (Tuple output a)
 * second :: forall input output a. (input -> output) -> (Tuple a input) -> (Tuple a output)
 * ```
 *
 * So, when the `profunctor` is `Function` application, `first` essentially applies your function
 * to the first element of a tuple, and `second` applies it to the second element (same as `map` would do).
 *
 * Adapted from https://github.com/purescript/purescript-profunctor/blob/master/src/Data/Profunctor/Strong.purs
 */
import { Category, Category2, Category3, Category4 }  from  './Category.ts'
import { identity }  from  './function.ts'
import { HKT2, Type2, Type3, URIS2, URIS3, URIS4, Type4 }  from  './HKT.ts'
import { Profunctor, Profunctor2, Profunctor3, Profunctor4 }  from  './Profunctor.ts'

/**
 * @since 1.11.0
 */
export interface Strong<F> extends Profunctor<F> {
  readonly first: <A, B, C>(pab: HKT2<F, A, B>) => HKT2<F, [A, C], [B, C]>
  readonly second: <A, B, C>(pab: HKT2<F, B, C>) => HKT2<F, [A, B], [A, C]>
}

export interface Strong2<F extends URIS2> extends Profunctor2<F> {
  readonly first: <A, B, C>(pab: Type2<F, A, B>) => Type2<F, [A, C], [B, C]>
  readonly second: <A, B, C>(pab: Type2<F, B, C>) => Type2<F, [A, B], [A, C]>
}

export interface Strong3<F extends URIS3> extends Profunctor3<F> {
  readonly first: <U, A, B, C>(pab: Type3<F, U, A, B>) => Type3<F, U, [A, C], [B, C]>
  readonly second: <U, A, B, C>(pab: Type3<F, U, B, C>) => Type3<F, U, [A, B], [A, C]>
}

export interface Strong4<F extends URIS4> extends Profunctor4<F> {
  readonly first: <X, U, A, B, C>(pab: Type4<F, X, U, A, B>) => Type4<F, X, U, [A, C], [B, C]>
  readonly second: <X, U, A, B, C>(pab: Type4<F, X, U, B, C>) => Type4<F, X, U, [A, B], [A, C]>
}

/**
 * Compose a value acting on a tuple from two values, each acting on one of the components of the tuple.
 *
 * Specializing `(***)` to function application would look like this:
 *
 * ```purescript
 * (***) :: forall a b c d. (a -> b) -> (c -> d) -> (Tuple a c) -> (Tuple b d)
 * ```
 *
 * We take two functions, `f` and `g`, and we transform them into a single function which takes a tuple and maps `f`
 * over the first element and `g` over the second.  Just like `bi-map` would do for the `bi-functor` instance of tuple.
 *
 * @since 1.11.0
 */
export function splitStrong<F extends URIS4>(
  F: Category4<F> & Strong4<F>
): <X, U, A, B, C, D>(pab: Type4<F, X, U, A, B>, pcd: Type4<F, X, U, C, D>) => Type4<F, X, U, [A, C], [B, D]>
export function splitStrong<F extends URIS3>(
  F: Category3<F> & Strong3<F>
): <U, A, B, C, D>(pab: Type3<F, U, A, B>, pcd: Type3<F, U, C, D>) => Type3<F, U, [A, C], [B, D]>
export function splitStrong<F extends URIS2>(
  F: Category2<F> & Strong2<F>
): <A, B, C, D>(pab: Type2<F, A, B>, pcd: Type2<F, C, D>) => Type2<F, [A, C], [B, D]>
export function splitStrong<F>(
  F: Category<F> & Strong<F>
): <A, B, C, D>(pab: HKT2<F, A, B>, pcd: HKT2<F, C, D>) => HKT2<F, [A, C], [B, D]>
export function splitStrong<F>(
  F: Category<F> & Strong<F>
): <A, B, C, D>(pab: HKT2<F, A, B>, pcd: HKT2<F, C, D>) => HKT2<F, [A, C], [B, D]> {
  return (pab, pcd) =>
    F.compose(
      F.first(pab),
      F.second(pcd)
    )
}

/**
 * Compose a value which introduces a tuple from two values, each introducing one side of the tuple.
 *
 * This combinator is useful when assembling values from smaller components, because it provides a way to support two
 * different types of output.
 *
 * Specializing `(&&&)` to function application would look like this:
 *
 * ```purescript
 * (&&&) :: forall a b c. (a -> b) -> (a -> c) -> (a -> (Tuple b c))
 * ```
 *
 * We take two functions, `f` and `g`, with the same parameter type and we transform them into a single function which
 * takes one parameter and returns a tuple of the results of running `f` and `g` on the parameter, respectively.  This
 * allows us to run two parallel computations on the same input and return both results in a tuple.
 *
 * @since 1.11.0
 */
export function fanout<F extends URIS4>(
  F: Category4<F> & Strong4<F>
): <X, U, A, B, C>(pab: Type4<F, X, U, A, B>, pac: Type4<F, X, U, A, C>) => Type4<F, X, U, A, [B, C]>
export function fanout<F extends URIS3>(
  F: Category3<F> & Strong3<F>
): <U, A, B, C>(pab: Type3<F, U, A, B>, pac: Type3<F, U, A, C>) => Type3<F, U, A, [B, C]>
export function fanout<F extends URIS2>(
  F: Category2<F> & Strong2<F>
): <A, B, C>(pab: Type2<F, A, B>, pac: Type2<F, A, C>) => Type2<F, A, [B, C]>
export function fanout<F>(
  F: Category<F> & Strong<F>
): <A, B, C>(pab: HKT2<F, A, B>, pac: HKT2<F, A, C>) => HKT2<F, A, [B, C]>
export function fanout<F>(
  F: Category<F> & Strong<F>
): <A, B, C>(pab: HKT2<F, A, B>, pac: HKT2<F, A, C>) => HKT2<F, A, [B, C]> {
  const splitStrongF = splitStrong(F)
  return <A, B, C>(pab: HKT2<F, A, B>, pac: HKT2<F, A, C>): HKT2<F, A, [B, C]> => {
    const split: HKT2<F, A, [A, A]> = F.promap(F.id<A>(), identity, a => [a, a])
    return F.compose(
      splitStrongF(pab, pac),
      split
    )
  }
}

/**
 * @file `Task<A>` represents an asynchronous computation that yields a value of type `A` and **never fails**.
 * If you want to represent an asynchronous computation that may fail, please see `TaskEither`.
 */
import { Either, left, right }  from  './Either.ts'
import { constant, constIdentity, identity, Lazy, toString }  from  './function.ts'
import { IO }  from  './IO.ts'
import { Monad1 }  from  './Monad.ts'
import { MonadIO1 }  from  './MonadIO.ts'
import { MonadTask1 }  from  './MonadTask.ts'
import { Monoid }  from  './Monoid.ts'
import { Semigroup }  from  './Semigroup.ts'

declare module './HKT.ts'
  interface URI2HKT<A> {
    Task: Task<A>
  }
}

export const URI = 'Task'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export class Task<A> {
  readonly _A!: A
  readonly _URI!: URI
  constructor(readonly run: Lazy<Promise<A>>) {}
  map<B>(f: (a: A) => B): Task<B> {
    return new Task(() => this.run().then(f))
  }
  ap<B>(fab: Task<(a: A) => B>): Task<B> {
    return new Task(() => Promise.all([fab.run(), this.run()]).then(([f, a]) => f(a)))
  }
  /**
   * Flipped version of `ap`
   */
  ap_<B, C>(this: Task<(b: B) => C>, fb: Task<B>): Task<C> {
    return fb.ap(this)
  }
  /**
   * Combine two effectful actions, keeping only the result of the first
   * @since 1.6.0
   */
  applyFirst<B>(fb: Task<B>): Task<A> {
    return fb.ap(this.map(constant))
  }
  /**
   * Combine two effectful actions, keeping only the result of the second
   * @since 1.5.0
   */
  applySecond<B>(fb: Task<B>): Task<B> {
    return fb.ap(this.map(constIdentity as () => (b: B) => B))
  }
  chain<B>(f: (a: A) => Task<B>): Task<B> {
    return new Task(() => this.run().then(a => f(a).run()))
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `new Task(${toString(this.run)})`
  }
}

const map = <A, B>(fa: Task<A>, f: (a: A) => B): Task<B> => {
  return fa.map(f)
}

const of = <A>(a: A): Task<A> => {
  return new Task(() => Promise.resolve(a))
}

const ap = <A, B>(fab: Task<(a: A) => B>, fa: Task<A>): Task<B> => {
  return fa.ap(fab)
}

const chain = <A, B>(fa: Task<A>, f: (a: A) => Task<B>): Task<B> => {
  return fa.chain(f)
}

/**
 * @since 1.0.0
 */
export const getRaceMonoid = <A = never>(): Monoid<Task<A>> => {
  return {
    concat: (x, y) =>
      new Task(
        () =>
          new Promise((resolve, reject) => {
            let running = true
            const resolveFirst = (a: A) => {
              if (running) {
                running = false
                resolve(a)
              }
            }
            const rejectFirst = (e: any) => {
              if (running) {
                running = false
                reject(e)
              }
            }
            x.run().then(resolveFirst, rejectFirst)
            y.run().then(resolveFirst, rejectFirst)
          })
      ),
    empty: never
  }
}

const never = new Task(() => new Promise<never>(_ => undefined))

/**
 * @since 1.0.0
 */
export const getSemigroup = <A>(S: Semigroup<A>): Semigroup<Task<A>> => {
  return {
    concat: (x, y) => new Task(() => x.run().then(rx => y.run().then(ry => S.concat(rx, ry))))
  }
}

/**
 * @since 1.0.0
 */
export const getMonoid = <A>(M: Monoid<A>): Monoid<Task<A>> => {
  return {
    ...getSemigroup(M),
    empty: of(M.empty)
  }
}

/**
 * @since 1.0.0
 */
export const tryCatch = <L, A>(f: Lazy<Promise<A>>, onrejected: (reason: unknown) => L): Task<Either<L, A>> => {
  return new Task(() => f().then<Either<L, A>, Either<L, A>>(right, reason => left(onrejected(reason))))
}

/**
 * Lifts an IO action into a Task
 *
 * @since 1.0.0
 */
export const fromIO = <A>(io: IO<A>): Task<A> => {
  return new Task(() => Promise.resolve(io.run()))
}

/**
 * @since 1.7.0
 */
export const delay = <A>(millis: number, a: A): Task<A> => {
  return new Task(
    () =>
      new Promise(resolve => {
        setTimeout(() => {
          resolve(a)
        }, millis)
      })
  )
}

const fromTask = identity

/**
 * @since 1.0.0
 */
export const task: Monad1<URI> & MonadIO1<URI> & MonadTask1<URI> = {
  URI,
  map,
  of,
  ap,
  chain,
  fromIO,
  fromTask
}

/**
 * Like `Task` but `ap` is sequential
 *
 * @since 1.10.0
 */
export const taskSeq: typeof task = {
  ...task,
  ap: (fab, fa) => fab.chain(f => fa.map(f))
}

/**
 * @file A `Traversable` with an additional index.
 * A `TraversableWithIndex` instance must be compatible with its `Traversable` instance
 *
 * ```ts
 * traverse(F)(ta, f) = traverseWithIndex(F)(ta, (_, a) => f(a))
 * ```
 *
 * with its `FoldableWithIndex` instance
 *
 * ```ts
 * foldMapWithIndex(M)(ta, f) = traverseWithIndex(getApplicative(M))(ta, (i, a) => new Const(f(i, a))).value
 * ```
 *
 * and with its `FunctorWithIndex` instance
 *
 * ```purescript
 * mapWithIndex(ta, f) = traverseWithIndex(identity)(ta, (i, a) => new Identity(f(i, a))).value
 * ```
 */
import { Applicative, Applicative1, Applicative2, Applicative2C, Applicative3, Applicative3C }  from  './Applicative.ts'
import { FoldableWithIndex, FoldableWithIndex1, FoldableWithIndex2, FoldableWithIndex2C }  from  './FoldableWithIndex.ts'
import { FunctorWithIndex, FunctorWithIndex1, FunctorWithIndex2, FunctorWithIndex2C }  from  './FunctorWithIndex.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Traversable2v, Traversable2v1, Traversable2v2, Traversable2v2C }  from  './Traversable2v.ts'

/**
 * @since 1.12.0
 */
export interface TraversableWithIndex<T, I> extends FunctorWithIndex<T, I>, FoldableWithIndex<T, I>, Traversable2v<T> {
  readonly traverseWithIndex: TraverseWithIndex<T, I>
}

export interface TraversableWithIndex1<T extends URIS, I>
  extends FunctorWithIndex1<T, I>,
    FoldableWithIndex1<T, I>,
    Traversable2v1<T> {
  readonly traverseWithIndex: TraverseWithIndex1<T, I>
}

export interface TraversableWithIndex2<T extends URIS2, I>
  extends FunctorWithIndex2<T, I>,
    FoldableWithIndex2<T, I>,
    Traversable2v2<T> {
  readonly traverseWithIndex: TraverseWithIndex2<T, I>
}

export interface TraversableWithIndex2C<T extends URIS2, I, L>
  extends FunctorWithIndex2C<T, I, L>,
    FoldableWithIndex2C<T, I, L>,
    Traversable2v2C<T, L> {
  readonly traverseWithIndex: TraverseWithIndex2C<T, I, L>
}

export interface TraverseWithIndex<T, I> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A, B>(
    ta: HKT<T, A>,
    f: (i: I, a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, HKT<T, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: HKT<T, A>,
    f: (i: I, a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, HKT<T, B>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A, B>(
    ta: HKT<T, A>,
    f: (i: I, a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, HKT<T, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A, B>(
    ta: HKT<T, A>,
    f: (i: I, a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, HKT<T, B>>
  <F extends URIS>(F: Applicative1<F>): <A, B>(ta: HKT<T, A>, f: (i: I, a: A) => Type<F, B>) => Type<F, HKT<T, B>>
  <F>(F: Applicative<F>): <A, B>(ta: HKT<T, A>, f: (i: I, a: A) => HKT<F, B>) => HKT<F, HKT<T, B>>
}

export interface TraverseWithIndex1<T extends URIS, I> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A, B>(
    ta: Type<T, A>,
    f: (i: I, a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type<T, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: Type<T, A>,
    f: (i: I, a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type<T, B>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A, B>(
    ta: Type<T, A>,
    f: (i: I, a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type<T, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A, B>(
    ta: Type<T, A>,
    f: (i: I, a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type<T, B>>
  <F extends URIS>(F: Applicative1<F>): <A, B>(ta: Type<T, A>, f: (i: I, a: A) => Type<F, B>) => Type<F, Type<T, B>>
  <F>(F: Applicative<F>): <A, B>(ta: Type<T, A>, f: (i: I, a: A) => HKT<F, B>) => HKT<F, Type<T, B>>
}

export interface TraverseWithIndex2<T extends URIS2, I> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A, B>(
    ta: Type2<T, FL, A>,
    f: (i: I, a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type2<T, FL, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: Type2<T, FL, A>,
    f: (i: I, a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type2<T, FL, B>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A, B>(
    ta: Type2<T, FL, A>,
    f: (i: I, a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type2<T, FL, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A, B>(
    ta: Type2<T, FL, A>,
    f: (i: I, a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type2<T, FL, B>>
  <F extends URIS>(F: Applicative1<F>): <FL, A, B>(
    ta: Type2<T, FL, A>,
    f: (i: I, a: A) => Type<F, B>
  ) => Type<F, Type2<T, FL, B>>
  <F>(F: Applicative<F>): <FL, A, B>(ta: Type2<T, FL, A>, f: (i: I, a: A) => HKT<F, B>) => HKT<F, Type2<T, FL, B>>
}

export interface TraverseWithIndex2C<T extends URIS2, I, FL> {
  <F extends URIS3>(F: Applicative3<F>): <FU, A, B>(
    ta: Type2<T, FL, A>,
    f: (i: I, a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type2<T, FL, B>>
  <F extends URIS3, FU>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: Type2<T, FL, A>,
    f: (i: I, a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type2<T, FL, B>>
  <F extends URIS2>(F: Applicative2<F>): <A, B>(
    ta: Type2<T, FL, A>,
    f: (i: I, a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type2<T, FL, B>>
  <F extends URIS2>(F: Applicative2C<F, FL>): <A, B>(
    ta: Type2<T, FL, A>,
    f: (i: I, a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type2<T, FL, B>>
  <F extends URIS>(F: Applicative1<F>): <A, B>(
    ta: Type2<T, FL, A>,
    f: (i: I, a: A) => Type<F, B>
  ) => Type<F, Type2<T, FL, B>>
  <F>(F: Applicative<F>): <A, B>(ta: Type2<T, FL, A>, f: (i: I, a: A) => HKT<F, B>) => HKT<F, Type2<T, FL, B>>
}

/**
 * @file Adapted from https://github.com/purescript/purescript-tuples
 */
import { Applicative, Applicative2C }  from  './Applicative.ts'
import { Apply2C }  from  './Apply.ts'
import { Bifunctor2 }  from  './Bifunctor.ts'
import { Chain2C }  from  './Chain.ts'
import { ChainRec2C }  from  './ChainRec.ts'
import { Comonad2 }  from  './Comonad.ts'
import { Either }  from  './Either.ts'
import { Foldable2v2 }  from  './Foldable2v.ts'
import { phantom, toString }  from  './function.ts'
import { HKT }  from  './HKT.ts'
import { Monad2C }  from  './Monad.ts'
import { Monoid }  from  './Monoid.ts'
import { contramap as contramapOrd, getSemigroup as getOrdSemigroup, Ord }  from  './Ord.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Semigroupoid2 }  from  './Semigroupoid.ts'
import { Setoid, fromEquals }  from  './Setoid.ts'
import { Traversable2v2 }  from  './Traversable2v.ts'
import { Show }  from  './Show.ts'

declare module './HKT.ts'
  interface URI2HKT2<L, A> {
    Tuple: Tuple<L, A>
  }
}

export const URI = 'Tuple'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export class Tuple<L, A> {
  readonly _A!: A
  readonly _L!: L
  readonly _URI!: URI
  constructor(readonly fst: L, readonly snd: A) {}
  compose<B>(ab: Tuple<A, B>): Tuple<L, B> {
    return new Tuple(this.fst, ab.snd)
  }
  map<B>(f: (a: A) => B): Tuple<L, B> {
    return new Tuple(this.fst, f(this.snd))
  }
  bimap<M, B>(f: (l: L) => M, g: (a: A) => B): Tuple<M, B> {
    return new Tuple(f(this.fst), g(this.snd))
  }
  extract(): A {
    return this.snd
  }
  extend<B>(f: (fa: Tuple<L, A>) => B): Tuple<L, B> {
    return new Tuple(this.fst, f(this))
  }
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    return f(b, this.snd)
  }
  /** Exchange the first and second components of a tuple */
  swap(): Tuple<A, L> {
    return new Tuple(this.snd, this.fst)
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `new Tuple(${toString(this.fst)}, ${toString(this.snd)})`
  }
  toTuple(): [L, A] {
    return [this.fst, this.snd]
  }
}

/**
 * @since 1.17.0
 */
export const getShow = <L, A>(SL: Show<L>, SA: Show<A>): Show<Tuple<L, A>> => {
  return {
    show: t => `new Tuple(${SL.show(t.fst)}, ${SA.show(t.snd)})`
  }
}

const fst = <L, A>(fa: Tuple<L, A>): L => {
  return fa.fst
}

const snd = <L, A>(fa: Tuple<L, A>): A => {
  return fa.snd
}

const compose = <L, A, B>(bc: Tuple<A, B>, fa: Tuple<L, A>): Tuple<L, B> => {
  return fa.compose(bc)
}

const map = <L, A, B>(fa: Tuple<L, A>, f: (a: A) => B): Tuple<L, B> => {
  return fa.map(f)
}

const bimap = <L, A, M, B>(fla: Tuple<L, A>, f: (l: L) => M, g: (a: A) => B): Tuple<M, B> => {
  return fla.bimap(f, g)
}

const extract = snd

const extend = <L, A, B>(fa: Tuple<L, A>, f: (fa: Tuple<L, A>) => B): Tuple<L, B> => {
  return fa.extend(f)
}

const reduce = <L, A, B>(fa: Tuple<L, A>, b: B, f: (b: B, a: A) => B): B => {
  return fa.reduce(b, f)
}

const foldMap = <M>(M: Monoid<M>) => <L, A>(fa: Tuple<L, A>, f: (a: A) => M): M => {
  return f(fa.snd)
}

const foldr = <L, A, B>(fa: Tuple<L, A>, b: B, f: (a: A, b: B) => B): B => {
  return f(fa.snd, b)
}

/**
 * @since 1.0.0
 */
export const getSetoid = <L, A>(SA: Setoid<L>, SB: Setoid<A>): Setoid<Tuple<L, A>> => {
  return fromEquals((x, y) => SA.equals(x.fst, y.fst) && SB.equals(x.snd, y.snd))
}
/**
 * To obtain the result, the `fst`s are `compare`d, and if they are `EQ`ual, the
 * `snd`s are `compare`d.
 *
 * @since 1.0.0
 */
export const getOrd = <L, A>(OL: Ord<L>, OA: Ord<A>): Ord<Tuple<L, A>> => {
  return getOrdSemigroup<Tuple<L, A>>().concat(contramapOrd(fst, OL), contramapOrd(snd, OA))
}

/**
 * @since 1.0.0
 */
export const getSemigroup = <L, A>(SL: Semigroup<L>, SA: Semigroup<A>): Semigroup<Tuple<L, A>> => {
  return {
    concat: (x, y) => new Tuple(SL.concat(x.fst, y.fst), SA.concat(x.snd, y.snd))
  }
}

/**
 * @since 1.0.0
 */
export const getMonoid = <L, A>(ML: Monoid<L>, MA: Monoid<A>): Monoid<Tuple<L, A>> => {
  return {
    ...getSemigroup(ML, MA),
    empty: new Tuple(ML.empty, MA.empty)
  }
}

const ap = <L>(S: Semigroup<L>) => <A, B>(fab: Tuple<L, (a: A) => B>, fa: Tuple<L, A>): Tuple<L, B> => {
  return new Tuple(S.concat(fab.fst, fa.fst), fab.snd(fa.snd))
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

const of = <L>(M: Monoid<L>) => <A>(a: A): Tuple<L, A> => {
  return new Tuple(M.empty, a)
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

const chain = <L>(S: Semigroup<L>) => <A, B>(fa: Tuple<L, A>, f: (b: A) => Tuple<L, B>): Tuple<L, B> => {
  const { fst, snd } = f(fa.snd)
  return new Tuple(S.concat(fa.fst, fst), snd)
}

/**
 * @since 1.0.0
 */
export const getChain = <L>(S: Semigroup<L>): Chain2C<URI, L> => {
  return {
    ...getApply(S),
    chain: chain(S)
  }
}

/**
 * @since 1.0.0
 */
export const getMonad = <L>(M: Monoid<L>): Monad2C<URI, L> => {
  return {
    ...getChain(M),
    of: of(M)
  }
}

const chainRec = <L>(M: Monoid<L>) => <A, B>(a: A, f: (a: A) => Tuple<L, Either<A, B>>): Tuple<L, B> => {
  let result = f(a)
  let acc = M.empty
  while (result.snd.isLeft()) {
    acc = M.concat(acc, result.fst)
    result = f(result.snd.value)
  }
  return new Tuple(M.concat(acc, result.fst), result.snd.value)
}

/**
 * @since 1.0.0
 */
export const getChainRec = <L>(M: Monoid<L>): ChainRec2C<URI, L> => {
  return {
    ...getChain(M),
    chainRec: chainRec(M)
  }
}

const traverse = <F>(F: Applicative<F>) => <L, A, B>(ta: Tuple<L, A>, f: (a: A) => HKT<F, B>): HKT<F, Tuple<L, B>> => {
  return F.map(f(ta.snd), b => new Tuple(ta.fst, b))
}

const sequence = <F>(F: Applicative<F>) => <L, A>(ta: Tuple<L, HKT<F, A>>): HKT<F, Tuple<L, A>> => {
  return F.map(ta.snd, b => new Tuple(ta.fst, b))
}

/**
 * @since 1.0.0
 */
export const tuple: Semigroupoid2<URI> & Bifunctor2<URI> & Comonad2<URI> & Foldable2v2<URI> & Traversable2v2<URI> = {
  URI,
  compose,
  map,
  bimap,
  extract,
  extend,
  reduce,
  foldMap,
  foldr,
  traverse,
  sequence
}

/**
 * @file This class identifies data structures which can be _unfolded_, generalizing `unfoldr` on arrays.
 */
import { Applicative, Applicative1, Applicative2, Applicative2C, Applicative3, Applicative3C }  from  './Applicative.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Option, none, option }  from  './Option.ts'
import { Traversable, Traversable1, sequence }  from  './Traversable.ts'

/**
 * @since 1.0.0
 */
export interface Unfoldable<F> {
  readonly URI: F
  readonly unfoldr: <A, B>(b: B, f: (b: B) => Option<[A, B]>) => HKT<F, A>
}

export interface Unfoldable1<F extends URIS> {
  readonly URI: F
  readonly unfoldr: <A, B>(b: B, f: (b: B) => Option<[A, B]>) => Type<F, A>
}

export interface Unfoldable2<F extends URIS2> {
  readonly URI: F
  readonly unfoldr: <L, A, B>(b: B, f: (b: B) => Option<[A, B]>) => Type2<F, L, A>
}

export interface Unfoldable3<F extends URIS3> {
  readonly URI: F
  readonly unfoldr: <U, L, A, B>(b: B, f: (b: B) => Option<[A, B]>) => Type3<F, U, L, A>
}

export interface Unfoldable2C<F extends URIS2, L> {
  readonly URI: F
  readonly _L: L
  readonly unfoldr: <A, B>(b: B, f: (b: B) => Option<[A, B]>) => Type2<F, L, A>
}

export interface Unfoldable3C<F extends URIS3, U, L> {
  readonly URI: F
  readonly _L: L
  readonly _U: U
  readonly unfoldr: <A, B>(b: B, f: (b: B) => Option<[A, B]>) => Type3<F, U, L, A>
}

/**
 * Replicate a value some natural number of times.
 *
 * @example
 * import { replicate }  from  'fp-ts/lib/Unfoldable.ts'
 * import { array }  from  'fp-ts/lib/Array.ts'
 *
 * assert.deepStrictEqual(replicate(array)('s', 2), ['s', 's'])
 *
 * @since 1.0.0
 */
export function replicate<F extends URIS3>(U: Unfoldable3<F>): <U, L, A>(a: A, n: number) => Type3<F, U, L, A>
export function replicate<F extends URIS3, U, L>(U: Unfoldable3C<F, U, L>): <A>(a: A, n: number) => Type3<F, U, L, A>
export function replicate<F extends URIS2>(U: Unfoldable2<F>): <L, A>(a: A, n: number) => Type2<F, L, A>
export function replicate<F extends URIS2, L>(U: Unfoldable2C<F, L>): <A>(a: A, n: number) => Type2<F, L, A>
export function replicate<F extends URIS>(U: Unfoldable1<F>): <A>(a: A, n: number) => Type<F, A>
export function replicate<F>(U: Unfoldable<F>): <A>(a: A, n: number) => HKT<F, A>
export function replicate<F>(U: Unfoldable<F>): <A>(a: A, n: number) => HKT<F, A> {
  return <A>(a: A, n: number) => {
    function step(n: number): Option<[A, number]> {
      return n <= 0 ? none : option.of([a, n - 1])
    }
    return U.unfoldr(n, step)
  }
}

/**
 * The container with no elements - unfolded with zero iterations.
 *
 * @example
 * import { empty }  from  'fp-ts/lib/Unfoldable.ts'
 * import { array }  from  'fp-ts/lib/Array.ts'
 *
 * assert.deepStrictEqual(empty(array), [])
 *
 * @since 1.0.0
 */
export function empty<F extends URIS3, U, L, A>(U: Unfoldable3<F> | Unfoldable3C<F, U, L>): Type3<F, U, L, A>
export function empty<F extends URIS2, L, A>(U: Unfoldable2<F> | Unfoldable2C<F, L>): Type2<F, L, A>
export function empty<F extends URIS, A>(U: Unfoldable1<F>): Type<F, A>
export function empty<F, A>(U: Unfoldable<F>): HKT<F, A>
export function empty<F, A>(U: Unfoldable<F>): HKT<F, A> {
  return U.unfoldr(undefined, () => none)
}

/**
 * Contain a single value
 *
 * @example
 * import { singleton }  from  'fp-ts/lib/Unfoldable.ts'
 * import { array }  from  'fp-ts/lib/Array.ts'
 *
 * assert.deepStrictEqual(singleton(array)(1), [1])
 *
 * @since 1.0.0
 */
export function singleton<F extends URIS3>(U: Unfoldable3<F>): <U, L, A>(a: A) => Type3<F, U, L, A>
export function singleton<F extends URIS3, U, L>(U: Unfoldable3C<F, U, L>): <A>(a: A) => Type3<F, U, L, A>
export function singleton<F extends URIS2>(U: Unfoldable2<F>): <L, A>(a: A) => Type2<F, L, A>
export function singleton<F extends URIS2, L>(U: Unfoldable2C<F, L>): <A>(a: A) => Type2<F, L, A>
export function singleton<F extends URIS>(U: Unfoldable1<F>): <A>(a: A) => Type<F, A>
export function singleton<F>(U: Unfoldable<F>): <A>(a: A) => HKT<F, A>
export function singleton<F>(U: Unfoldable<F>): <A>(a: A) => HKT<F, A> {
  const replicateU = replicate(U)
  return a => replicateU(a, 1)
}

/**
 * Perform an Applicative action `n` times, and accumulate all the results
 *
 * @example
 * import { replicateA }  from  'fp-ts/lib/Unfoldable.ts'
 * import { array }  from  'fp-ts/lib/Array.ts'
 * import { option, some, none }  from  'fp-ts/lib/Option.ts'
 *
 * assert.deepStrictEqual(replicateA(option, array)(2, some(1)), some([1, 1]))
 * assert.deepStrictEqual(replicateA(option, array)(2, none), none)
 *
 * @since 1.0.0
 */
export function replicateA<F extends URIS3, T extends URIS>(
  A: Applicative3<F>,
  UT: Unfoldable1<T> & Traversable1<T>
): <U, L, A>(n: number, ma: Type3<F, U, L, A>) => Type3<F, U, L, Type<T, A>>
export function replicateA<F extends URIS3, T extends URIS, U, L>(
  A: Applicative3C<F, U, L>,
  UT: Unfoldable1<T> & Traversable1<T>
): <A>(n: number, ma: Type3<F, U, L, A>) => Type3<F, U, L, Type<T, A>>
export function replicateA<F extends URIS2, T extends URIS>(
  A: Applicative2<F>,
  UT: Unfoldable1<T> & Traversable1<T>
): <L, A>(n: number, ma: Type2<F, L, A>) => Type2<F, L, Type<T, A>>
export function replicateA<F extends URIS2, T extends URIS, L>(
  A: Applicative2C<F, L>,
  UT: Unfoldable1<T> & Traversable1<T>
): <A>(n: number, ma: Type2<F, L, A>) => Type2<F, L, Type<T, A>>
export function replicateA<F extends URIS, T extends URIS>(
  F: Applicative1<F>,
  UT: Unfoldable1<T> & Traversable1<T>
): <A>(n: number, ma: Type<F, A>) => Type<F, Type<T, A>>
export function replicateA<F, T>(
  F: Applicative<F>,
  // tslint:disable-next-line: deprecation
  UT: Unfoldable<T> & Traversable<T>
): <A>(n: number, ma: HKT<F, A>) => HKT<F, HKT<T, A>> {
  const sequenceFUT = sequence(F, UT)
  const replicateUT = replicate(UT)
  return (n, ma) => sequenceFUT(replicateUT(ma, n))
}

/**
 * @file The `Applicative` type class extends the `Apply` type class with a `of` function, which can be used to create values
 * of type `f a` from values of type `a`.
 *
 * Where `Apply` provides the ability to lift functions of two or more arguments to functions whose arguments are
 * wrapped using `f`, and `Functor` provides the ability to lift functions of one argument, `pure` can be seen as the
 * function which lifts functions of _zero_ arguments. That is, `Applicative` functors support a lifting operation for
 * any number of function arguments.
 *
 * Instances must satisfy the following laws in addition to the `Apply` laws:
 *
 * 1. Identity: `A.ap(A.of(a => a), fa) = fa`
 * 2. Homomorphism: `A.ap(A.of(ab), A.of(a)) = A.of(ab(a))`
 * 3. Interchange: `A.ap(fab, A.of(a)) = A.ap(A.of(ab => ab(a)), fab)`
 *
 * Note. `Functor`'s `map` can be derived: `A.map(x, f) = A.ap(A.of(f), x)`
 */
import { Apply, Apply1, Apply2, Apply2C, Apply3, Apply3C, getSemigroup }  from  './Apply.ts'
import {
  FunctorComposition,
  FunctorComposition11,
  FunctorComposition12,
  FunctorComposition12C,
  FunctorComposition21,
  FunctorComposition22,
  FunctorComposition22C,
  FunctorComposition2C1,
  FunctorComposition3C1,
  getFunctorComposition
} from './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monoid }  from  './Monoid.ts'

/**
 * @since 1.0.0
 */
export interface Applicative<F> extends Apply<F> {
  readonly of: <A>(a: A) => HKT<F, A>
}

export interface Applicative1<F extends URIS> extends Apply1<F> {
  readonly of: <A>(a: A) => Type<F, A>
}

export interface Applicative2<F extends URIS2> extends Apply2<F> {
  readonly of: <L, A>(a: A) => Type2<F, L, A>
}

export interface Applicative3<F extends URIS3> extends Apply3<F> {
  readonly of: <U, L, A>(a: A) => Type3<F, U, L, A>
}

export interface Applicative2C<F extends URIS2, L> extends Apply2C<F, L> {
  readonly of: <A>(a: A) => Type2<F, L, A>
}

export interface Applicative3C<F extends URIS3, U, L> extends Apply3C<F, U, L> {
  readonly of: <A>(a: A) => Type3<F, U, L, A>
}

export interface ApplicativeComposition<F, G> extends FunctorComposition<F, G> {
  readonly of: <A>(a: A) => HKT<F, HKT<G, A>>
  readonly ap: <A, B>(fgab: HKT<F, HKT<G, (a: A) => B>>, fga: HKT<F, HKT<G, A>>) => HKT<F, HKT<G, B>>
}

export interface ApplicativeComposition11<F extends URIS, G extends URIS> extends FunctorComposition11<F, G> {
  readonly of: <A>(a: A) => Type<F, Type<G, A>>
  readonly ap: <A, B>(fgab: Type<F, Type<G, (a: A) => B>>, fga: Type<F, Type<G, A>>) => Type<F, Type<G, B>>
}

export interface ApplicativeComposition12<F extends URIS, G extends URIS2> extends FunctorComposition12<F, G> {
  readonly of: <LG, A>(a: A) => Type<F, Type2<G, LG, A>>
  readonly ap: <LG, A, B>(
    fgab: Type<F, Type2<G, LG, (a: A) => B>>,
    fga: Type<F, Type2<G, LG, A>>
  ) => Type<F, Type2<G, LG, B>>
}

export interface ApplicativeComposition12C<F extends URIS, G extends URIS2, LG>
  extends FunctorComposition12C<F, G, LG> {
  readonly of: <A>(a: A) => Type<F, Type2<G, LG, A>>
  readonly ap: <A, B>(
    fgab: Type<F, Type2<G, LG, (a: A) => B>>,
    fga: Type<F, Type2<G, LG, A>>
  ) => Type<F, Type2<G, LG, B>>
}

export interface ApplicativeComposition21<F extends URIS2, G extends URIS> extends FunctorComposition21<F, G> {
  readonly of: <LF, A>(a: A) => Type2<F, LF, Type<G, A>>
  readonly ap: <LF, A, B>(
    fgab: Type2<F, LF, Type<G, (a: A) => B>>,
    fga: Type2<F, LF, Type<G, A>>
  ) => Type2<F, LF, Type<G, B>>
}

export interface ApplicativeComposition2C1<F extends URIS2, G extends URIS, LF>
  extends FunctorComposition2C1<F, G, LF> {
  readonly of: <A>(a: A) => Type2<F, LF, Type<G, A>>
  readonly ap: <A, B>(
    fgab: Type2<F, LF, Type<G, (a: A) => B>>,
    fga: Type2<F, LF, Type<G, A>>
  ) => Type2<F, LF, Type<G, B>>
}

export interface ApplicativeComposition22<F extends URIS2, G extends URIS2> extends FunctorComposition22<F, G> {
  readonly of: <LF, LG, A>(a: A) => Type2<F, LF, Type2<G, LG, A>>
  readonly ap: <L, M, A, B>(
    fgab: Type2<F, L, Type2<G, M, (a: A) => B>>,
    fga: Type2<F, L, Type2<G, M, A>>
  ) => Type2<F, L, Type2<G, M, B>>
}

export interface ApplicativeComposition22C<F extends URIS2, G extends URIS2, LG>
  extends FunctorComposition22C<F, G, LG> {
  readonly of: <LF, A>(a: A) => Type2<F, LF, Type2<G, LG, A>>
  readonly ap: <LF, A, B>(
    fgab: Type2<F, LF, Type2<G, LG, (a: A) => B>>,
    fga: Type2<F, LF, Type2<G, LG, A>>
  ) => Type2<F, LF, Type2<G, LG, B>>
}

export interface ApplicativeComposition3C1<F extends URIS3, G extends URIS, UF, LF>
  extends FunctorComposition3C1<F, G, UF, LF> {
  readonly of: <A>(a: A) => Type3<F, UF, LF, Type<G, A>>
  readonly ap: <A, B>(
    fgab: Type3<F, UF, LF, Type<G, (a: A) => B>>,
    fga: Type3<F, UF, LF, Type<G, A>>
  ) => Type3<F, UF, LF, Type<G, B>>
}

/**
 * Perform a applicative action when a condition is true
 *
 * @example
 * import { IO, io }  from  'fp-ts/lib/IO.ts'
 * import { when }  from  'fp-ts/lib/Applicative.ts'
 *
 * const log: Array<string> = []
 * const action = new IO(() => {
 *   log.push('action called')
 * })
 * when(io)(false, action).run()
 * assert.deepStrictEqual(log, [])
 * when(io)(true, action).run()
 * assert.deepStrictEqual(log, ['action called'])
 *
 * @since 1.0.0
 */
export function when<F extends URIS3>(
  F: Applicative3<F>
): <U, L>(condition: boolean, fu: Type3<F, U, L, void>) => Type3<F, U, L, void>
export function when<F extends URIS3, U, L>(
  F: Applicative3C<F, U, L>
): (condition: boolean, fu: Type3<F, U, L, void>) => Type3<F, U, L, void>
export function when<F extends URIS2>(
  F: Applicative2<F>
): <L>(condition: boolean, fu: Type2<F, L, void>) => Type2<F, L, void>
export function when<F extends URIS2, L>(
  F: Applicative2C<F, L>
): (condition: boolean, fu: Type2<F, L, void>) => Type2<F, L, void>
export function when<F extends URIS>(F: Applicative1<F>): (condition: boolean, fu: Type<F, void>) => Type<F, void>
export function when<F>(F: Applicative<F>): (condition: boolean, fu: HKT<F, void>) => HKT<F, void>
export function when<F>(F: Applicative<F>): (condition: boolean, fu: HKT<F, void>) => HKT<F, void> {
  return (condition, fu) => (condition ? fu : F.of(undefined))
}

/**
 * Like `Functor`, `Applicative`s compose. If `F` and `G` have `Applicative` instances, then so does `F<G<_>>`
 *
 * @example
 * import { getApplicativeComposition }  from  'fp-ts/lib/Applicative.ts'
 * import { option, Option, some }  from  'fp-ts/lib/Option.ts'
 * import { task, Task }  from  'fp-ts/lib/Task.ts'
 *
 * const x: Task<Option<number>> = task.of(some(1))
 * const y: Task<Option<number>> = task.of(some(2))
 *
 * const A = getApplicativeComposition(task, option)
 *
 * const sum = (a: number) => (b: number): number => a + b
 * A.ap(A.map(x, sum), y)
 *   .run()
 *   .then(result => assert.deepStrictEqual(result, some(3)))
 *
 * @since 1.0.0
 */
export function getApplicativeComposition<F extends URIS3, G extends URIS, UF, LF>(
  F: Applicative3C<F, UF, LF>,
  G: Applicative1<G>
): ApplicativeComposition3C1<F, G, UF, LF>
export function getApplicativeComposition<F extends URIS2, G extends URIS2, LG>(
  F: Applicative2<F>,
  G: Applicative2C<G, LG>
): ApplicativeComposition22C<F, G, LG>
export function getApplicativeComposition<F extends URIS2, G extends URIS2>(
  F: Applicative2<F>,
  G: Applicative2<G>
): ApplicativeComposition22<F, G>
export function getApplicativeComposition<F extends URIS2, G extends URIS2, LG>(
  F: Applicative2<F>,
  G: Applicative2C<G, LG>
): ApplicativeComposition22C<F, G, LG>
export function getApplicativeComposition<F extends URIS2, G extends URIS>(
  F: Applicative2<F>,
  G: Applicative1<G>
): ApplicativeComposition21<F, G>
export function getApplicativeComposition<F extends URIS, G extends URIS2>(
  F: Applicative1<F>,
  G: Applicative2<G>
): ApplicativeComposition12<F, G>
export function getApplicativeComposition<F extends URIS, G extends URIS2, LG>(
  F: Applicative1<F>,
  G: Applicative2C<G, LG>
): ApplicativeComposition12C<F, G, LG>
export function getApplicativeComposition<F extends URIS, G extends URIS>(
  F: Applicative1<F>,
  G: Applicative1<G>
): ApplicativeComposition11<F, G>
export function getApplicativeComposition<F, G extends URIS2>(
  F: Applicative<F>,
  G: Applicative2<G>
): ApplicativeComposition<F, G>
export function getApplicativeComposition<F, G extends URIS>(
  F: Applicative<F>,
  G: Applicative1<G>
): ApplicativeComposition<F, G>
export function getApplicativeComposition<F, G>(F: Applicative<F>, G: Applicative<G>): ApplicativeComposition<F, G>
export function getApplicativeComposition<F, G>(F: Applicative<F>, G: Applicative<G>): ApplicativeComposition<F, G> {
  return {
    ...getFunctorComposition(F, G),
    of: a => F.of(G.of(a)),
    ap: <A, B>(fgab: HKT<F, HKT<G, (a: A) => B>>, fga: HKT<F, HKT<G, A>>): HKT<F, HKT<G, B>> =>
      F.ap(F.map(fgab, h => (ga: HKT<G, A>) => G.ap<A, B>(h, ga)), fga)
  }
}

/**
 * If `F` is a `Applicative` and `M` is a `Monoid` over `A` then `HKT<F, A>` is a `Monoid` over `A` as well.
 * Adapted from http://hackage.haskell.org/package/monoids-0.2.0.2/docs/Data-Monoid-Applicative.html
 *
 * @example
 * import { getMonoid }  from  'fp-ts/lib/Applicative.ts'
 * import { option, some, none }  from  'fp-ts/lib/Option.ts'
 * import { monoidSum }  from  'fp-ts/lib/Monoid.ts'
 *
 * const M = getMonoid(option, monoidSum)()
 * assert.deepStrictEqual(M.concat(none, none), none)
 * assert.deepStrictEqual(M.concat(some(1), none), none)
 * assert.deepStrictEqual(M.concat(none, some(2)), none)
 * assert.deepStrictEqual(M.concat(some(1), some(2)), some(3))
 *
 * @since 1.4.0
 */
export function getMonoid<F extends URIS3, A>(
  F: Applicative3<F>,
  M: Monoid<A>
): <U = never, L = never>() => Monoid<Type3<F, U, L, A>>
export function getMonoid<F extends URIS3, U, L, A>(
  F: Applicative3C<F, U, L>,
  M: Monoid<A>
): () => Monoid<Type3<F, U, L, A>>
export function getMonoid<F extends URIS2, A>(F: Applicative2<F>, M: Monoid<A>): <L = never>() => Monoid<Type2<F, L, A>>
export function getMonoid<F extends URIS2, L, A>(F: Applicative2C<F, L>, M: Monoid<A>): () => Monoid<Type2<F, L, A>>
export function getMonoid<F extends URIS, A>(F: Applicative1<F>, M: Monoid<A>): () => Monoid<Type<F, A>>
export function getMonoid<F, A>(F: Applicative<F>, M: Monoid<A>): () => Monoid<HKT<F, A>>
export function getMonoid<F, A>(F: Applicative<F>, M: Monoid<A>): () => Monoid<HKT<F, A>> {
  const S = getSemigroup(F, M)()
  return () => ({
    ...S,
    empty: F.of(M.empty)
  })
}

/**
 * @file The `Apply` class provides the `ap` which is used to apply a function to an argument under a type constructor.
 *
 * `Apply` can be used to lift functions of two or more arguments to work on values wrapped with the type constructor
 * `f`.
 *
 * Instances must satisfy the following law in addition to the `Functor` laws:
 *
 * 1. Associative composition: `F.ap(F.ap(F.map(fbc, bc => ab => a => bc(ab(a))), fab), fa) = F.ap(fbc, F.ap(fab, fa))`
 *
 * Formally, `Apply` represents a strong lax semi-monoidal endofunctor.
 */
import { Functor, Functor1, Functor2, Functor2C, Functor3, Functor3C }  from  './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Curried2, Curried3, Curried4, constant, curried, Function1 }  from  './function.ts'

/**
 * @since 1.0.0
 */
export interface Apply<F> extends Functor<F> {
  readonly ap: <A, B>(fab: HKT<F, (a: A) => B>, fa: HKT<F, A>) => HKT<F, B>
}

export interface Apply1<F extends URIS> extends Functor1<F> {
  readonly ap: <A, B>(fab: Type<F, (a: A) => B>, fa: Type<F, A>) => Type<F, B>
}

export interface Apply2<F extends URIS2> extends Functor2<F> {
  readonly ap: <L, A, B>(fab: Type2<F, L, (a: A) => B>, fa: Type2<F, L, A>) => Type2<F, L, B>
}

export interface Apply3<F extends URIS3> extends Functor3<F> {
  readonly ap: <U, L, A, B>(fab: Type3<F, U, L, (a: A) => B>, fa: Type3<F, U, L, A>) => Type3<F, U, L, B>
}

export interface Apply2C<F extends URIS2, L> extends Functor2C<F, L> {
  readonly ap: <A, B>(fab: Type2<F, L, (a: A) => B>, fa: Type2<F, L, A>) => Type2<F, L, B>
}

export interface Apply3C<F extends URIS3, U, L> extends Functor3C<F, U, L> {
  readonly ap: <A, B>(fab: Type3<F, U, L, (a: A) => B>, fa: Type3<F, U, L, A>) => Type3<F, U, L, B>
}

/**
 * Combine two effectful actions, keeping only the result of the first
 *
 * @since 1.0.0
 */
export function applyFirst<F extends URIS3>(
  F: Apply3<F>
): <U, L, A, B>(fa: Type3<F, U, L, A>, fb: Type3<F, U, L, B>) => Type3<F, U, L, A>
export function applyFirst<F extends URIS3, U, L>(
  F: Apply3C<F, U, L>
): <A, B>(fa: Type3<F, U, L, A>, fb: Type3<F, U, L, B>) => Type3<F, U, L, A>
export function applyFirst<F extends URIS2>(
  F: Apply2<F>
): <L, A, B>(fa: Type2<F, L, A>, fb: Type2<F, L, B>) => Type2<F, L, A>
export function applyFirst<F extends URIS2, L>(
  F: Apply2C<F, L>
): <A, B>(fa: Type2<F, L, A>, fb: Type2<F, L, B>) => Type2<F, L, A>
export function applyFirst<F extends URIS>(F: Apply1<F>): <A, B>(fa: Type<F, A>, fb: Type<F, B>) => Type<F, A>
export function applyFirst<F>(F: Apply<F>): <A, B>(fa: HKT<F, A>, fb: HKT<F, B>) => HKT<F, A>
export function applyFirst<F>(F: Apply<F>): <A, B>(fa: HKT<F, A>, fb: HKT<F, B>) => HKT<F, A> {
  return (fa, fb) => F.ap(F.map(fa, constant), fb)
}

/**
 * Combine two effectful actions, keeping only the result of the second
 *
 * @since 1.0.0
 */
export function applySecond<F extends URIS3>(
  F: Apply3<F>
): <U, L, A, B>(fa: Type3<F, U, L, A>, fb: Type3<F, U, L, B>) => Type3<F, U, L, B>
export function applySecond<F extends URIS3, U, L>(
  F: Apply3C<F, U, L>
): <A, B>(fa: Type3<F, U, L, A>, fb: Type3<F, U, L, B>) => Type3<F, U, L, B>
export function applySecond<F extends URIS2>(
  F: Apply2<F>
): <L, A, B>(fa: Type2<F, L, A>, fb: Type2<F, L, B>) => Type2<F, L, B>
export function applySecond<F extends URIS2, L>(
  F: Apply2C<F, L>
): <A, B>(fa: Type2<F, L, A>, fb: Type2<F, L, B>) => Type2<F, L, B>
export function applySecond<F extends URIS>(F: Apply1<F>): <A, B>(fa: Type<F, A>, fb: Type<F, B>) => Type<F, B>
export function applySecond<F>(F: Apply<F>): <A, B>(fa: HKT<F, A>, fb: HKT<F, B>) => HKT<F, B>
export function applySecond<F>(F: Apply<F>): <A, B>(fa: HKT<F, A>, fb: HKT<F, B>) => HKT<F, B> {
  return <A, B>(fa: HKT<F, A>, fb: HKT<F, B>) => F.ap(F.map(fa, () => (b: B) => b), fb)
}

/**
 * Lift a function of two arguments to a function which accepts and returns values wrapped with the type constructor `F`
 *
 * Use `sequenceT` / `sequenceS` instead.
 *
 * @since 1.0.0
 * @deprecated
 */
export function liftA2<F extends URIS3>(
  F: Apply3<F>
): <A, B, C>(f: Curried2<A, B, C>) => <U, L>(fa: Type3<F, U, L, A>) => (fb: Type3<F, U, L, B>) => Type3<F, U, L, C>
export function liftA2<F extends URIS3, U, L>(
  F: Apply3C<F, U, L>
): <A, B, C>(f: Curried2<A, B, C>) => (fa: Type3<F, U, L, A>) => (fb: Type3<F, U, L, B>) => Type3<F, U, L, C>
export function liftA2<F extends URIS2>(
  F: Apply2<F>
): <A, B, C>(f: Curried2<A, B, C>) => <L>(fa: Type2<F, L, A>) => (fb: Type2<F, L, B>) => Type2<F, L, C>
export function liftA2<F extends URIS2, L>(
  F: Apply2C<F, L>
): <A, B, C>(f: Curried2<A, B, C>) => (fa: Type2<F, L, A>) => (fb: Type2<F, L, B>) => Type2<F, L, C>
export function liftA2<F extends URIS>(
  F: Apply1<F>
): <A, B, C>(f: Curried2<A, B, C>) => Curried2<Type<F, A>, Type<F, B>, Type<F, C>>
/** @deprecated */
export function liftA2<F>(F: Apply<F>): <A, B, C>(f: Curried2<A, B, C>) => Curried2<HKT<F, A>, HKT<F, B>, HKT<F, C>>
export function liftA2<F>(F: Apply<F>): <A, B, C>(f: Curried2<A, B, C>) => Curried2<HKT<F, A>, HKT<F, B>, HKT<F, C>> {
  return f => fa => fb => F.ap(F.map(fa, f), fb)
}

/**
 * Lift a function of three arguments to a function which accepts and returns values wrapped with the type constructor
 * `F`
 *
 * Use `sequenceT` / `sequenceS` instead.
 *
 * @since 1.0.0
 * @deprecated
 */
export function liftA3<F extends URIS3>(
  F: Apply3<F>
): <A, B, C, D>(
  f: Curried3<A, B, C, D>
) => <U, L>(fa: Type3<F, U, L, A>) => (fb: Type3<F, U, L, B>) => (fc: Type3<F, U, L, C>) => Type3<F, U, L, D>
export function liftA3<F extends URIS3, U, L>(
  F: Apply3C<F, U, L>
): <A, B, C, D>(
  f: Curried3<A, B, C, D>
) => (fa: Type3<F, U, L, A>) => (fb: Type3<F, U, L, B>) => (fc: Type3<F, U, L, C>) => Type3<F, U, L, D>
export function liftA3<F extends URIS2>(
  F: Apply2<F>
): <A, B, C, D>(
  f: Curried3<A, B, C, D>
) => <L>(fa: Type2<F, L, A>) => (fb: Type2<F, L, B>) => (fc: Type2<F, L, C>) => Type2<F, L, D>
export function liftA3<F extends URIS2, L>(
  F: Apply2C<F, L>
): <A, B, C, D>(
  f: Curried3<A, B, C, D>
) => (fa: Type2<F, L, A>) => (fb: Type2<F, L, B>) => (fc: Type2<F, L, C>) => Type2<F, L, D>
export function liftA3<F extends URIS>(
  F: Apply1<F>
): <A, B, C, D>(f: Curried3<A, B, C, D>) => Curried3<Type<F, A>, Type<F, B>, Type<F, C>, Type<F, D>>
/** @deprecated */
export function liftA3<F>(
  F: Apply<F>
): <A, B, C, D>(f: Curried3<A, B, C, D>) => Curried3<HKT<F, A>, HKT<F, B>, HKT<F, C>, HKT<F, D>>
export function liftA3<F>(
  F: Apply<F>
): <A, B, C, D>(f: Curried3<A, B, C, D>) => Curried3<HKT<F, A>, HKT<F, B>, HKT<F, C>, HKT<F, D>> {
  return f => fa => fb => fc => F.ap(F.ap(F.map(fa, f), fb), fc)
}

/**
 * Lift a function of four arguments to a function which accepts and returns values wrapped with the type constructor
 * `F`
 *
 * Use `sequenceT` / `sequenceS` instead.
 *
 * @since 1.0.0
 * @deprecated
 */
export function liftA4<F extends URIS3>(
  F: Apply3<F>
): <A, B, C, D, E>(
  f: Curried4<A, B, C, D, E>
) => <U, L>(
  fa: Type3<F, U, L, A>
) => (fb: Type3<F, U, L, B>) => (fc: Type3<F, U, L, C>) => (fd: Type3<F, U, L, D>) => Type3<F, U, L, E>
export function liftA4<F extends URIS3, U, L>(
  F: Apply3C<F, U, L>
): <A, B, C, D, E>(
  f: Curried4<A, B, C, D, E>
) => (
  fa: Type3<F, U, L, A>
) => (fb: Type3<F, U, L, B>) => (fc: Type3<F, U, L, C>) => (fd: Type3<F, U, L, D>) => Type3<F, U, L, E>
export function liftA4<F extends URIS2>(
  F: Apply2<F>
): <A, B, C, D, E>(
  f: Curried4<A, B, C, D, E>
) => <L>(fa: Type2<F, L, A>) => (fb: Type2<F, L, B>) => (fc: Type2<F, L, C>) => (fd: Type2<F, L, D>) => Type2<F, L, E>
export function liftA4<F extends URIS2, L>(
  F: Apply2C<F, L>
): <A, B, C, D, E>(
  f: Curried4<A, B, C, D, E>
) => (fa: Type2<F, L, A>) => (fb: Type2<F, L, B>) => (fc: Type2<F, L, C>) => (fd: Type2<F, L, D>) => Type2<F, L, E>
export function liftA4<F extends URIS>(
  F: Apply1<F>
): <A, B, C, D, E>(f: Curried4<A, B, C, D, E>) => Curried4<Type<F, A>, Type<F, B>, Type<F, C>, Type<F, D>, Type<F, E>>
/** @deprecated */
export function liftA4<F>(
  F: Apply<F>
): <A, B, C, D, E>(f: Curried4<A, B, C, D, E>) => Curried4<HKT<F, A>, HKT<F, B>, HKT<F, C>, HKT<F, D>, HKT<F, E>>
export function liftA4<F>(
  F: Apply<F>
): <A, B, C, D, E>(f: Curried4<A, B, C, D, E>) => Curried4<HKT<F, A>, HKT<F, B>, HKT<F, C>, HKT<F, D>, HKT<F, E>> {
  return f => fa => fb => fc => fd => F.ap(F.ap(F.ap(F.map(fa, f), fb), fc), fd)
}

/**
 * If `F` is a `Apply` and `S` is a `Semigroup` over `A` then `HKT<F, A>` is a `Semigroup` over `A` as well
 *
 * @example
 * import { getSemigroup }  from  'fp-ts/lib/Apply.ts'
 * import { option, some, none }  from  'fp-ts/lib/Option.ts'
 * import { monoidSum }  from  'fp-ts/lib/Monoid.ts'
 *
 * const S = getSemigroup(option, monoidSum)()
 * assert.deepStrictEqual(S.concat(none, none), none)
 * assert.deepStrictEqual(S.concat(some(1), none), none)
 * assert.deepStrictEqual(S.concat(none, some(2)), none)
 * assert.deepStrictEqual(S.concat(some(1), some(2)), some(3))
 *
 * @since 1.4.0
 */
export function getSemigroup<F extends URIS3, A>(
  F: Apply3<F>,
  S: Semigroup<A>
): <U = never, L = never>() => Semigroup<Type3<F, U, L, A>>
export function getSemigroup<F extends URIS3, U, L, A>(
  F: Apply3C<F, U, L>,
  S: Semigroup<A>
): () => Semigroup<Type3<F, U, L, A>>
export function getSemigroup<F extends URIS2, A>(
  F: Apply2<F>,
  S: Semigroup<A>
): <L = never>() => Semigroup<Type2<F, L, A>>
export function getSemigroup<F extends URIS2, L, A>(F: Apply2C<F, L>, S: Semigroup<A>): () => Semigroup<Type2<F, L, A>>
export function getSemigroup<F extends URIS, A>(F: Apply1<F>, S: Semigroup<A>): () => Semigroup<Type<F, A>>
export function getSemigroup<F, A>(F: Apply<F>, S: Semigroup<A>): () => Semigroup<HKT<F, A>>
export function getSemigroup<F, A>(F: Apply<F>, S: Semigroup<A>): () => Semigroup<HKT<F, A>> {
  const f = (a: A) => (b: A) => S.concat(a, b)
  return () => ({
    concat: (x, y) => F.ap(F.map(x, f), y)
  })
}

export interface SequenceT3<F extends URIS3> {
  <U, L, T extends Array<Type3<F, U, L, any>>>(...t: T & { 0: Type3<F, U, L, any> }): Type3<
    F,
    U,
    L,
    { [K in keyof T]: [T[K]] extends [Type3<F, U, L, infer A>] ? A : never }
  >
}
export interface SequenceT3C<F extends URIS3, U, L> {
  <T extends Array<Type3<F, U, L, any>>>(...t: T & { 0: Type3<F, U, L, any> }): Type3<
    F,
    U,
    L,
    { [K in keyof T]: [T[K]] extends [Type3<F, U, L, infer A>] ? A : never }
  >
}
export interface SequenceT2<F extends URIS2> {
  <L, T extends Array<Type2<F, L, any>>>(...t: T & { 0: Type2<F, L, any> }): Type2<
    F,
    L,
    { [K in keyof T]: [T[K]] extends [Type2<F, L, infer A>] ? A : never }
  >
}
export interface SequenceT2C<F extends URIS2, L> {
  <T extends Array<Type2<F, L, any>>>(...t: T & { 0: Type2<F, L, any> }): Type2<
    F,
    L,
    { [K in keyof T]: [T[K]] extends [Type2<F, L, infer A>] ? A : never }
  >
}
export interface SequenceT1<F extends URIS> {
  <T extends Array<Type<F, any>>>(...t: T & { 0: Type<F, any> }): Type<
    F,
    { [K in keyof T]: [T[K]] extends [Type<F, infer A>] ? A : never }
  >
}
export interface SequenceT<F> {
  <T extends Array<HKT<F, any>>>(...t: T & { 0: HKT<F, any> }): HKT<
    F,
    { [K in keyof T]: [T[K]] extends [HKT<F, infer A>] ? A : never }
  >
}

const tupleConstructors: { [key: string]: Function1<any, any> } = {}

/**
 * Tuple sequencing, i.e., take a tuple of monadic actions and does them from left-to-right, returning the resulting tuple.
 *
 * @example
 * import { sequenceT }  from  'fp-ts/lib/Apply.ts'
 * import { option, some, none }  from  'fp-ts/lib/Option.ts'
 *
 * const sequenceTOption = sequenceT(option)
 * assert.deepStrictEqual(sequenceTOption(some(1)), some([1]))
 * assert.deepStrictEqual(sequenceTOption(some(1), some('2')), some([1, '2']))
 * assert.deepStrictEqual(sequenceTOption(some(1), some('2'), none), none)
 *
 * @since 1.5.0
 */
export function sequenceT<F extends URIS3>(F: Apply3<F>): SequenceT3<F>
export function sequenceT<F extends URIS3, U, L>(F: Apply3C<F, U, L>): SequenceT3C<F, U, L>
export function sequenceT<F extends URIS2>(F: Apply2<F>): SequenceT2<F>
export function sequenceT<F extends URIS2, L>(F: Apply2C<F, L>): SequenceT2C<F, L>
export function sequenceT<F extends URIS>(F: Apply1<F>): SequenceT1<F>
export function sequenceT<F>(F: Apply<F>): SequenceT<F>
export function sequenceT<F>(F: Apply<F>): (...args: Array<any>) => HKT<F, any> {
  return (...args: Array<any>) => {
    const len = args.length
    let f = tupleConstructors[len]
    if (!Boolean(f)) {
      f = tupleConstructors[len] = curried((...args: Array<any>): Array<any> => args, len - 1, [])
    }
    let r = F.map(args[0], f)
    for (let i = 1; i < len; i++) {
      r = F.ap(r, args[i])
    }
    return r
  }
}

type EnforceNonEmptyRecord<R> = keyof R extends never ? never : R

/**
 * Like `Apply.sequenceT` but works with structs instead of tuples.
 *
 * @example
 * import { either, right, left }  from  'fp-ts/lib/Either.ts'
 * import { sequenceS }  from  'fp-ts/lib/Apply.ts'
 *
 * const ado = sequenceS(either)
 *
 * assert.deepStrictEqual(
 *   ado({
 *     a: right<string, number>(1),
 *     b: right<string, boolean>(true)
 *   }),
 *   right({ a: 1, b: true })
 * )
 * assert.deepStrictEqual(
 *   ado({
 *     a: right<string, number>(1),
 *     b: left<string, number>('error')
 *   }),
 *   left('error')
 * )
 *
 * @since 1.15.0
 */
export function sequenceS<F extends URIS3>(
  F: Apply3<F>
): <U, L, R extends Record<string, Type3<F, U, L, any>>>(
  r: EnforceNonEmptyRecord<R> & Record<string, Type3<F, U, L, any>>
) => Type3<F, U, L, { [K in keyof R]: [R[K]] extends [Type3<F, any, any, infer A>] ? A : never }>
export function sequenceS<F extends URIS3, U, L>(
  F: Apply3C<F, U, L>
): <R extends Record<string, Type3<F, U, L, any>>>(
  r: EnforceNonEmptyRecord<R>
) => Type3<F, U, L, { [K in keyof R]: [R[K]] extends [Type3<F, any, any, infer A>] ? A : never }>
export function sequenceS<F extends URIS2>(
  F: Apply2<F>
): <L, R extends Record<string, Type2<F, L, any>>>(
  r: EnforceNonEmptyRecord<R> & Record<string, Type2<F, L, any>>
) => Type2<F, L, { [K in keyof R]: [R[K]] extends [Type2<F, any, infer A>] ? A : never }>
export function sequenceS<F extends URIS2, L>(
  F: Apply2C<F, L>
): <R extends Record<string, Type2<F, L, any>>>(
  r: EnforceNonEmptyRecord<R>
) => Type2<F, L, { [K in keyof R]: [R[K]] extends [Type2<F, any, infer A>] ? A : never }>
export function sequenceS<F extends URIS>(
  F: Apply1<F>
): <R extends Record<string, Type<F, any>>>(
  r: EnforceNonEmptyRecord<R>
) => Type<F, { [K in keyof R]: [R[K]] extends [Type<F, infer A>] ? A : never }>
export function sequenceS<F>(
  F: Apply<F>
): <R extends Record<string, HKT<F, any>>>(
  r: EnforceNonEmptyRecord<R>
) => HKT<F, { [K in keyof R]: [R[K]] extends [HKT<F, infer A>] ? A : never }>
export function sequenceS<F>(F: Apply<F>): (r: Record<string, HKT<F, any>>) => HKT<F, Record<string, any>> {
  return r => {
    const keys = Object.keys(r)
    const fst = keys[0]
    const others = keys.slice(1)
    let fr: HKT<F, Record<string, any>> = F.map(r[fst], a => ({ [fst]: a }))
    for (const key of others) {
      fr = F.ap(
        F.map(fr, r => (a: any) => {
          r[key] = a
          return r
        }),
        r[key]
      )
    }
    return fr
  }
}

/**
 * @file `Compactable` represents data structures which can be _compacted_/_filtered_. This is a generalization of
 * `catOptions` as a new function `compact`. `compact` has relations with `Functor`, `Applicative`,
 * `Monad`, `Plus`, and `Traversable` in that we can use these classes to provide the ability to
 * operate on a data type by eliminating intermediate `None`s. This is useful for representing the filtering out of
 * values, or failure.
 *
 * Adapted from https://github.com/LiamGoodacre/purescript-filterable/blob/master/src/Data/Compactable.purs
 */
import { Either }  from  './Either.ts'
import {
  Functor,
  Functor1,
  Functor2,
  Functor2C,
  Functor3C,
  FunctorComposition,
  FunctorComposition11,
  FunctorComposition12,
  FunctorComposition12C,
  FunctorComposition21,
  FunctorComposition22,
  FunctorComposition22C,
  FunctorComposition2C1,
  FunctorComposition3C1,
  getFunctorComposition
} from './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { fromEither, none, Option, some }  from  './Option.ts'

/**
 * A `Separated` type which holds `left` and `right` parts.
 *
 * @since 1.7.0
 */
export interface Separated<A, B> {
  readonly left: A
  readonly right: B
}

/**
 * @since 1.7.0
 */
export interface Compactable<F> {
  readonly URI: F
  /**
   * Compacts a data structure unwrapping inner Option
   */
  readonly compact: <A>(fa: HKT<F, Option<A>>) => HKT<F, A>
  /**
   * Separates a data structure moving inner Left to the left side and inner Right to the right side of Separated
   */
  readonly separate: <A, B>(fa: HKT<F, Either<A, B>>) => Separated<HKT<F, A>, HKT<F, B>>
}

export interface Compactable1<F extends URIS> {
  readonly URI: F
  readonly compact: <A>(fa: Type<F, Option<A>>) => Type<F, A>
  readonly separate: <A, B>(fa: Type<F, Either<A, B>>) => Separated<Type<F, A>, Type<F, B>>
}

export interface Compactable2<F extends URIS2> {
  readonly URI: F
  readonly compact: <L, A>(fa: Type2<F, L, Option<A>>) => Type2<F, L, A>
  readonly separate: <L, A, B>(fa: Type2<F, L, Either<A, B>>) => Separated<Type2<F, L, A>, Type2<F, L, B>>
}

export interface Compactable2C<F extends URIS2, L> {
  readonly URI: F
  readonly _L: L
  readonly compact: <A>(fa: Type2<F, L, Option<A>>) => Type2<F, L, A>
  readonly separate: <A, B>(fa: Type2<F, L, Either<A, B>>) => Separated<Type2<F, L, A>, Type2<F, L, B>>
}

export interface Compactable3<F extends URIS3> {
  readonly URI: F
  readonly compact: <U, L, A>(fa: Type3<F, U, L, Option<A>>) => Type3<F, U, L, A>
  readonly separate: <U, L, A, B>(fa: Type3<F, U, L, Either<A, B>>) => Separated<Type3<F, U, L, A>, Type3<F, U, L, B>>
}

export interface Compactable3C<F extends URIS3, U, L> {
  readonly URI: F
  readonly _L: L
  readonly _U: U
  readonly compact: <A>(fa: Type3<F, U, L, Option<A>>) => Type3<F, U, L, A>
  readonly separate: <A, B>(fa: Type3<F, U, L, Either<A, B>>) => Separated<Type3<F, U, L, A>, Type3<F, U, L, B>>
}

export interface CompactableComposition<F, G> extends FunctorComposition<F, G> {
  readonly compact: <A>(fga: HKT<F, HKT<G, Option<A>>>) => HKT<F, HKT<G, A>>
  readonly separate: <A, B>(fge: HKT<F, HKT<G, Either<A, B>>>) => Separated<HKT<F, HKT<G, A>>, HKT<F, HKT<G, B>>>
}

export interface CompactableComposition11<F extends URIS, G extends URIS> extends FunctorComposition11<F, G> {
  readonly compact: <A>(fga: Type<F, Type<G, Option<A>>>) => Type<F, Type<G, A>>
  readonly separate: <A, B>(fge: Type<F, Type<G, Either<A, B>>>) => Separated<Type<F, Type<G, A>>, Type<F, Type<G, B>>>
}

export interface CompactableComposition12<F extends URIS, G extends URIS2> extends FunctorComposition12<F, G> {
  readonly compact: <LG, A>(fga: Type<F, Type2<G, LG, Option<A>>>) => Type<F, Type2<G, LG, A>>
  readonly separate: <LG, A, B>(
    fge: Type<F, Type2<G, LG, Either<A, B>>>
  ) => Separated<Type<F, Type2<G, LG, A>>, Type<F, Type2<G, LG, B>>>
}

export interface CompactableComposition12C<F extends URIS, G extends URIS2, LG>
  extends FunctorComposition12C<F, G, LG> {
  readonly compact: <A>(fga: Type<F, Type2<G, LG, Option<A>>>) => Type<F, Type2<G, LG, A>>
  readonly separate: <A, B>(
    fge: Type<F, Type2<G, LG, Either<A, B>>>
  ) => Separated<Type<F, Type2<G, LG, A>>, Type<F, Type2<G, LG, B>>>
}

export interface CompactableComposition21<F extends URIS2, G extends URIS> extends FunctorComposition21<F, G> {
  readonly compact: <LF, A>(fga: Type2<F, LF, Type<G, Option<A>>>) => Type2<F, LF, Type<G, A>>
  readonly separate: <LF, A, B>(
    fge: Type2<F, LF, Type<G, Either<A, B>>>
  ) => Separated<Type2<F, LF, Type<G, A>>, Type2<F, LF, Type<G, B>>>
}

export interface CompactableComposition2C1<F extends URIS2, G extends URIS, LF>
  extends FunctorComposition2C1<F, G, LF> {
  readonly compact: <A>(fga: Type2<F, LF, Type<G, Option<A>>>) => Type2<F, LF, Type<G, A>>
  readonly separate: <A, B>(
    fge: Type2<F, LF, Type<G, Either<A, B>>>
  ) => Separated<Type2<F, LF, Type<G, A>>, Type2<F, LF, Type<G, B>>>
}

export interface CompactableComposition22<F extends URIS2, G extends URIS2> extends FunctorComposition22<F, G> {
  readonly compact: <LF, LG, A>(fga: Type2<F, LF, Type2<G, LG, Option<A>>>) => Type2<F, LF, Type2<G, LG, A>>
  readonly separate: <LF, LG, A, B>(
    fge: Type2<F, LF, Type2<G, LG, Either<A, B>>>
  ) => Separated<Type2<F, LF, Type2<G, LG, A>>, Type2<F, LF, Type2<G, LG, B>>>
}

export interface CompactableComposition22C<F extends URIS2, G extends URIS2, LG>
  extends FunctorComposition22C<F, G, LG> {
  readonly compact: <LF, A>(fga: Type2<F, LF, Type2<G, LG, Option<A>>>) => Type2<F, LF, Type2<G, LG, A>>
  readonly separate: <LF, A, B>(
    fge: Type2<F, LF, Type2<G, LG, Either<A, B>>>
  ) => Separated<Type2<F, LF, Type2<G, LG, A>>, Type2<F, LF, Type2<G, LG, B>>>
}

export interface CompactableComposition3C1<F extends URIS3, G extends URIS, UF, LF>
  extends FunctorComposition3C1<F, G, UF, LF> {
  readonly compact: <A>(fga: Type3<F, UF, LF, Type<G, Option<A>>>) => Type3<F, UF, LF, Type<G, A>>
  readonly separate: <A, B>(
    fge: Type3<F, UF, LF, Type<G, Either<A, B>>>
  ) => Separated<Type3<F, UF, LF, Type<G, A>>, Type3<F, UF, LF, Type<G, B>>>
}

/**
 * @since 1.12.0
 */
export function getCompactableComposition<F extends URIS3, G extends URIS, UF, LF>(
  F: Functor3C<F, UF, LF>,
  G: Compactable1<G> & Functor1<G>
): CompactableComposition3C1<F, G, UF, LF>
export function getCompactableComposition<F extends URIS2, G extends URIS2, LG>(
  F: Functor2<F>,
  G: Compactable2C<G, LG> & Functor2C<G, LG>
): CompactableComposition22C<F, G, LG>
export function getCompactableComposition<F extends URIS2, G extends URIS2>(
  F: Functor2<F>,
  G: Compactable2<G> & Functor2<G>
): CompactableComposition22<F, G>
export function getCompactableComposition<F extends URIS2, G extends URIS, LF>(
  F: Functor2C<F, LF>,
  G: Compactable1<G> & Functor1<G>
): CompactableComposition2C1<F, G, LF>
export function getCompactableComposition<F extends URIS2, G extends URIS>(
  F: Functor2<F>,
  G: Compactable1<G> & Functor1<G>
): CompactableComposition21<F, G>
export function getCompactableComposition<F extends URIS, G extends URIS2, LG>(
  F: Functor1<F>,
  G: Compactable2C<G, LG> & Functor2C<G, LG>
): CompactableComposition12<F, G>
export function getCompactableComposition<F extends URIS, G extends URIS2>(
  F: Functor1<F>,
  G: Compactable2<G> & Functor2<G>
): CompactableComposition12<F, G>
export function getCompactableComposition<F extends URIS, G extends URIS>(
  F: Functor1<F>,
  G: Compactable1<G> & Functor1<G>
): CompactableComposition11<F, G>
export function getCompactableComposition<F, G>(
  F: Functor<F>,
  G: Compactable<G> & Functor<G>
): CompactableComposition<F, G>
export function getCompactableComposition<F, G>(
  F: Functor<F>,
  G: Compactable<G> & Functor<G>
): CompactableComposition<F, G> {
  const FC = getFunctorComposition(F, G)
  const CC: CompactableComposition<F, G> = {
    ...FC,
    compact: fga => F.map(fga, G.compact),
    separate: fge => {
      const left = CC.compact(FC.map(fge, e => e.fold(some, () => none)))
      const right = CC.compact(FC.map(fge, fromEither))
      return { left, right }
    }
  }
  return CC
}

/**
 * @file `Filterable` represents data structures which can be _partitioned_/_filtered_.
 *
 * Adapted from https://github.com/LiamGoodacre/purescript-filterable/blob/master/src/Data/Filterable.purs
 */
import {
  Compactable,
  Compactable1,
  Compactable2,
  Compactable2C,
  Compactable3,
  Compactable3C,
  CompactableComposition,
  CompactableComposition11,
  CompactableComposition12,
  CompactableComposition12C,
  CompactableComposition21,
  CompactableComposition22,
  CompactableComposition3C1,
  getCompactableComposition,
  Separated
} from './Compactable.ts'
import { Either }  from  './Either.ts'
import { Predicate, Refinement }  from  './function.ts'
import {
  Functor,
  Functor1,
  Functor2,
  Functor2C,
  Functor3,
  Functor3C,
  FunctorComposition,
  FunctorComposition11,
  FunctorComposition12,
  FunctorComposition12C,
  FunctorComposition21,
  FunctorComposition22,
  FunctorComposition3C1
} from './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Option, some, none }  from  './Option.ts'

interface Filter<F> {
  <A, B extends A>(fa: HKT<F, A>, refinement: Refinement<A, B>): HKT<F, B>
  <A>(fa: HKT<F, A>, predicate: Predicate<A>): HKT<F, A>
}

interface Partition<F> {
  <A, B extends A>(fa: HKT<F, A>, refinement: Refinement<A, B>): Separated<HKT<F, A>, HKT<F, B>>
  <A>(fa: HKT<F, A>, predicate: Predicate<A>): Separated<HKT<F, A>, HKT<F, A>>
}

/**
 * @since 1.7.0
 */
export interface Filterable<F> extends Functor<F>, Compactable<F> {
  /**
   * Partition a data structure based on an either predicate.
   */
  readonly partitionMap: <RL, RR, A>(fa: HKT<F, A>, f: (a: A) => Either<RL, RR>) => Separated<HKT<F, RL>, HKT<F, RR>>
  /**
   * Partition a data structure based on a boolean predicate.
   */
  readonly partition: Partition<F>
  /**
   * Map over a data structure and filter based on an option predicate.
   */
  readonly filterMap: <A, B>(fa: HKT<F, A>, f: (a: A) => Option<B>) => HKT<F, B>
  /**
   * Filter a data structure based on a boolean predicate.
   */
  readonly filter: Filter<F>
}

interface Filter1<F extends URIS> {
  <A, B extends A>(fa: Type<F, A>, refinement: Refinement<A, B>): Type<F, B>
  <A>(fa: Type<F, A>, predicate: Predicate<A>): Type<F, A>
}

interface Partition1<F extends URIS> {
  <A, B extends A>(fa: Type<F, A>, refinement: Refinement<A, B>): Separated<Type<F, A>, Type<F, B>>
  <A>(fa: Type<F, A>, predicate: Predicate<A>): Separated<Type<F, A>, Type<F, A>>
}

/**
 * @since 1.7.0
 */
export interface Filterable1<F extends URIS> extends Functor1<F>, Compactable1<F> {
  readonly partitionMap: <RL, RR, A>(fa: Type<F, A>, f: (a: A) => Either<RL, RR>) => Separated<Type<F, RL>, Type<F, RR>>
  readonly partition: Partition1<F>
  readonly filterMap: <A, B>(fa: Type<F, A>, f: (a: A) => Option<B>) => Type<F, B>
  readonly filter: Filter1<F>
}

interface Filter2<F extends URIS2> {
  <L, A, B extends A>(fa: Type2<F, L, A>, refinement: Refinement<A, B>): Type2<F, L, B>
  <L, A>(fa: Type2<F, L, A>, predicate: Predicate<A>): Type2<F, L, A>
}

interface Partition2<F extends URIS2> {
  <L, A, B extends A>(fa: Type2<F, L, A>, refinement: Refinement<A, B>): Separated<Type2<F, L, A>, Type2<F, L, B>>
  <L, A>(fa: Type2<F, L, A>, predicate: Predicate<A>): Separated<Type2<F, L, A>, Type2<F, L, A>>
}

/**
 * @since 1.7.0
 */
export interface Filterable2<F extends URIS2> extends Functor2<F>, Compactable2<F> {
  readonly partitionMap: <RL, RR, L, A>(
    fa: Type2<F, L, A>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type2<F, L, RL>, Type2<F, L, RR>>
  readonly partition: Partition2<F>
  readonly filterMap: <L, A, B>(fa: Type2<F, L, A>, f: (a: A) => Option<B>) => Type2<F, L, B>
  readonly filter: Filter2<F>
}

interface Filter2C<F extends URIS2, L> {
  <A, B extends A>(fa: Type2<F, L, A>, refinement: Refinement<A, B>): Type2<F, L, B>
  <A>(fa: Type2<F, L, A>, predicate: Predicate<A>): Type2<F, L, A>
}

interface Partition2C<F extends URIS2, L> {
  <A, B extends A>(fa: Type2<F, L, A>, refinement: Refinement<A, B>): Separated<Type2<F, L, A>, Type2<F, L, B>>
  <A>(fa: Type2<F, L, A>, predicate: Predicate<A>): Separated<Type2<F, L, A>, Type2<F, L, A>>
}

/**
 * @since 1.7.0
 */
export interface Filterable2C<F extends URIS2, L> extends Functor2C<F, L>, Compactable2C<F, L> {
  readonly partitionMap: <RL, RR, A>(
    fa: Type2<F, L, A>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type2<F, L, RL>, Type2<F, L, RR>>
  readonly partition: Partition2C<F, L>
  readonly filterMap: <A, B>(fa: Type2<F, L, A>, f: (a: A) => Option<B>) => Type2<F, L, B>
  readonly filter: Filter2C<F, L>
}

interface Filter3<F extends URIS3> {
  <U, L, A, B extends A>(fa: Type3<F, U, L, A>, refinement: Refinement<A, B>): Type3<F, U, L, B>
  <U, L, A>(fa: Type3<F, U, L, A>, predicate: Predicate<A>): Type3<F, U, L, A>
}

interface Partition3<F extends URIS3> {
  <U, L, A, B extends A>(fa: Type3<F, U, L, A>, refinement: Refinement<A, B>): Separated<
    Type3<F, U, L, A>,
    Type3<F, U, L, B>
  >
  <U, L, A>(fa: Type3<F, U, L, A>, predicate: Predicate<A>): Separated<Type3<F, U, L, A>, Type3<F, U, L, A>>
}

/**
 * @since 1.7.0
 */
export interface Filterable3<F extends URIS3> extends Functor3<F>, Compactable3<F> {
  readonly partitionMap: <RL, RR, U, L, A>(
    fa: Type3<F, U, L, A>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type3<F, U, L, RL>, Type3<F, U, L, RR>>
  readonly partition: Partition3<F>
  readonly filterMap: <U, L, A, B>(fa: Type3<F, U, L, A>, f: (a: A) => Option<B>) => Type3<F, U, L, B>
  readonly filter: Filter3<F>
}

interface Filter3C<F extends URIS3, U, L> {
  <A, B extends A>(fa: Type3<F, U, L, A>, refinement: Refinement<A, B>): Type3<F, U, L, B>
  <A>(fa: Type3<F, U, L, A>, predicate: Predicate<A>): Type3<F, U, L, A>
}

interface Partition3C<F extends URIS3, U, L> {
  <A, B extends A>(fa: Type3<F, U, L, A>, refinement: Refinement<A, B>): Separated<Type3<F, U, L, A>, Type3<F, U, L, B>>
  <A>(fa: Type3<F, U, L, A>, predicate: Predicate<A>): Separated<Type3<F, U, L, A>, Type3<F, U, L, A>>
}

/**
 * @since 1.7.0
 */
export interface Filterable3C<F extends URIS3, U, L> extends Functor3C<F, U, L>, Compactable3C<F, U, L> {
  readonly partitionMap: <RL, RR, A>(
    fa: Type3<F, U, L, A>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type3<F, U, L, RL>, Type3<F, U, L, RR>>
  readonly partition: Partition3C<F, U, L>
  readonly filterMap: <A, B>(fa: Type3<F, U, L, A>, f: (a: A) => Option<B>) => Type3<F, U, L, B>
  readonly filter: Filter3C<F, U, L>
}

export interface FilterableComposition<F, G> extends FunctorComposition<F, G>, CompactableComposition<F, G> {
  readonly partitionMap: <RL, RR, A>(
    fa: HKT<F, HKT<G, A>>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<HKT<F, HKT<G, RL>>, HKT<F, HKT<G, RR>>>
  readonly partition: <A>(
    fa: HKT<F, HKT<G, A>>,
    predicate: Predicate<A>
  ) => Separated<HKT<F, HKT<G, A>>, HKT<F, HKT<G, A>>>
  readonly filterMap: <A, B>(fa: HKT<F, HKT<G, A>>, f: (a: A) => Option<B>) => HKT<F, HKT<G, B>>
  readonly filter: <A>(fa: HKT<F, HKT<G, A>>, predicate: Predicate<A>) => HKT<F, HKT<G, A>>
}

export interface FilterableComposition11<F extends URIS, G extends URIS>
  extends FunctorComposition11<F, G>,
    CompactableComposition11<F, G> {
  readonly partitionMap: <RL, RR, A>(
    fa: Type<F, Type<G, A>>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type<F, Type<G, RL>>, Type<F, Type<G, RR>>>
  readonly partition: <A>(
    fa: Type<F, Type<G, A>>,
    predicate: Predicate<A>
  ) => Separated<Type<F, Type<G, A>>, Type<F, Type<G, A>>>
  readonly filterMap: <A, B>(fa: Type<F, Type<G, A>>, f: (a: A) => Option<B>) => Type<F, Type<G, B>>
  readonly filter: <A>(fa: Type<F, Type<G, A>>, predicate: Predicate<A>) => Type<F, Type<G, A>>
}

export interface FilterableComposition12<F extends URIS, G extends URIS2>
  extends FunctorComposition12<F, G>,
    CompactableComposition12<F, G> {
  readonly partitionMap: <LG, RL, RR, A>(
    fa: Type<F, Type2<G, LG, A>>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type<F, Type2<G, LG, RL>>, Type<F, Type2<G, LG, RR>>>
  readonly partition: <LG, A>(
    fa: Type<F, Type2<G, LG, A>>,
    predicate: Predicate<A>
  ) => Separated<Type<F, Type2<G, LG, A>>, Type<F, Type2<G, LG, A>>>
  readonly filterMap: <LG, A, B>(fa: Type<F, Type2<G, LG, A>>, f: (a: A) => Option<B>) => Type<F, Type2<G, LG, B>>
  readonly filter: <LG, A>(fa: Type<F, Type2<G, LG, A>>, predicate: Predicate<A>) => Type<F, Type2<G, LG, A>>
}

export interface FilterableComposition12C<F extends URIS, G extends URIS2, LG>
  extends FunctorComposition12C<F, G, LG>,
    CompactableComposition12C<F, G, LG> {
  readonly partitionMap: <RL, RR, A>(
    fa: Type<F, Type2<G, LG, A>>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type<F, Type2<G, LG, RL>>, Type<F, Type2<G, LG, RR>>>
  readonly partition: <A>(
    fa: Type<F, Type2<G, LG, A>>,
    predicate: Predicate<A>
  ) => Separated<Type<F, Type2<G, LG, A>>, Type<F, Type2<G, LG, A>>>
  readonly filterMap: <A, B>(fa: Type<F, Type2<G, LG, A>>, f: (a: A) => Option<B>) => Type<F, Type2<G, LG, B>>
  readonly filter: <A>(fa: Type<F, Type2<G, LG, A>>, predicate: Predicate<A>) => Type<F, Type2<G, LG, A>>
}

export interface FilterableComposition21<F extends URIS2, G extends URIS>
  extends FunctorComposition21<F, G>,
    CompactableComposition21<F, G> {
  readonly partitionMap: <LF, RL, RR, A>(
    fa: Type2<F, LF, Type<G, A>>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type2<F, LF, Type<G, RL>>, Type2<F, LF, Type<G, RR>>>
  readonly partition: <LF, A>(
    fa: Type2<F, LF, Type<G, A>>,
    predicate: Predicate<A>
  ) => Separated<Type2<F, LF, Type<G, A>>, Type2<F, LF, Type<G, A>>>
  readonly filterMap: <LF, A, B>(fa: Type2<F, LF, Type<G, A>>, f: (a: A) => Option<B>) => Type2<F, LF, Type<G, B>>
  readonly filter: <LF, A>(fa: Type2<F, LF, Type<G, A>>, predicate: Predicate<A>) => Type2<F, LF, Type<G, A>>
}

export interface FilterableComposition2C1<F extends URIS2, G extends URIS, LF>
  extends FunctorComposition21<F, G>,
    CompactableComposition21<F, G> {
  readonly partitionMap: <RL, RR, A>(
    fa: Type2<F, LF, Type<G, A>>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type2<F, LF, Type<G, RL>>, Type2<F, LF, Type<G, RR>>>
  readonly partition: <A>(
    fa: Type2<F, LF, Type<G, A>>,
    predicate: Predicate<A>
  ) => Separated<Type2<F, LF, Type<G, A>>, Type2<F, LF, Type<G, A>>>
  readonly filterMap: <A, B>(fa: Type2<F, LF, Type<G, A>>, f: (a: A) => Option<B>) => Type2<F, LF, Type<G, B>>
  readonly filter: <A>(fa: Type2<F, LF, Type<G, A>>, predicate: Predicate<A>) => Type2<F, LF, Type<G, A>>
}

export interface FilterableComposition22<F extends URIS2, G extends URIS2>
  extends FunctorComposition22<F, G>,
    CompactableComposition22<F, G> {
  readonly partitionMap: <LF, LG, RL, RR, A>(
    fa: Type2<F, LF, Type2<G, LG, A>>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type2<F, LF, Type2<G, LG, RL>>, Type2<F, LF, Type2<G, LG, RR>>>
  readonly partition: <LF, LG, A>(
    fa: Type2<F, LF, Type2<G, LG, A>>,
    predicate: Predicate<A>
  ) => Separated<Type2<F, LF, Type2<G, LG, A>>, Type2<F, LF, Type2<G, LG, A>>>
  readonly filterMap: <LF, LG, A, B>(
    fa: Type2<F, LF, Type2<G, LG, A>>,
    f: (a: A) => Option<B>
  ) => Type2<F, LF, Type2<G, LG, B>>
  readonly filter: <LF, LG, A>(
    fa: Type2<F, LF, Type2<G, LG, A>>,
    predicate: Predicate<A>
  ) => Type2<F, LF, Type2<G, LG, A>>
}

export interface FilterableComposition22C<F extends URIS2, G extends URIS2, LG>
  extends FunctorComposition22<F, G>,
    CompactableComposition22<F, G> {
  readonly partitionMap: <LF, RL, RR, A>(
    fa: Type2<F, LF, Type2<G, LG, A>>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type2<F, LF, Type2<G, LG, RL>>, Type2<F, LF, Type2<G, LG, RR>>>
  readonly partition: <LF, A>(
    fa: Type2<F, LF, Type2<G, LG, A>>,
    predicate: Predicate<A>
  ) => Separated<Type2<F, LF, Type2<G, LG, A>>, Type2<F, LF, Type2<G, LG, A>>>
  readonly filterMap: <LF, A, B>(
    fa: Type2<F, LF, Type2<G, LG, A>>,
    f: (a: A) => Option<B>
  ) => Type2<F, LF, Type2<G, LG, B>>
  readonly filter: <LF, A>(fa: Type2<F, LF, Type2<G, LG, A>>, predicate: Predicate<A>) => Type2<F, LF, Type2<G, LG, A>>
}

export interface FilterableComposition3C1<F extends URIS3, G extends URIS, UF, LF>
  extends FunctorComposition3C1<F, G, UF, LF>,
    CompactableComposition3C1<F, G, UF, LF> {
  readonly partitionMap: <RL, RR, A>(
    fa: Type3<F, UF, LF, Type<G, A>>,
    f: (a: A) => Either<RL, RR>
  ) => Separated<Type3<F, UF, LF, Type<G, RL>>, Type3<F, UF, LF, Type<G, RR>>>
  readonly partition: <A>(
    fa: Type3<F, UF, LF, Type<G, A>>,
    predicate: Predicate<A>
  ) => Separated<Type3<F, UF, LF, Type<G, A>>, Type3<F, UF, LF, Type<G, A>>>
  readonly filterMap: <A, B>(fa: Type3<F, UF, LF, Type<G, A>>, f: (a: A) => Option<B>) => Type3<F, UF, LF, Type<G, B>>
  readonly filter: <A>(fa: Type3<F, UF, LF, Type<G, A>>, predicate: Predicate<A>) => Type3<F, UF, LF, Type<G, A>>
}

/**
 * @since 1.12.0
 */
export function getFilterableComposition<F extends URIS3, G extends URIS, UF, LF>(
  F: Functor3C<F, UF, LF>,
  G: Filterable1<G>
): FilterableComposition3C1<F, G, UF, LF>
export function getFilterableComposition<F extends URIS2, G extends URIS2, LG>(
  F: Functor2<F>,
  G: Filterable2C<G, LG>
): FilterableComposition22C<F, G, LG>
export function getFilterableComposition<F extends URIS2, G extends URIS2>(
  F: Functor2<F>,
  G: Filterable2<G>
): FilterableComposition22<F, G>
export function getFilterableComposition<F extends URIS2, G extends URIS, LF>(
  F: Functor2C<F, LF>,
  G: Filterable1<G>
): FilterableComposition2C1<F, G, LF>
export function getFilterableComposition<F extends URIS2, G extends URIS>(
  F: Functor2<F>,
  G: Filterable1<G>
): FilterableComposition21<F, G>
export function getFilterableComposition<F extends URIS, G extends URIS2, LG>(
  F: Functor1<F>,
  G: Filterable2C<G, LG>
): FilterableComposition12C<F, G, LG>
export function getFilterableComposition<F extends URIS, G extends URIS2>(
  F: Functor1<F>,
  G: Filterable2<G>
): FilterableComposition12<F, G>
export function getFilterableComposition<F extends URIS, G extends URIS>(
  F: Functor1<F>,
  G: Filterable1<G>
): FilterableComposition11<F, G>
export function getFilterableComposition<F, G>(F: Functor<F>, G: Filterable<G>): FilterableComposition<F, G>
export function getFilterableComposition<F, G>(F: Functor<F>, G: Filterable<G>): FilterableComposition<F, G> {
  const FC: FilterableComposition<F, G> = {
    ...getCompactableComposition(F, G),
    partitionMap: (fga, f) => {
      const left = FC.filterMap(fga, a => f(a).fold(some, () => none))
      const right = FC.filterMap(fga, a => f(a).fold(() => none, some))
      return { left, right }
    },
    partition: (fga, p) => {
      const left = FC.filter(fga, a => !p(a))
      const right = FC.filter(fga, p)
      return { left, right }
    },
    filterMap: (fga, f) => F.map(fga, ga => G.filterMap(ga, f)),
    filter: (fga, f) => F.map(fga, ga => G.filter(ga, f))
  }
  return FC
}

/**
 * @file A `Foldable` with an additional index.
 * A `FoldableWithIndex` instance must be compatible with its `Foldable` instance
 *
 * ```ts
 * reduce(fa, b, f) = reduceWithIndex(fa, b, (_, b, a) => f(b, a))
 * foldMap(M)(fa, f) = foldMapWithIndex(M)(fa, (_, a) => f(a))
 * foldr(fa, b, f) = foldrWithIndex(fa, b, (_, a, b) => f(a, b))
 * ```
 */
import {
  Foldable2v,
  Foldable2v1,
  Foldable2v2,
  Foldable2v2C,
  Foldable2v3,
  Foldable2v3C,
  Foldable2vComposition,
  getFoldableComposition,
  Foldable2vComposition11,
  Foldable2vComposition12,
  Foldable2vComposition12C,
  Foldable2vComposition21,
  Foldable2vComposition2C1,
  Foldable2vComposition22,
  Foldable2vComposition22C,
  Foldable2vComposition3C1
} from './Foldable2v.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monoid }  from  './Monoid.ts'

/**
 * @since 1.12.0
 */
export interface FoldableWithIndex<F, I> extends Foldable2v<F> {
  readonly reduceWithIndex: <A, B>(fa: HKT<F, A>, b: B, f: (i: I, b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(M: Monoid<M>) => <A>(fa: HKT<F, A>, f: (i: I, a: A) => M) => M
  readonly foldrWithIndex: <A, B>(fa: HKT<F, A>, b: B, f: (i: I, a: A, b: B) => B) => B
}

export interface FoldableWithIndex1<F extends URIS, I> extends Foldable2v1<F> {
  readonly reduceWithIndex: <A, B>(fa: Type<F, A>, b: B, f: (i: I, b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(M: Monoid<M>) => <A>(fa: Type<F, A>, f: (i: I, a: A) => M) => M
  readonly foldrWithIndex: <A, B>(fa: Type<F, A>, b: B, f: (i: I, a: A, b: B) => B) => B
}

export interface FoldableWithIndex2<F extends URIS2, I> extends Foldable2v2<F> {
  readonly reduceWithIndex: <L, A, B>(fa: Type2<F, L, A>, b: B, f: (i: I, b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(M: Monoid<M>) => <L, A>(fa: Type2<F, L, A>, f: (i: I, a: A) => M) => M
  readonly foldrWithIndex: <L, A, B>(fa: Type2<F, L, A>, b: B, f: (i: I, a: A, b: B) => B) => B
}

export interface FoldableWithIndex3<F extends URIS3, I> extends Foldable2v3<F> {
  readonly reduceWithIndex: <U, L, A, B>(fa: Type3<F, U, L, A>, b: B, f: (i: I, b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(M: Monoid<M>) => <U, L, A>(fa: Type3<F, U, L, A>, f: (i: I, a: A) => M) => M
  readonly foldrWithIndex: <U, L, A, B>(fa: Type3<F, U, L, A>, b: B, f: (i: I, a: A, b: B) => B) => B
}

export interface FoldableWithIndex2C<F extends URIS2, I, L> extends Foldable2v2C<F, L> {
  readonly reduceWithIndex: <A, B>(fa: Type2<F, L, A>, b: B, f: (i: I, b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(M: Monoid<M>) => <A>(fa: Type2<F, L, A>, f: (i: I, a: A) => M) => M
  readonly foldrWithIndex: <A, B>(fa: Type2<F, L, A>, b: B, f: (i: I, a: A, b: B) => B) => B
}

export interface FoldableWithIndex3C<F extends URIS3, I, U, L> extends Foldable2v3C<F, U, L> {
  readonly reduceWithIndex: <A, B>(fa: Type3<F, U, L, A>, b: B, f: (i: I, b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(M: Monoid<M>) => <A>(fa: Type3<F, U, L, A>, f: (i: I, a: A) => M) => M
  readonly foldrWithIndex: <A, B>(fa: Type3<F, U, L, A>, b: B, f: (i: I, a: A, b: B) => B) => B
}

export interface FoldableWithIndexComposition<F, FI, G, GI> extends Foldable2vComposition<F, G> {
  readonly reduceWithIndex: <A, B>(fga: HKT<F, HKT<G, A>>, b: B, f: (i: [FI, GI], b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(M: Monoid<M>) => <A>(fga: HKT<F, HKT<G, A>>, f: (i: [FI, GI], a: A) => M) => M
  readonly foldrWithIndex: <A, B>(fga: HKT<F, HKT<G, A>>, b: B, f: (i: [FI, GI], a: A, b: B) => B) => B
}

export interface FoldableWithIndexComposition11<F extends URIS, FI, G extends URIS, GI>
  extends Foldable2vComposition11<F, G> {
  readonly reduceWithIndex: <A, B>(fga: Type<F, Type<G, A>>, b: B, f: (i: [FI, GI], b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(M: Monoid<M>) => <A>(fga: Type<F, Type<G, A>>, f: (i: [FI, GI], a: A) => M) => M
  readonly foldrWithIndex: <A, B>(fga: Type<F, Type<G, A>>, b: B, f: (i: [FI, GI], a: A, b: B) => B) => B
}

export interface FoldableWithIndexComposition12<F extends URIS, FI, G extends URIS2, GI>
  extends Foldable2vComposition12<F, G> {
  readonly reduceWithIndex: <LG, A, B>(fga: Type<F, Type2<G, LG, A>>, b: B, f: (i: [FI, GI], b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(
    M: Monoid<M>
  ) => <LG, A>(fga: Type<F, Type2<G, LG, A>>, f: (i: [FI, GI], a: A) => M) => M
  readonly foldrWithIndex: <LG, A, B>(fga: Type<F, Type2<G, LG, A>>, b: B, f: (i: [FI, GI], a: A, b: B) => B) => B
}

export interface FoldableWithIndexComposition12C<F extends URIS, FI, G extends URIS2, GI, LG>
  extends Foldable2vComposition12C<F, G, LG> {
  readonly reduceWithIndex: <A, B>(fga: Type<F, Type2<G, LG, A>>, b: B, f: (i: [FI, GI], b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(M: Monoid<M>) => <A>(fga: Type<F, Type2<G, LG, A>>, f: (i: [FI, GI], a: A) => M) => M
  readonly foldrWithIndex: <A, B>(fga: Type<F, Type2<G, LG, A>>, b: B, f: (i: [FI, GI], a: A, b: B) => B) => B
}

export interface FoldableWithIndexComposition21<F extends URIS2, FI, G extends URIS, GI>
  extends Foldable2vComposition21<F, G> {
  readonly reduceWithIndex: <LF, A, B>(fga: Type2<F, LF, Type<G, A>>, b: B, f: (i: [FI, GI], b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(
    M: Monoid<M>
  ) => <LF, A>(fga: Type2<F, LF, Type<G, A>>, f: (i: [FI, GI], a: A) => M) => M
  readonly foldrWithIndex: <LF, A, B>(fga: Type2<F, LF, Type<G, A>>, b: B, f: (i: [FI, GI], a: A, b: B) => B) => B
}

export interface FoldableWithIndexComposition2C1<F extends URIS2, FI, G extends URIS, GI, LF>
  extends Foldable2vComposition2C1<F, G, LF> {
  readonly reduceWithIndex: <A, B>(fga: Type2<F, LF, Type<G, A>>, b: B, f: (i: [FI, GI], b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(M: Monoid<M>) => <A>(fga: Type2<F, LF, Type<G, A>>, f: (i: [FI, GI], a: A) => M) => M
  readonly foldrWithIndex: <A, B>(fga: Type2<F, LF, Type<G, A>>, b: B, f: (i: [FI, GI], a: A, b: B) => B) => B
}

export interface FoldableWithIndexComposition22<F extends URIS2, FI, G extends URIS2, GI>
  extends Foldable2vComposition22<F, G> {
  readonly reduceWithIndex: <LF, LG, A, B>(
    fga: Type2<F, LF, Type2<G, LG, A>>,
    b: B,
    f: (i: [FI, GI], b: B, a: A) => B
  ) => B
  readonly foldMapWithIndex: <M>(
    M: Monoid<M>
  ) => <LF, LG, A>(fga: Type2<F, LF, Type2<G, LG, A>>, f: (i: [FI, GI], a: A) => M) => M
  readonly foldrWithIndex: <LF, LG, A, B>(
    fga: Type2<F, LF, Type2<G, LG, A>>,
    b: B,
    f: (i: [FI, GI], a: A, b: B) => B
  ) => B
}

export interface FoldableWithIndexComposition22C<F extends URIS2, FI, G extends URIS2, GI, LG>
  extends Foldable2vComposition22C<F, G, LG> {
  readonly reduceWithIndex: <LF, A, B>(fga: Type2<F, LF, Type2<G, LG, A>>, b: B, f: (i: [FI, GI], b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(
    M: Monoid<M>
  ) => <LF, A>(fga: Type2<F, LF, Type2<G, LG, A>>, f: (i: [FI, GI], a: A) => M) => M
  readonly foldrWithIndex: <LF, A, B>(fga: Type2<F, LF, Type2<G, LG, A>>, b: B, f: (i: [FI, GI], a: A, b: B) => B) => B
}

export interface FoldableWithIndexComposition3C1<F extends URIS3, FI, G extends URIS, GI, UF, LF>
  extends Foldable2vComposition3C1<F, G, UF, LF> {
  readonly reduceWithIndex: <A, B>(fga: Type3<F, UF, LF, Type<G, A>>, b: B, f: (i: [FI, GI], b: B, a: A) => B) => B
  readonly foldMapWithIndex: <M>(
    M: Monoid<M>
  ) => <A>(fga: Type3<F, UF, LF, Type<G, A>>, f: (i: [FI, GI], a: A) => M) => M
  readonly foldrWithIndex: <A, B>(fga: Type3<F, UF, LF, Type<G, A>>, b: B, f: (i: [FI, GI], a: A, b: B) => B) => B
}

/**
 * @since 1.12.0
 */
export function getFoldableWithIndexComposition<F extends URIS3, FI, G extends URIS, GI, UF, LF>(
  F: FoldableWithIndex3C<F, FI, UF, LF>,
  G: FoldableWithIndex1<G, GI>
): FoldableWithIndexComposition3C1<F, FI, G, GI, UF, LF>
export function getFoldableWithIndexComposition<F extends URIS2, FI, G extends URIS2, GI, LG>(
  F: FoldableWithIndex2<F, FI>,
  G: FoldableWithIndex2C<G, GI, LG>
): FoldableWithIndexComposition22C<F, FI, G, GI, LG>
export function getFoldableWithIndexComposition<F extends URIS2, FI, G extends URIS2, GI>(
  F: FoldableWithIndex2<F, FI>,
  G: FoldableWithIndex2<G, GI>
): FoldableWithIndexComposition22<F, FI, G, GI>
export function getFoldableWithIndexComposition<F extends URIS2, FI, G extends URIS, GI, LF>(
  F: FoldableWithIndex2C<F, FI, LF>,
  G: FoldableWithIndex1<G, GI>
): FoldableWithIndexComposition2C1<F, FI, G, GI, LF>
export function getFoldableWithIndexComposition<F extends URIS2, FI, G extends URIS, GI>(
  F: FoldableWithIndex2<F, FI>,
  G: FoldableWithIndex1<G, GI>
): FoldableWithIndexComposition21<F, FI, G, GI>
export function getFoldableWithIndexComposition<F extends URIS, FI, G extends URIS2, GI>(
  F: FoldableWithIndex1<F, FI>,
  G: FoldableWithIndex2<G, GI>
): FoldableWithIndexComposition12<F, FI, G, GI>
export function getFoldableWithIndexComposition<F extends URIS, FI, G extends URIS2, GI>(
  F: FoldableWithIndex1<F, FI>,
  G: FoldableWithIndex2<G, GI>
): FoldableWithIndexComposition12<F, FI, G, GI>
export function getFoldableWithIndexComposition<F extends URIS, FI, G extends URIS, GI>(
  F: FoldableWithIndex1<F, FI>,
  G: FoldableWithIndex1<G, GI>
): FoldableWithIndexComposition11<F, FI, G, GI>
export function getFoldableWithIndexComposition<F, FI, G, GI>(
  F: FoldableWithIndex<F, FI>,
  G: FoldableWithIndex<G, GI>
): FoldableWithIndexComposition<F, FI, G, GI>
export function getFoldableWithIndexComposition<F, FI, G, GI>(
  F: FoldableWithIndex<F, FI>,
  G: FoldableWithIndex<G, GI>
): FoldableWithIndexComposition<F, FI, G, GI> {
  return {
    ...getFoldableComposition(F, G),
    reduceWithIndex: (fga, b, f) =>
      F.reduceWithIndex(fga, b, (fi, b, ga) => G.reduceWithIndex(ga, b, (gi, b, a) => f([fi, gi], b, a))),
    foldMapWithIndex: M => {
      const foldMapWithIndexF = F.foldMapWithIndex(M)
      const foldMapWithIndexG = G.foldMapWithIndex(M)
      return (fga, f) => foldMapWithIndexF(fga, (fi, ga) => foldMapWithIndexG(ga, (gi, a) => f([fi, gi], a)))
    },
    foldrWithIndex: (fga, b, f) =>
      F.foldrWithIndex(fga, b, (fi, ga, b) => G.foldrWithIndex(ga, b, (gi, a, b) => f([fi, gi], a, b)))
  }
}

import { HKT }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export const identity = <A>(a: A): A => {
  return a
}

/**
 * @since 1.0.0
 */
export const unsafeCoerce: <A, B>(a: A) => B = identity as any

/**
 * Thunk type
 */
export type Lazy<A> = () => A

/**
 * @example
 * import { FunctionN }  from  'fp-ts/lib/function.ts'
 *
 * export const sum: FunctionN<[number, number], number> = (a, b) => a + b
 *
 * @since 1.16.0
 */
export type FunctionN<A extends Array<unknown>, B> = (...args: A) => B

export type Function1<A, B> = (a: A) => B
export type Function2<A, B, C> = (a: A, b: B) => C
export type Function3<A, B, C, D> = (a: A, b: B, c: C) => D
export type Function4<A, B, C, D, E> = (a: A, b: B, c: C, d: D) => E
export type Function5<A, B, C, D, E, F> = (a: A, b: B, c: C, d: D, e: E) => F
export type Function6<A, B, C, D, E, F, G> = (a: A, b: B, c: C, d: D, e: E, f: F) => G
export type Function7<A, B, C, D, E, F, G, H> = (a: A, b: B, c: C, d: D, e: E, f: F, g: G) => H
export type Function8<A, B, C, D, E, F, G, H, I> = (a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H) => I
export type Function9<A, B, C, D, E, F, G, H, I, J> = (a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I) => J

export type Curried2<A, B, C> = (a: A) => (b: B) => C
export type Curried3<A, B, C, D> = (a: A) => (b: B) => (c: C) => D
export type Curried4<A, B, C, D, E> = (a: A) => (b: B) => (c: C) => (d: D) => E
export type Curried5<A, B, C, D, E, F> = (a: A) => (b: B) => (c: C) => (d: D) => (e: E) => F
export type Curried6<A, B, C, D, E, F, G> = (a: A) => (b: B) => (c: C) => (d: D) => (e: E) => (f: F) => G
export type Curried7<A, B, C, D, E, F, G, H> = (a: A) => (b: B) => (c: C) => (d: D) => (e: E) => (f: F) => (g: G) => H
export type Curried8<A, B, C, D, E, F, G, H, I> = (
  a: A
) => (b: B) => (c: C) => (d: D) => (e: E) => (f: F) => (g: G) => (h: H) => I
export type Curried9<A, B, C, D, E, F, G, H, I, J> = (
  a: A
) => (b: B) => (c: C) => (d: D) => (e: E) => (f: F) => (g: G) => (h: H) => (i: I) => J

export type Predicate<A> = (a: A) => boolean

export type Refinement<A, B extends A> = (a: A) => a is B

/**
 * @since 1.0.0
 */
export const not = <A>(predicate: Predicate<A>): Predicate<A> => {
  return a => !predicate(a)
}

/**
 * @since 1.0.0
 */
export function or<A, B1 extends A, B2 extends A>(p1: Refinement<A, B1>, p2: Refinement<A, B2>): Refinement<A, B1 | B2>
export function or<A>(p1: Predicate<A>, p2: Predicate<A>): Predicate<A>
export function or<A>(p1: Predicate<A>, p2: Predicate<A>): Predicate<A> {
  return a => p1(a) || p2(a)
}

/**
 * @since 1.0.0
 */
export const and = <A>(p1: Predicate<A>, p2: Predicate<A>): Predicate<A> => {
  return a => p1(a) && p2(a)
}

export type Endomorphism<A> = (a: A) => A

export type BinaryOperation<A, B> = (a1: A, a2: A) => B

export type Kleisli<F, A, B> = (a: A) => HKT<F, B>
export type Cokleisli<F, A, B> = (fa: HKT<F, A>) => B

/**
 * @since 1.0.0
 */
export const constant = <A>(a: A): Lazy<A> => {
  return () => a
}

/**
 * A thunk that returns always `true`
 *
 * @since 1.0.0
 */
export const constTrue = (): boolean => {
  return true
}

/**
 * A thunk that returns always `false`
 *
 * @since 1.0.0
 */
export const constFalse = (): boolean => {
  return false
}

/**
 * A thunk that returns always `null`
 *
 * @since 1.0.0
 */
export const constNull = (): null => {
  return null
}

/**
 * A thunk that returns always `undefined`
 *
 * @since 1.0.0
 */
export const constUndefined = (): undefined => {
  return
}

/**
 * A thunk that returns always `void`
 *
 * @since 1.14.0
 */
export const constVoid = (): void => {
  return
}

/**
 * Flips the order of the arguments to a function of two arguments.
 *
 * @since 1.0.0
 */
export const flip = <A, B, C>(f: Curried2<A, B, C>): Curried2<B, A, C> => {
  return b => a => f(a)(b)
}

/**
 * The `on` function is used to change the domain of a binary operator.
 *
 * @since 1.0.0
 */
export const on = <B, C>(op: BinaryOperation<B, C>) => <A>(f: (a: A) => B): BinaryOperation<A, C> => {
  return (x, y) => op(f(x), f(y))
}

/**
 * @since 1.0.0
 */
export function compose<A, B, C>(bc: (b: B) => C, ab: (a: A) => B): (a: A) => C
export function compose<A, B, C, D>(cd: (c: C) => D, bc: (b: B) => C, ab: (a: A) => B): (a: A) => D
export function compose<A, B, C, D, E>(de: (d: D) => E, cd: (c: C) => D, bc: (b: B) => C, ab: (a: A) => B): (a: A) => E
export function compose<A, B, C, D, E, F>(
  ef: (e: E) => F,
  de: (d: D) => E,
  cd: (c: C) => D,
  bc: (b: B) => C,
  ab: (a: A) => B
): (a: A) => F
export function compose<A, B, C, D, E, F, G>(
  fg: (f: F) => G,
  ef: (e: E) => F,
  de: (d: D) => E,
  cd: (c: C) => D,
  bc: (b: B) => C,
  ab: (a: A) => B
): (a: A) => G
export function compose<A, B, C, D, E, F, G, H>(
  gh: (g: G) => H,
  fg: (f: F) => G,
  ef: (e: E) => F,
  de: (d: D) => E,
  cd: (c: C) => D,
  bc: (b: B) => C,
  ab: (a: A) => B
): (a: A) => H
export function compose<A, B, C, D, E, F, G, H, I>(
  hi: (h: H) => I,
  gh: (g: G) => H,
  fg: (f: F) => G,
  ef: (e: E) => F,
  de: (d: D) => E,
  cd: (c: C) => D,
  bc: (b: B) => C,
  ab: (a: A) => B
): (a: A) => I
export function compose<A, B, C, D, E, F, G, H, I, J>(
  ij: (i: I) => J,
  hi: (h: H) => I,
  gh: (g: G) => H,
  fg: (f: F) => G,
  ef: (e: E) => F,
  de: (d: D) => E,
  cd: (c: C) => D,
  bc: (b: B) => C,
  ab: (a: A) => B
): (a: A) => J
export function compose(...fns: Array<Function>): Function {
  const len = fns.length - 1
  return function(this: any, x: any) {
    let y = x
    for (let i = len; i > -1; i--) {
      y = fns[i].call(this, y)
    }
    return y
  }
}

/**
 * @since 1.0.0
 */
export function pipe<A, B, C>(ab: (a: A) => B, bc: (b: B) => C): (a: A) => C
export function pipe<A, B, C, D>(ab: (a: A) => B, bc: (b: B) => C, cd: (c: C) => D): (a: A) => D
export function pipe<A, B, C, D, E>(ab: (a: A) => B, bc: (b: B) => C, cd: (c: C) => D, de: (d: D) => E): (a: A) => E
export function pipe<A, B, C, D, E, F>(
  ab: (a: A) => B,
  bc: (b: B) => C,
  cd: (c: C) => D,
  de: (d: D) => E,
  ef: (e: E) => F
): (a: A) => F
export function pipe<A, B, C, D, E, F, G>(
  ab: (a: A) => B,
  bc: (b: B) => C,
  cd: (c: C) => D,
  de: (d: D) => E,
  ef: (e: E) => F,
  fg: (f: F) => G
): (a: A) => G
export function pipe<A, B, C, D, E, F, G, H>(
  ab: (a: A) => B,
  bc: (b: B) => C,
  cd: (c: C) => D,
  de: (d: D) => E,
  ef: (e: E) => F,
  fg: (f: F) => G,
  gh: (g: G) => H
): (a: A) => H
export function pipe<A, B, C, D, E, F, G, H, I>(
  ab: (a: A) => B,
  bc: (b: B) => C,
  cd: (c: C) => D,
  de: (d: D) => E,
  ef: (e: E) => F,
  fg: (f: F) => G,
  gh: (g: G) => H,
  hi: (h: H) => I
): (a: A) => I
export function pipe<A, B, C, D, E, F, G, H, I, J>(
  ab: (a: A) => B,
  bc: (b: B) => C,
  cd: (c: C) => D,
  de: (d: D) => E,
  ef: (e: E) => F,
  fg: (f: F) => G,
  gh: (g: G) => H,
  hi: (h: H) => I,
  ij: (i: I) => J
): (a: A) => J
export function pipe(...fns: Array<Function>): Function {
  const len = fns.length - 1
  return function(this: any, x: any) {
    let y = x
    for (let i = 0; i <= len; i++) {
      y = fns[i].call(this, y)
    }
    return y
  }
}

/**
 * @since 1.0.0
 */
export const concat = <A>(x: Array<A>, y: Array<A>): Array<A> => {
  const lenx = x.length
  if (lenx === 0) {
    return y
  }
  const leny = y.length
  if (leny === 0) {
    return x
  }
  const r = Array(lenx + leny)
  for (let i = 0; i < lenx; i++) {
    r[i] = x[i]
  }
  for (let i = 0; i < leny; i++) {
    r[i + lenx] = y[i]
  }
  return r
}

/**
 * @since 1.0.0
 */
export function curried(f: Function, n: number, acc: Array<any>) {
  return function(this: any, x: any) {
    const combined = concat(acc, [x])
    return n === 0 ? f.apply(this, combined) : curried(f, n - 1, combined)
  }
}

/**
 * @since 1.0.0
 */
export function curry<A, B, C>(f: Function2<A, B, C>): Curried2<A, B, C>
export function curry<A, B, C, D>(f: Function3<A, B, C, D>): Curried3<A, B, C, D>
export function curry<A, B, C, D, E>(f: Function4<A, B, C, D, E>): Curried4<A, B, C, D, E>
export function curry<A, B, C, D, E, F>(f: Function5<A, B, C, D, E, F>): Curried5<A, B, C, D, E, F>
export function curry<A, B, C, D, E, F, G>(f: Function6<A, B, C, D, E, F, G>): Curried6<A, B, C, D, E, F, G>
export function curry<A, B, C, D, E, F, G, H>(f: Function7<A, B, C, D, E, F, G, H>): Curried7<A, B, C, D, E, F, G, H>
export function curry<A, B, C, D, E, F, G, H, I>(
  f: Function8<A, B, C, D, E, F, G, H, I>
): Curried8<A, B, C, D, E, F, G, H, I>
export function curry<A, B, C, D, E, F, G, H, I, J>(
  f: Function9<A, B, C, D, E, F, G, H, I, J>
): Curried9<A, B, C, D, E, F, G, H, I, J>
export function curry(f: Function) {
  return curried(f, f.length - 1, [])
}

/* tslint:disable-next-line */
const getFunctionName = (f: Function): string => (f as any).displayName || f.name || `<function${f.length}>`

/**
 * @since 1.0.0
 */
export const toString = (x: any): string => {
  if (typeof x === 'string') {
    return JSON.stringify(x)
  }
  if (x instanceof Date) {
    return `new Date('${x.toISOString()}')`
  }
  if (Array.isArray(x)) {
    return `[${x.map(toString).join(', ')}]`
  }
  if (typeof x === 'function') {
    return getFunctionName(x)
  }
  if (x == null) {
    return String(x)
  }
  if (typeof x.toString === 'function' && x.toString !== Object.prototype.toString) {
    return x.toString()
  }
  try {
    return JSON.stringify(x, null, 2)
  } catch (e) {
    return String(x)
  }
}

/**
 * @since 1.0.0
 */
export const tuple = <T extends Array<any>>(...t: T): T => {
  return t
}

/**
 * @since 1.0.0
 * @deprecated
 */
export const tupleCurried = <A>(a: A) => <B>(b: B): [A, B] => {
  return [a, b]
}

/**
 * Applies a function to an argument ($)
 *
 * @since 1.0.0
 */
export const apply = <A, B>(f: (a: A) => B) => (a: A): B => {
  return f(a)
}

/**
 * Applies an argument to a function (#)
 *
 * @since 1.0.0
 */
export const applyFlipped = <A>(a: A) => <B>(f: (a: A) => B): B => {
  return f(a)
}

/**
 * For use with phantom fields
 *
 * @since 1.0.0
 */
export const phantom: any = undefined

/**
 * A thunk that returns always the `identity` function.
 * For use with `applySecond` methods.
 *
 * @since 1.5.0
 */
export const constIdentity = (): (<A>(a: A) => A) => {
  return identity
}

/**
 * @since 1.9.0
 */
export const increment = (n: number): number => {
  return n + 1
}

/**
 * @since 1.9.0
 */
export const decrement = (n: number): number => {
  return n - 1
}

/**
 * @since 1.18.0
 */
export function absurd<A>(_: never): A {
  throw new Error('Called `absurd` function which should be uncallable')
}

/**
 * @file A `Functor` is a type constructor which supports a mapping operation `map`.
 *
 * `map` can be used to turn functions `a -> b` into functions `f a -> f b` whose argument and return types use the type
 * constructor `f` to represent some computational context.
 *
 * Instances must satisfy the following laws:
 *
 * 1. Identity: `F.map(fa, a => a) = fa`
 * 2. Composition: `F.map(fa, a => bc(ab(a))) = F.map(F.map(fa, ab), bc)`
 */
import { constant }  from  './function.ts'
import { HKT, Type, Type2, Type3, Type4, URIS, URIS2, URIS3, URIS4 }  from  './HKT.ts'

/**
 * @since 1.0.0
 */
export interface Functor<F> {
  readonly URI: F
  readonly map: <A, B>(fa: HKT<F, A>, f: (a: A) => B) => HKT<F, B>
}

export interface Functor1<F extends URIS> {
  readonly URI: F
  readonly map: <A, B>(fa: Type<F, A>, f: (a: A) => B) => Type<F, B>
}

export interface Functor2<F extends URIS2> {
  readonly URI: F
  readonly map: <L, A, B>(fa: Type2<F, L, A>, f: (a: A) => B) => Type2<F, L, B>
}

export interface Functor3<F extends URIS3> {
  readonly URI: F
  readonly map: <U, L, A, B>(fa: Type3<F, U, L, A>, f: (a: A) => B) => Type3<F, U, L, B>
}

export interface Functor4<F extends URIS4> {
  readonly URI: F
  readonly map: <X, U, L, A, B>(fa: Type4<F, X, U, L, A>, f: (a: A) => B) => Type4<F, X, U, L, B>
}

export interface Functor2C<F extends URIS2, L> {
  readonly URI: F
  readonly _L: L
  readonly map: <A, B>(fa: Type2<F, L, A>, f: (a: A) => B) => Type2<F, L, B>
}

export interface Functor3C<F extends URIS3, U, L> {
  readonly URI: F
  readonly _L: L
  readonly _U: U
  readonly map: <A, B>(fa: Type3<F, U, L, A>, f: (a: A) => B) => Type3<F, U, L, B>
}

export interface FunctorComposition<F, G> {
  readonly map: <A, B>(fa: HKT<F, HKT<G, A>>, f: (a: A) => B) => HKT<F, HKT<G, B>>
}

export interface FunctorComposition11<F extends URIS, G extends URIS> {
  readonly map: <A, B>(fa: Type<F, Type<G, A>>, f: (a: A) => B) => Type<F, Type<G, B>>
}

export interface FunctorComposition12<F extends URIS, G extends URIS2> {
  readonly map: <LG, A, B>(fa: Type<F, Type2<G, LG, A>>, f: (a: A) => B) => Type<F, Type2<G, LG, B>>
}

export interface FunctorComposition12C<F extends URIS, G extends URIS2, LG> {
  readonly map: <A, B>(fa: Type<F, Type2<G, LG, A>>, f: (a: A) => B) => Type<F, Type2<G, LG, B>>
}

export interface FunctorComposition21<F extends URIS2, G extends URIS> {
  readonly map: <LF, A, B>(fa: Type2<F, LF, Type<G, A>>, f: (a: A) => B) => Type2<F, LF, Type<G, B>>
}

export interface FunctorComposition2C1<F extends URIS2, G extends URIS, LF> {
  readonly map: <A, B>(fa: Type2<F, LF, Type<G, A>>, f: (a: A) => B) => Type2<F, LF, Type<G, B>>
}

export interface FunctorComposition22<F extends URIS2, G extends URIS2> {
  readonly map: <LF, LG, A, B>(fa: Type2<F, LF, Type2<G, LG, A>>, f: (a: A) => B) => Type2<F, LF, Type2<G, LG, B>>
}

export interface FunctorComposition22C<F extends URIS2, G extends URIS2, LG> {
  readonly map: <LF, A, B>(fa: Type2<F, LF, Type2<G, LG, A>>, f: (a: A) => B) => Type2<F, LF, Type2<G, LG, B>>
}

export interface FunctorComposition3C1<F extends URIS3, G extends URIS, UF, LF> {
  readonly map: <A, B>(fa: Type3<F, UF, LF, Type<G, A>>, f: (a: A) => B) => Type3<F, UF, LF, Type<G, B>>
}

/**
 * Lift a function of one argument to a function which accepts and returns values wrapped with the type constructor `F`
 *
 * @since 1.0.0
 */
export function lift<F extends URIS3>(
  F: Functor3<F>
): <A, B>(f: (a: A) => B) => <U, L>(fa: Type3<F, U, L, A>) => Type3<F, U, L, B>
export function lift<F extends URIS3, U, L>(
  F: Functor3C<F, U, L>
): <A, B>(f: (a: A) => B) => (fa: Type3<F, U, L, A>) => Type3<F, U, L, B>
export function lift<F extends URIS2>(
  F: Functor2<F>
): <A, B>(f: (a: A) => B) => <L>(fa: Type2<F, L, A>) => Type2<F, L, B>
export function lift<F extends URIS2, L>(
  F: Functor2C<F, L>
): <A, B>(f: (a: A) => B) => (fa: Type2<F, L, A>) => Type2<F, L, B>
export function lift<F extends URIS>(F: Functor1<F>): <A, B>(f: (a: A) => B) => (fa: Type<F, A>) => Type<F, B>
export function lift<F>(F: Functor<F>): <A, B>(f: (a: A) => B) => (fa: HKT<F, A>) => HKT<F, B>
export function lift<F>(F: Functor<F>): <A, B>(f: (a: A) => B) => (fa: HKT<F, A>) => HKT<F, B> {
  return f => fa => F.map(fa, f)
}

/**
 * Ignore the return value of a computation, using the specified return value instead (`<$`)
 *
 * @since 1.0.0
 */
export function voidRight<F extends URIS3>(
  F: Functor3<F>
): <U, L, A, B>(a: A, fb: Type3<F, U, L, B>) => Type3<F, U, L, A>
export function voidRight<F extends URIS3, U, L>(
  F: Functor3C<F, U, L>
): <A, B>(a: A, fb: Type3<F, U, L, B>) => Type3<F, U, L, A>
export function voidRight<F extends URIS2>(F: Functor2<F>): <L, A, B>(a: A, fb: Type2<F, L, B>) => Type2<F, L, A>
export function voidRight<F extends URIS2, L>(F: Functor2C<F, L>): <A, B>(a: A, fb: Type2<F, L, B>) => Type2<F, L, A>
export function voidRight<F extends URIS>(F: Functor1<F>): <A, B>(a: A, fb: Type<F, B>) => Type<F, A>
export function voidRight<F>(F: Functor<F>): <A, B>(a: A, fb: HKT<F, B>) => HKT<F, A>
export function voidRight<F>(F: Functor<F>): <A, B>(a: A, fb: HKT<F, B>) => HKT<F, A> {
  return (a, fb) => F.map(fb, constant(a))
}

/**
 * A version of `voidRight` with its arguments flipped (`$>`)
 *
 * @since 1.0.0
 */
export function voidLeft<F extends URIS3>(
  F: Functor3<F>
): <U, L, A, B>(fa: Type3<F, U, L, A>, b: B) => Type3<F, U, L, B>
export function voidLeft<F extends URIS3, U, L>(
  F: Functor3C<F, U, L>
): <A, B>(fa: Type3<F, U, L, A>, b: B) => Type3<F, U, L, B>
export function voidLeft<F extends URIS2>(F: Functor2<F>): <L, A, B>(fa: Type2<F, L, A>, b: B) => Type2<F, L, B>
export function voidLeft<F extends URIS2, L>(F: Functor2C<F, L>): <A, B>(fa: Type2<F, L, A>, b: B) => Type2<F, L, B>
export function voidLeft<F extends URIS>(F: Functor1<F>): <A, B>(fa: Type<F, A>, b: B) => Type<F, B>
export function voidLeft<F>(F: Functor<F>): <A, B>(fa: HKT<F, A>, b: B) => HKT<F, B>
export function voidLeft<F>(F: Functor<F>): <A, B>(fa: HKT<F, A>, b: B) => HKT<F, B> {
  return (fa, b) => F.map(fa, constant(b))
}

/**
 * Apply a value in a computational context to a value in no context. Generalizes `flip`
 *
 * @since 1.0.0
 */
export function flap<F extends URIS3>(
  functor: Functor3<F>
): <U, L, A, B>(a: A, ff: Type3<F, U, L, (a: A) => B>) => Type3<F, U, L, B>
export function flap<F extends URIS3, U, L>(
  functor: Functor3C<F, U, L>
): <A, B>(a: A, ff: Type3<F, U, L, (a: A) => B>) => Type3<F, U, L, B>
export function flap<F extends URIS2>(
  functor: Functor2<F>
): <L, A, B>(a: A, ff: Type2<F, L, (a: A) => B>) => Type2<F, L, B>
export function flap<F extends URIS2, L>(
  functor: Functor2C<F, L>
): <A, B>(a: A, ff: Type2<F, L, (a: A) => B>) => Type2<F, L, B>
export function flap<F extends URIS>(functor: Functor1<F>): <A, B>(a: A, ff: Type<F, (a: A) => B>) => Type<F, B>
export function flap<F>(functor: Functor<F>): <A, B>(a: A, ff: HKT<F, (a: A) => B>) => HKT<F, B>
export function flap<F>(functor: Functor<F>): <A, B>(a: A, ff: HKT<F, (a: A) => B>) => HKT<F, B> {
  return (a, ff) => functor.map(ff, f => f(a))
}

/**
 * @since 1.0.0
 */
export function getFunctorComposition<F extends URIS3, G extends URIS, UF, LF>(
  F: Functor3C<F, UF, LF>,
  G: Functor1<G>
): FunctorComposition3C1<F, G, UF, LF>
export function getFunctorComposition<F extends URIS2, G extends URIS2, LG>(
  F: Functor2<F>,
  G: Functor2C<G, LG>
): FunctorComposition22C<F, G, LG>
export function getFunctorComposition<F extends URIS2, G extends URIS2>(
  F: Functor2<F>,
  G: Functor2<G>
): FunctorComposition22<F, G>
export function getFunctorComposition<F extends URIS2, G extends URIS, LF>(
  F: Functor2C<F, LF>,
  G: Functor1<G>
): FunctorComposition2C1<F, G, LF>
export function getFunctorComposition<F extends URIS2, G extends URIS>(
  F: Functor2<F>,
  G: Functor1<G>
): FunctorComposition21<F, G>
export function getFunctorComposition<F extends URIS, G extends URIS2, LG>(
  F: Functor1<F>,
  G: Functor2C<G, LG>
): FunctorComposition12C<F, G, LG>
export function getFunctorComposition<F extends URIS, G extends URIS2>(
  F: Functor1<F>,
  G: Functor2<G>
): FunctorComposition12<F, G>
export function getFunctorComposition<F extends URIS, G extends URIS>(
  F: Functor1<F>,
  G: Functor1<G>
): FunctorComposition11<F, G>
export function getFunctorComposition<F, G>(F: Functor<F>, G: Functor<G>): FunctorComposition<F, G>
export function getFunctorComposition<F, G>(F: Functor<F>, G: Functor<G>): FunctorComposition<F, G> {
  return {
    map: (fa, f) => F.map(fa, ga => G.map(ga, f))
  }
}

/**
 * @file Data structure which represents non-empty arrays
 */
import { Monad1 }  from  './Monad.ts'
import * as A  from  './Array.ts'
import { Comonad1 }  from  './Comonad.ts'
import { FunctorWithIndex1 }  from  './FunctorWithIndex.ts'
import { TraversableWithIndex1, TraverseWithIndex1 }  from  './TraversableWithIndex.ts'
import { FoldableWithIndex1 }  from  './FoldableWithIndex.ts'
import { Ord }  from  './Ord.ts'
import { getMeetSemigroup, getJoinSemigroup, Semigroup }  from  './Semigroup.ts'
import { Option, some, none }  from  './Option.ts'
import { Setoid }  from  './Setoid.ts'
import { compose, Predicate, Refinement }  from  './function.ts'
import { Traverse1 }  from  './Traversable.ts'
import { Sequence1 }  from  './Traversable2v.ts'
import { Show }  from  './Show.ts'

declare module './HKT.ts'
  interface URI2HKT<A> {
    NonEmptyArray2v: NonEmptyArray<A>
  }
}

export const URI = 'NonEmptyArray2v'

export type URI = typeof URI

/**
 * @since 1.15.0
 */
export interface NonEmptyArray<A> extends Array<A> {
  0: A
  map<B>(f: (a: A, index: number, nea: NonEmptyArray<A>) => B): NonEmptyArray<B>
  concat(as: Array<A>): NonEmptyArray<A>
}

/**
 * @since 1.17.0
 */
export const getShow = <A>(S: Show<A>): Show<NonEmptyArray<A>> => {
  const SA = A.getShow(S)
  return {
    show: arr => `make(${S.show(arr[0])}, ${SA.show(arr.slice(1))})`
  }
}

/**
 * Use `cons` instead
 *
 * @since 1.15.0
 * @deprecated
 */
export function make<A>(head: A, tail: Array<A>): NonEmptyArray<A> {
  return A.cons(head, tail)
}

/**
 * @since 1.15.0
 */
export function head<A>(nea: NonEmptyArray<A>): A {
  return nea[0]
}

/**
 * @since 1.15.0
 */
export function tail<A>(nea: NonEmptyArray<A>): Array<A> {
  return nea.slice(1)
}

/**
 * @since 1.17.3
 */
export const reverse: <A>(nea: NonEmptyArray<A>) => NonEmptyArray<A> = A.reverse as any

/**
 * @since 1.15.0
 */
export function min<A>(ord: Ord<A>): (nea: NonEmptyArray<A>) => A {
  const S = getMeetSemigroup(ord)
  return nea => nea.reduce(S.concat)
}

/**
 * @since 1.15.0
 */
export function max<A>(ord: Ord<A>): (nea: NonEmptyArray<A>) => A {
  const S = getJoinSemigroup(ord)
  return nea => nea.reduce(S.concat)
}

/**
 * Builds a `NonEmptyArray` from an `Array` returning `none` if `as` is an empty array
 *
 * @since 1.15.0
 */
export function fromArray<A>(as: Array<A>): Option<NonEmptyArray<A>> {
  return A.isNonEmpty(as) ? some(as) : none
}

/**
 * Builds a `NonEmptyArray` from a provably (compile time) non empty `Array`.
 *
 * @since 1.15.0
 */
export function fromNonEmptyArray<A>(as: Array<A> & { 0: A }): NonEmptyArray<A> {
  return as as any
}

/**
 * Builds a `Semigroup` instance for `NonEmptyArray`
 *
 * @since 1.15.0
 */
export const getSemigroup = <A = never>(): Semigroup<NonEmptyArray<A>> => {
  return {
    concat: (x, y) => x.concat(y)
  }
}

/**
 * @example
 * import { fromNonEmptyArray, getSetoid, make }  from  'fp-ts/lib/NonEmptyArray2v.ts'
 * import { setoidNumber }  from  'fp-ts/lib/Setoid.ts'
 *
 * const S = getSetoid(setoidNumber)
 * assert.strictEqual(S.equals(make(1, [2]), fromNonEmptyArray([1, 2])), true)
 * assert.strictEqual(S.equals(make(1, [2]), fromNonEmptyArray([1, 3])), false)
 *
 * @since 1.15.0
 */
export function getSetoid<A>(S: Setoid<A>): Setoid<NonEmptyArray<A>> {
  return A.getSetoid(S)
}

/**
 * Group equal, consecutive elements of an array into non empty arrays.
 *
 * @example
 * import { make, group }  from  'fp-ts/lib/NonEmptyArray2v.ts'
 * import { ordNumber }  from  'fp-ts/lib/Ord.ts'
 *
 * assert.deepStrictEqual(group(ordNumber)([1, 2, 1, 1]), [
 *   make(1, []),
 *   make(2, []),
 *   make(1, [1])
 * ])
 *
 * @since 1.15.0
 */
export const group = <A>(S: Setoid<A>) => (as: Array<A>): Array<NonEmptyArray<A>> => {
  const len = as.length
  if (len === 0) {
    return A.empty
  }
  const r: Array<NonEmptyArray<A>> = []
  let head: A = as[0]
  let nea = fromNonEmptyArray([head])
  for (let i = 1; i < len; i++) {
    const x = as[i]
    if (S.equals(x, head)) {
      nea.push(x)
    } else {
      r.push(nea)
      head = x
      nea = fromNonEmptyArray([head])
    }
  }
  r.push(nea)
  return r
}

/**
 * Sort and then group the elements of an array into non empty arrays.
 *
 * @example
 * import { make, groupSort }  from  'fp-ts/lib/NonEmptyArray2v.ts'
 * import { ordNumber }  from  'fp-ts/lib/Ord.ts'
 *
 * assert.deepStrictEqual(groupSort(ordNumber)([1, 2, 1, 1]), [make(1, [1, 1]), make(2, [])])
 *
 * @since 1.15.0
 */
export const groupSort = <A>(O: Ord<A>): ((as: Array<A>) => Array<NonEmptyArray<A>>) => {
  return compose(
    group(O),
    A.sort(O)
  )
}

/**
 * Splits an array into sub-non-empty-arrays stored in an object, based on the result of calling a `string`-returning
 * function on each element, and grouping the results according to values returned
 *
 * @example
 * import { make, groupBy }  from  'fp-ts/lib/NonEmptyArray2v.ts'
 *
 * assert.deepStrictEqual(groupBy(['foo', 'bar', 'foobar'], a => String(a.length)), {
 *   '3': make('foo', ['bar']),
 *   '6': make('foobar', [])
 * })
 *
 * @since 1.15.0
 */
export const groupBy = <A>(as: Array<A>, f: (a: A) => string): { [key: string]: NonEmptyArray<A> } => {
  const r: { [key: string]: NonEmptyArray<A> } = {}
  for (const a of as) {
    const k = f(a)
    if (r.hasOwnProperty(k)) {
      r[k].push(a)
    } else {
      r[k] = cons(a, [])
    }
  }
  return r
}

/**
 * @since 1.15.0
 */
export function last<A>(nea: NonEmptyArray<A>): A {
  return nea[nea.length - 1]
}

/**
 * @since 1.15.0
 */
export function sort<A>(O: Ord<A>): (nea: NonEmptyArray<A>) => NonEmptyArray<A> {
  return A.sort(O) as any
}

/**
 * @since 1.15.0
 */
export function findFirst<A, B extends A>(nea: NonEmptyArray<A>, refinement: Refinement<A, B>): Option<B>
export function findFirst<A>(nea: NonEmptyArray<A>, predicate: Predicate<A>): Option<A>
export function findFirst<A>(nea: NonEmptyArray<A>, predicate: Predicate<A>): Option<A> {
  return A.findFirst(nea, predicate)
}

/**
 * @since 1.15.0
 */
export function findLast<A, B extends A>(nea: NonEmptyArray<A>, refinement: Refinement<A, B>): Option<B>
export function findLast<A>(nea: NonEmptyArray<A>, predicate: Predicate<A>): Option<A>
export function findLast<A>(nea: NonEmptyArray<A>, predicate: Predicate<A>): Option<A> {
  return A.findLast(nea, predicate)
}

/**
 * @since 1.15.0
 */
export function findIndex<A>(nea: NonEmptyArray<A>, predicate: Predicate<A>): Option<number> {
  return A.findIndex(nea, predicate)
}

/**
 * @since 1.15.0
 */
export function findLastIndex<A>(nea: NonEmptyArray<A>, predicate: Predicate<A>): Option<number> {
  return A.findLastIndex(nea, predicate)
}

/**
 * @since 1.15.0
 */
export function insertAt<A>(i: number, a: A, nea: NonEmptyArray<A>): Option<NonEmptyArray<A>> {
  return A.insertAt(i, a, nea) as any
}

/**
 * @since 1.15.0
 */
export function updateAt<A>(i: number, a: A, nea: NonEmptyArray<A>): Option<NonEmptyArray<A>> {
  return A.updateAt(i, a, nea) as any
}

/**
 * @since 1.17.0
 */
export function modifyAt<A>(nea: NonEmptyArray<A>, i: number, f: (a: A) => A): Option<NonEmptyArray<A>> {
  return A.modifyAt(nea, i, f) as any
}

/**
 * @since 1.17.0
 */
export const copy = <A>(nea: NonEmptyArray<A>): NonEmptyArray<A> => {
  return A.copy(nea) as any
}

/**
 * @since 1.15.0
 */
export function filter<A, B extends A>(nea: NonEmptyArray<A>, refinement: Refinement<A, B>): Option<NonEmptyArray<A>>
export function filter<A>(nea: NonEmptyArray<A>, predicate: Predicate<A>): Option<NonEmptyArray<A>>
export function filter<A>(nea: NonEmptyArray<A>, predicate: Predicate<A>): Option<NonEmptyArray<A>> {
  return filterWithIndex(nea, (_, a) => predicate(a))
}

/**
 * @since 1.15.0
 */
export function filterWithIndex<A>(
  nea: NonEmptyArray<A>,
  predicate: (i: number, a: A) => boolean
): Option<NonEmptyArray<A>> {
  return fromArray(nea.filter((a, i) => predicate(i, a)))
}

const mapWithIndex = <A, B>(fa: NonEmptyArray<A>, f: (i: number, a: A) => B): NonEmptyArray<B> => {
  return fa.map((a, i) => f(i, a))
}

/**
 * Append an element to the end of an array, creating a new non empty array
 *
 * @example
 * import { snoc }  from  'fp-ts/lib/NonEmptyArray2v.ts'
 *
 * assert.deepStrictEqual(snoc([1, 2, 3], 4), [1, 2, 3, 4])
 *
 * @since 1.16.0
 */
export const snoc: <A>(as: Array<A>, a: A) => NonEmptyArray<A> = A.snoc

/**
 * Append an element to the front of an array, creating a new non empty array
 *
 * @example
 * import { cons }  from  'fp-ts/lib/NonEmptyArray2v.ts'
 *
 * assert.deepStrictEqual(cons(1, [2, 3, 4]), [1, 2, 3, 4])
 *
 * @since 1.16.0
 */
export const cons: <A>(a: A, as: Array<A>) => NonEmptyArray<A> = A.cons

/**
 * @since 1.15.0
 */
export const nonEmptyArray: Monad1<URI> &
  Comonad1<URI> &
  TraversableWithIndex1<URI, number> &
  FunctorWithIndex1<URI, number> &
  FoldableWithIndex1<URI, number> = {
  URI,
  map: A.array.map as <A, B>(fa: NonEmptyArray<A>, f: (a: A) => B) => any,
  mapWithIndex,
  of: A.array.of as <A>(a: A) => NonEmptyArray<A>,
  ap: A.array.ap as <A, B>(fab: NonEmptyArray<(a: A) => B>, fa: NonEmptyArray<A>) => any,
  chain: A.array.chain as <A, B>(fa: NonEmptyArray<A>, f: (a: A) => NonEmptyArray<B>) => any,
  extend: A.array.extend as <A, B>(ea: any, f: (fa: NonEmptyArray<A>) => B) => NonEmptyArray<B>,
  extract: head,
  reduce: A.array.reduce,
  foldMap: A.array.foldMap,
  foldr: A.array.foldr,
  traverse: A.array.traverse as Traverse1<any>,
  sequence: A.array.sequence as Sequence1<any>,
  reduceWithIndex: A.array.reduceWithIndex,
  foldMapWithIndex: A.array.foldMapWithIndex,
  foldrWithIndex: A.array.foldrWithIndex,
  traverseWithIndex: A.array.traverseWithIndex as TraverseWithIndex1<any, number>
}

import {
  Applicative,
  Applicative1,
  Applicative2,
  Applicative2C,
  Applicative3C,
  ApplicativeComposition,
  ApplicativeComposition11,
  ApplicativeComposition21,
  ApplicativeComposition2C1,
  ApplicativeComposition3C1,
  getApplicativeComposition
} from './Applicative.ts'
import { Functor, Functor1, Functor2, Functor2C, Functor3C }  from  './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monad, Monad1, Monad2, Monad2C, Monad3C }  from  './Monad.ts'
import { Option, URI, none as optionNone, option, some as optionSome }  from  './Option.ts'

export interface OptionT2v<M> extends ApplicativeComposition<M, URI> {
  readonly chain: <A, B>(fa: HKT<M, Option<A>>, f: (a: A) => HKT<M, Option<B>>) => HKT<M, Option<B>>
}

export interface OptionT2v1<M extends URIS> extends ApplicativeComposition11<M, URI> {
  readonly chain: <A, B>(fa: Type<M, Option<A>>, f: (a: A) => Type<M, Option<B>>) => Type<M, Option<B>>
}

export interface OptionT2v2<M extends URIS2> extends ApplicativeComposition21<M, URI> {
  readonly chain: <L, A, B>(fa: Type2<M, L, Option<A>>, f: (a: A) => Type2<M, L, Option<B>>) => Type2<M, L, Option<B>>
}

export interface OptionT2v2C<M extends URIS2, L> extends ApplicativeComposition2C1<M, URI, L> {
  readonly chain: <A, B>(fa: Type2<M, L, Option<A>>, f: (a: A) => Type2<M, L, Option<B>>) => Type2<M, L, Option<B>>
}

export interface OptionT2v3C<M extends URIS3, U, L> extends ApplicativeComposition3C1<M, URI, U, L> {
  readonly chain: <A, B>(
    fa: Type3<M, U, L, Option<A>>,
    f: (a: A) => Type3<M, U, L, Option<B>>
  ) => Type3<M, U, L, Option<B>>
}

/**
 * @since 1.0.0
 */
export function fold<F extends URIS3, U, L>(
  F: Functor3C<F, U, L>
): <R, A>(onNone: R, onSome: (a: A) => R, fa: Type3<F, U, L, Option<A>>) => Type3<F, U, L, R>
export function fold<F extends URIS2>(
  F: Functor2<F>
): <L, R, A>(onNone: R, onSome: (a: A) => R, fa: Type2<F, L, Option<A>>) => Type2<F, L, R>
export function fold<F extends URIS2, L>(
  F: Functor2C<F, L>
): <R, A>(onNone: R, onSome: (a: A) => R, fa: Type2<F, L, Option<A>>) => Type2<F, L, R>
export function fold<F extends URIS>(
  F: Functor1<F>
): <R, A>(onNone: R, onSome: (a: A) => R, fa: Type<F, Option<A>>) => Type<F, R>
export function fold<F>(F: Functor<F>): <R, A>(onNone: R, onSome: (a: A) => R, fa: HKT<F, Option<A>>) => HKT<F, R>
export function fold<F>(F: Functor<F>): <R, A>(onNone: R, onSome: (a: A) => R, fa: HKT<F, Option<A>>) => HKT<F, R> {
  return (onNone, onSome, fa) => F.map(fa, o => (o.isNone() ? onNone : onSome(o.value)))
}

/**
 * @since 1.14.0
 */
export function getOptionT2v<M extends URIS3, U, L>(M: Monad3C<M, U, L>): OptionT2v3C<M, U, L>
export function getOptionT2v<M extends URIS2>(M: Monad2<M>): OptionT2v2<M>
export function getOptionT2v<M extends URIS2, L>(M: Monad2C<M, L>): OptionT2v2C<M, L>
export function getOptionT2v<M extends URIS>(M: Monad1<M>): OptionT2v1<M>
export function getOptionT2v<M>(M: Monad<M>): OptionT2v<M>
export function getOptionT2v<M>(M: Monad<M>): OptionT2v<M> {
  const applicativeComposition = getApplicativeComposition(M, option)

  return {
    ...applicativeComposition,
    chain: (fa, f) => M.chain(fa, o => (o.isNone() ? M.of(optionNone) : f(o.value)))
  }
}

/** @deprecated */
export interface OptionT<M> extends ApplicativeComposition<M, URI> {
  readonly chain: <A, B>(f: (a: A) => HKT<M, Option<B>>, fa: HKT<M, Option<A>>) => HKT<M, Option<B>>
}

/** @deprecated */
export interface OptionT1<M extends URIS> extends ApplicativeComposition11<M, URI> {
  readonly chain: <A, B>(f: (a: A) => Type<M, Option<B>>, fa: Type<M, Option<A>>) => Type<M, Option<B>>
}

/** @deprecated */
export interface OptionT2<M extends URIS2> extends ApplicativeComposition21<M, URI> {
  readonly chain: <L, A, B>(f: (a: A) => Type2<M, L, Option<B>>, fa: Type2<M, L, Option<A>>) => Type2<M, L, Option<B>>
}

/** @deprecated */
export interface OptionT2C<M extends URIS2, L> extends ApplicativeComposition2C1<M, URI, L> {
  readonly chain: <A, B>(f: (a: A) => Type2<M, L, Option<B>>, fa: Type2<M, L, Option<A>>) => Type2<M, L, Option<B>>
}

/** @deprecated */
export interface OptionT3C<M extends URIS3, U, L> extends ApplicativeComposition3C1<M, URI, U, L> {
  readonly chain: <A, B>(
    f: (a: A) => Type3<M, U, L, Option<B>>,
    fa: Type3<M, U, L, Option<A>>
  ) => Type3<M, U, L, Option<B>>
}

/**
 * Use `getOptionT2v` instead
 * @since 1.0.0
 * @deprecated
 */
// tslint:disable-next-line: deprecation
export function chain<F extends URIS3, U, L>(F: Monad3C<F, U, L>): OptionT3C<F, U, L>['chain']
/** @deprecated */
// tslint:disable-next-line: deprecation
export function chain<F extends URIS2>(F: Monad2<F>): OptionT2<F>['chain']
/** @deprecated */
// tslint:disable-next-line: deprecation
export function chain<F extends URIS2, L>(F: Monad2C<F, L>): OptionT2C<F, L>['chain']
/** @deprecated */
// tslint:disable-next-line: deprecation
export function chain<F extends URIS>(F: Monad1<F>): OptionT1<F>['chain']
/** @deprecated */
// tslint:disable-next-line: deprecation
export function chain<F>(F: Monad<F>): OptionT<F>['chain']
/** @deprecated */
// tslint:disable-next-line: deprecation
export function chain<F>(F: Monad<F>): OptionT<F>['chain'] {
  return (f, fa) => F.chain(fa, o => (o.isNone() ? F.of(optionNone) : f(o.value)))
}

/**
 * Use `getOptionT2v` instead
 * @since 1.0.0
 * @deprecated
 */
// tslint:disable-next-line: deprecation
export function getOptionT<M extends URIS3, U, L>(M: Monad3C<M, U, L>): OptionT3C<M, U, L>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getOptionT<M extends URIS2>(M: Monad2<M>): OptionT2<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getOptionT<M extends URIS2, L>(M: Monad2C<M, L>): OptionT2C<M, L>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getOptionT<M extends URIS>(M: Monad1<M>): OptionT1<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getOptionT<M>(M: Monad<M>): OptionT<M>
// tslint:disable-next-line: deprecation
export function getOptionT<M>(M: Monad<M>): OptionT<M> {
  const applicativeComposition = getApplicativeComposition(M, option)

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
export function some<F extends URIS3, U, L>(F: Applicative3C<F, U, L>): <A>(a: A) => Type3<F, U, L, Option<A>>
/** @deprecated */
export function some<F extends URIS2>(F: Applicative2<F>): <L, A>(a: A) => Type2<F, L, Option<A>>
/** @deprecated */
export function some<F extends URIS2, L>(F: Applicative2C<F, L>): <A>(a: A) => Type2<F, L, Option<A>>
/** @deprecated */
export function some<F extends URIS>(F: Applicative1<F>): <A>(a: A) => Type<F, Option<A>>
/** @deprecated */
export function some<F>(F: Applicative<F>): <A>(a: A) => HKT<F, Option<A>>
/** @deprecated */
export function some<F>(F: Applicative<F>): <A>(a: A) => HKT<F, Option<A>> {
  return a => F.of(optionSome(a))
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function none<F extends URIS3, U, L>(F: Applicative3C<F, U, L>): () => Type3<F, U, L, Option<never>>
/** @deprecated */
export function none<F extends URIS2>(F: Applicative2<F>): <L>() => Type2<F, L, Option<never>>
/** @deprecated */
export function none<F extends URIS2, L>(F: Applicative2C<F, L>): () => Type2<F, L, Option<never>>
/** @deprecated */
export function none<F extends URIS>(F: Applicative1<F>): () => Type<F, Option<never>>
/** @deprecated */
export function none<F>(F: Applicative<F>): () => HKT<F, Option<never>>
/** @deprecated */
export function none<F>(F: Applicative<F>): () => HKT<F, Option<never>> {
  return () => F.of(optionNone)
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function fromOption<F extends URIS3, U, L>(
  F: Applicative3C<F, U, L>
): <A>(fa: Option<A>) => Type3<F, U, L, Option<A>>
export function fromOption<F extends URIS2>(F: Applicative2<F>): <L, A>(fa: Option<A>) => Type2<F, L, Option<A>>
/** @deprecated */
export function fromOption<F extends URIS2, L>(F: Applicative2C<F, L>): <A>(fa: Option<A>) => Type2<F, L, Option<A>>
/** @deprecated */
export function fromOption<F extends URIS>(F: Applicative1<F>): <A>(fa: Option<A>) => Type<F, Option<A>>
/** @deprecated */
export function fromOption<F>(F: Applicative<F>): <A>(fa: Option<A>) => HKT<F, Option<A>>
/** @deprecated */
export function fromOption<F>(F: Applicative<F>): <A>(fa: Option<A>) => HKT<F, Option<A>> {
  return F.of
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function liftF<F extends URIS3, U, L>(
  F: Functor3C<F, U, L>
): <A>(fa: Type3<F, U, L, A>) => Type3<F, U, L, Option<A>>
/** @deprecated */
export function liftF<F extends URIS2>(F: Functor2<F>): <L, A>(fa: Type2<F, L, A>) => Type2<F, L, Option<A>>
/** @deprecated */
export function liftF<F extends URIS2, L>(F: Functor2C<F, L>): <A>(fa: Type2<F, L, A>) => Type2<F, L, Option<A>>
/** @deprecated */
export function liftF<F extends URIS>(F: Functor1<F>): <A>(fa: Type<F, A>) => Type<F, Option<A>>
/** @deprecated */
export function liftF<F>(F: Functor<F>): <A>(fa: HKT<F, A>) => HKT<F, Option<A>>
/** @deprecated */
export function liftF<F>(F: Functor<F>): <A>(fa: HKT<F, A>) => HKT<F, Option<A>> {
  return fa => F.map(fa, optionSome)
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function getOrElse<F extends URIS3, U, L>(
  F: Functor3C<F, U, L>
): <A>(a: A) => (fa: Type3<F, U, L, Option<A>>) => Type3<F, U, L, A>
/** @deprecated */
export function getOrElse<F extends URIS2>(
  F: Functor2<F>
): <A>(a: A) => <L>(fa: Type2<F, L, Option<A>>) => Type2<F, L, A>
/** @deprecated */
export function getOrElse<F extends URIS2, L>(
  F: Functor2C<F, L>
): <A>(a: A) => (fa: Type2<F, L, Option<A>>) => Type2<F, L, A>
/** @deprecated */
export function getOrElse<F extends URIS>(F: Functor1<F>): <A>(a: A) => (fa: Type<F, Option<A>>) => Type<F, A>
/** @deprecated */
export function getOrElse<F>(F: Functor<F>): <A>(a: A) => (fa: HKT<F, Option<A>>) => HKT<F, A>
/** @deprecated */
export function getOrElse<F>(F: Functor<F>): <A>(a: A) => (fa: HKT<F, Option<A>>) => HKT<F, A> {
  return a => fa => F.map(fa, o => o.getOrElse(a))
}

import { Applicative, Applicative1, Applicative2, Applicative3 }  from  './Applicative.ts'
import { Chain, Chain1, Chain2, Chain3 }  from  './Chain.ts'
import { Functor, Functor1, Functor2, Functor3 }  from  './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monad, Monad1, Monad2, Monad3 }  from  './Monad.ts'
import { Reader }  from  './Reader.ts'

export interface ReaderT2v<M> {
  readonly map: <E, A, B>(fa: (e: E) => HKT<M, A>, f: (a: A) => B) => (e: E) => HKT<M, B>
  readonly of: <E, A>(a: A) => (e: E) => HKT<M, A>
  readonly ap: <E, A, B>(fab: (e: E) => HKT<M, (a: A) => B>, fa: (e: E) => HKT<M, A>) => (e: E) => HKT<M, B>
  readonly chain: <E, A, B>(fa: (e: E) => HKT<M, A>, f: (a: A) => (e: E) => HKT<M, B>) => (e: E) => HKT<M, B>
}

export interface ReaderT2v1<M extends URIS> {
  readonly map: <E, A, B>(fa: (e: E) => Type<M, A>, f: (a: A) => B) => (e: E) => Type<M, B>
  readonly of: <E, A>(a: A) => (e: E) => Type<M, A>
  readonly ap: <E, A, B>(fab: (e: E) => Type<M, (a: A) => B>, fa: (e: E) => Type<M, A>) => (e: E) => Type<M, B>
  readonly chain: <E, A, B>(fa: (e: E) => Type<M, A>, f: (a: A) => (e: E) => Type<M, B>) => (e: E) => Type<M, B>
}

export interface ReaderT2v2<M extends URIS2> {
  readonly map: <L, E, A, B>(fa: (e: E) => Type2<M, L, A>, f: (a: A) => B) => (e: E) => Type2<M, L, B>
  readonly of: <L, E, A>(a: A) => (e: E) => Type2<M, L, A>
  readonly ap: <L, E, A, B>(
    fab: (e: E) => Type2<M, L, (a: A) => B>,
    fa: (e: E) => Type2<M, L, A>
  ) => (e: E) => Type2<M, L, B>
  readonly chain: <L, E, A, B>(
    fa: (e: E) => Type2<M, L, A>,
    f: (a: A) => (e: E) => Type2<M, L, B>
  ) => (e: E) => Type2<M, L, B>
}

export interface ReaderT2v3<M extends URIS3> {
  readonly map: <U, L, E, A, B>(fa: (e: E) => Type3<M, U, L, A>, f: (a: A) => B) => (e: E) => Type3<M, U, L, B>
  readonly of: <U, L, E, A>(a: A) => (e: E) => Type3<M, U, L, A>
  readonly ap: <U, L, E, A, B>(
    fab: (e: E) => Type3<M, U, L, (a: A) => B>,
    fa: (e: E) => Type3<M, U, L, A>
  ) => (e: E) => Type3<M, U, L, B>
  readonly chain: <U, L, E, A, B>(
    fa: (e: E) => Type3<M, U, L, A>,
    f: (a: A) => (e: E) => Type3<M, U, L, B>
  ) => (e: E) => Type3<M, U, L, B>
}

/**
 * @since 1.2.0
 */
export function fromReader<F extends URIS3>(
  F: Applicative3<F>
): <E, U, L, A>(fa: Reader<E, A>) => (e: E) => Type3<F, U, L, A>
export function fromReader<F extends URIS2>(F: Applicative2<F>): <E, L, A>(fa: Reader<E, A>) => (e: E) => Type2<F, L, A>
export function fromReader<F extends URIS>(F: Applicative1<F>): <E, A>(fa: Reader<E, A>) => (e: E) => Type<F, A>
export function fromReader<F>(F: Applicative<F>): <E, A>(fa: Reader<E, A>) => (e: E) => HKT<F, A>
export function fromReader<F>(F: Applicative<F>): <E, A>(fa: Reader<E, A>) => (e: E) => HKT<F, A> {
  return fa => e => F.of(fa.run(e))
}

/**
 * @since 1.14.0
 */
export function getReaderT2v<M extends URIS3>(M: Monad3<M>): ReaderT2v3<M>
export function getReaderT2v<M extends URIS2>(M: Monad2<M>): ReaderT2v2<M>
export function getReaderT2v<M extends URIS>(M: Monad1<M>): ReaderT2v1<M>
export function getReaderT2v<M>(M: Monad<M>): ReaderT2v<M>
export function getReaderT2v<M>(M: Monad<M>): ReaderT2v<M> {
  return {
    map: (fa, f) => e => M.map(fa(e), f),
    of: a => () => M.of(a),
    ap: (fab, fa) => e => M.ap(fab(e), fa(e)),
    chain: (fa, f) => e => M.chain(fa(e), a => f(a)(e))
  }
}

/** @deprecated */
export interface ReaderT<M> {
  readonly map: <E, A, B>(f: (a: A) => B, fa: (e: E) => HKT<M, A>) => (e: E) => HKT<M, B>
  readonly of: <E, A>(a: A) => (e: E) => HKT<M, A>
  readonly ap: <E, A, B>(fab: (e: E) => HKT<M, (a: A) => B>, fa: (e: E) => HKT<M, A>) => (e: E) => HKT<M, B>
  readonly chain: <E, A, B>(f: (a: A) => (e: E) => HKT<M, B>, fa: (e: E) => HKT<M, A>) => (e: E) => HKT<M, B>
}

/** @deprecated */
export interface ReaderT1<M extends URIS> {
  readonly map: <E, A, B>(f: (a: A) => B, fa: (e: E) => Type<M, A>) => (e: E) => Type<M, B>
  readonly of: <E, A>(a: A) => (e: E) => Type<M, A>
  readonly ap: <E, A, B>(fab: (e: E) => Type<M, (a: A) => B>, fa: (e: E) => Type<M, A>) => (e: E) => Type<M, B>
  readonly chain: <E, A, B>(f: (a: A) => (e: E) => Type<M, B>, fa: (e: E) => Type<M, A>) => (e: E) => Type<M, B>
}

/** @deprecated */
export interface ReaderT2<M extends URIS2> {
  readonly map: <L, E, A, B>(f: (a: A) => B, fa: (e: E) => Type2<M, L, A>) => (e: E) => Type2<M, L, B>
  readonly of: <L, E, A>(a: A) => (e: E) => Type2<M, L, A>
  readonly ap: <L, E, A, B>(
    fab: (e: E) => Type2<M, L, (a: A) => B>,
    fa: (e: E) => Type2<M, L, A>
  ) => (e: E) => Type2<M, L, B>
  readonly chain: <L, E, A, B>(
    f: (a: A) => (e: E) => Type2<M, L, B>,
    fa: (e: E) => Type2<M, L, A>
  ) => (e: E) => Type2<M, L, B>
}

/** @deprecated */
export interface ReaderT3<M extends URIS3> {
  readonly map: <U, L, E, A, B>(f: (a: A) => B, fa: (e: E) => Type3<M, U, L, A>) => (e: E) => Type3<M, U, L, B>
  readonly of: <U, L, E, A>(a: A) => (e: E) => Type3<M, U, L, A>
  readonly ap: <U, L, E, A, B>(
    fab: (e: E) => Type3<M, U, L, (a: A) => B>,
    fa: (e: E) => Type3<M, U, L, A>
  ) => (e: E) => Type3<M, U, L, B>
  readonly chain: <U, L, E, A, B>(
    f: (a: A) => (e: E) => Type3<M, U, L, B>,
    fa: (e: E) => Type3<M, U, L, A>
  ) => (e: E) => Type3<M, U, L, B>
}

/**
 * Use `map2v` instead
 * @since 1.0.0
 * @deprecated
 */
export function map<F extends URIS3>(
  F: Functor3<F>
): <U, L, E, A, B>(f: (a: A) => B, fa: (e: E) => Type3<F, U, L, A>) => (e: E) => Type3<F, U, L, B>
/** @deprecated */
export function map<F extends URIS2>(
  F: Functor2<F>
): <L, E, A, B>(f: (a: A) => B, fa: (e: E) => Type2<F, L, A>) => (e: E) => Type2<F, L, B>
/** @deprecated */
export function map<F extends URIS>(
  F: Functor1<F>
): <E, A, B>(f: (a: A) => B, fa: (e: E) => Type<F, A>) => (e: E) => Type<F, B>
/** @deprecated */
export function map<F>(F: Functor<F>): <E, A, B>(f: (a: A) => B, fa: (e: E) => HKT<F, A>) => (e: E) => HKT<F, B>
/** @deprecated */
export function map<F>(F: Functor<F>): <E, A, B>(f: (a: A) => B, fa: (e: E) => HKT<F, A>) => (e: E) => HKT<F, B> {
  return (f, fa) => e => F.map(fa(e), f)
}

/**
 * Use `getReaderT2v` instead
 * @since 1.0.0
 * @deprecated
 */
export function chain<F extends URIS3>(
  F: Chain3<F>
): <U, L, E, A, B>(
  f: (a: A) => (e: E) => Type3<F, U, L, B>,
  fa: (e: E) => Type3<F, U, L, A>
) => (e: E) => Type3<F, U, L, B>
/** @deprecated */
export function chain<F extends URIS2>(
  F: Chain2<F>
): <L, E, A, B>(f: (a: A) => (e: E) => Type2<F, L, B>, fa: (e: E) => Type2<F, L, A>) => (e: E) => Type2<F, L, B>
/** @deprecated */
export function chain<F extends URIS>(
  F: Chain1<F>
): <E, A, B>(f: (a: A) => (e: E) => Type<F, B>, fa: (e: E) => Type<F, A>) => (e: E) => Type<F, B>
/** @deprecated */
export function chain<F>(
  F: Chain<F>
): <E, A, B>(f: (a: A) => (e: E) => HKT<F, B>, fa: (e: E) => HKT<F, A>) => (e: E) => HKT<F, B>
/** @deprecated */
export function chain<F>(
  F: Chain<F>
): <E, A, B>(f: (a: A) => (e: E) => HKT<F, B>, fa: (e: E) => HKT<F, A>) => (e: E) => HKT<F, B> {
  return (f, fa) => e => F.chain(fa(e), a => f(a)(e))
}

/**
 * Use `getReaderT2v` instead
 * @since 1.0.0
 * @deprecated
 */
// tslint:disable-next-line: deprecation
export function getReaderT<M extends URIS3>(M: Monad3<M>): ReaderT3<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getReaderT<M extends URIS2>(M: Monad2<M>): ReaderT2<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getReaderT<M extends URIS>(M: Monad1<M>): ReaderT1<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getReaderT<M>(M: Monad<M>): ReaderT<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getReaderT<M>(M: Monad<M>): ReaderT<M> {
  return {
    // tslint:disable-next-line: deprecation
    map: map(M),
    // tslint:disable-next-line: deprecation
    of: of(M),
    // tslint:disable-next-line: deprecation
    ap: ap(M),
    // tslint:disable-next-line: deprecation
    chain: chain(M)
  }
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function of<F extends URIS3>(F: Applicative3<F>): <U, L, E, A>(a: A) => (e: E) => Type3<F, U, L, A>
/** @deprecated */
export function of<F extends URIS2>(F: Applicative2<F>): <L, E, A>(a: A) => (e: E) => Type2<F, L, A>
/** @deprecated */
export function of<F extends URIS>(F: Applicative1<F>): <E, A>(a: A) => (e: E) => Type<F, A>
/** @deprecated */
export function of<F>(F: Applicative<F>): <E, A>(a: A) => (e: E) => HKT<F, A>
/** @deprecated */
export function of<F>(F: Applicative<F>): <E, A>(a: A) => (e: E) => HKT<F, A> {
  return <A>(a: A) => () => F.of(a)
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function ap<F extends URIS3>(
  F: Applicative3<F>
): <U, L, E, A, B>(
  fab: (e: E) => Type3<F, U, L, (a: A) => B>,
  fa: (e: E) => Type3<F, U, L, A>
) => (e: E) => Type3<F, U, L, B>
/** @deprecated */
export function ap<F extends URIS2>(
  F: Applicative2<F>
): <L, E, A, B>(fab: (e: E) => Type2<F, L, (a: A) => B>, fa: (e: E) => Type2<F, L, A>) => (e: E) => Type2<F, L, B>
/** @deprecated */
export function ap<F extends URIS>(
  F: Applicative1<F>
): <E, A, B>(fab: (e: E) => Type<F, (a: A) => B>, fa: (e: E) => Type<F, A>) => (e: E) => Type<F, B>
/** @deprecated */
export function ap<F>(
  F: Applicative<F>
): <E, A, B>(fab: (e: E) => HKT<F, (a: A) => B>, fa: (e: E) => HKT<F, A>) => (e: E) => HKT<F, B>
/** @deprecated */
export function ap<F>(
  F: Applicative<F>
): <E, A, B>(fab: (e: E) => HKT<F, (a: A) => B>, fa: (e: E) => HKT<F, A>) => (e: E) => HKT<F, B> {
  return (fab, fa) => e => F.ap(fab(e), fa(e))
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function ask<F extends URIS3>(F: Applicative3<F>): <U, L, E>() => (e: E) => Type3<F, U, L, E>
/** @deprecated */
export function ask<F extends URIS2>(F: Applicative2<F>): <L, E>() => (e: E) => Type2<F, L, E>
/** @deprecated */
export function ask<F extends URIS>(F: Applicative1<F>): <E>() => (e: E) => Type<F, E>
/** @deprecated */
export function ask<F>(F: Applicative<F>): <E>() => (e: E) => HKT<F, E>
/** @deprecated */
export function ask<F>(F: Applicative<F>): <E>() => (e: E) => HKT<F, E> {
  return () => F.of
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function asks<F extends URIS3>(F: Applicative3<F>): <U, L, E, A>(f: (e: E) => A) => (e: E) => Type3<F, U, L, A>
/** @deprecated */
export function asks<F extends URIS2>(F: Applicative2<F>): <L, E, A>(f: (e: E) => A) => (e: E) => Type2<F, L, A>
/** @deprecated */
export function asks<F extends URIS>(F: Applicative1<F>): <E, A>(f: (e: E) => A) => (e: E) => Type<F, A>
/** @deprecated */
export function asks<F>(F: Applicative<F>): <E, A>(f: (e: E) => A) => (e: E) => HKT<F, A>
/** @deprecated */
export function asks<F>(F: Applicative<F>): <E, A>(f: (e: E) => A) => (e: E) => HKT<F, A> {
  return f => e => F.of(f(e))
}

import { Either }  from  './Either.ts'
import { Monoid }  from  './Monoid.ts'
import { Ord }  from  './Ord.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Setoid, fromEquals }  from  './Setoid.ts'
import { Predicate, not, Refinement, identity }  from  './function.ts'
import { Separated }  from  './Compactable.ts'
import { Option }  from  './Option.ts'
import { Show }  from  './Show.ts'

/**
 * @since 1.17.0
 */
export const getShow = <A>(SA: Show<A>): Show<Set<A>> => {
  return {
    show: s => {
      let elements = ''
      s.forEach(a => {
        elements += SA.show(a) + ', '
      })
      if (elements !== '') {
        elements = elements.substring(0, elements.length - 2)
      }
      return `new Set([${elements}])`
    }
  }
}

/**
 * @since 1.14.0
 */
export const empty: Set<never> = new Set()

/**
 * @since 1.0.0
 */
export const toArray = <A>(O: Ord<A>) => (x: Set<A>): Array<A> => {
  const r: Array<A> = []
  x.forEach(e => r.push(e))
  return r.sort(O.compare)
}

/**
 * @since 1.0.0
 */
export const getSetoid = <A>(S: Setoid<A>): Setoid<Set<A>> => {
  const subsetS = subset(S)
  return fromEquals((x, y) => subsetS(x, y) && subsetS(y, x))
}

/**
 * @since 1.0.0
 */
export const some = <A>(x: Set<A>, predicate: Predicate<A>): boolean => {
  const values = x.values()
  let e: IteratorResult<A>
  let found = false
  while (!found && !(e = values.next()).done) {
    found = predicate(e.value)
  }
  return found
}

/**
 * Projects a Set through a function
 *
 * @since 1.2.0
 */
export const map = <B>(S: Setoid<B>): (<A>(set: Set<A>, f: (x: A) => B) => Set<B>) => {
  const has = elem(S)
  return (set, f) => {
    const r = new Set<B>()
    set.forEach(e => {
      const v = f(e)
      if (!has(v, r)) {
        r.add(v)
      }
    })
    return r
  }
}

/**
 * @since 1.0.0
 */
export const every = <A>(x: Set<A>, predicate: Predicate<A>): boolean => {
  return !some(x, not(predicate))
}

/**
 * @since 1.2.0
 */
export const chain = <B>(S: Setoid<B>): (<A>(set: Set<A>, f: (x: A) => Set<B>) => Set<B>) => {
  const has = elem(S)
  return (set, f) => {
    let r = new Set<B>()
    set.forEach(e => {
      f(e).forEach(e => {
        if (!has(e, r)) {
          r.add(e)
        }
      })
    })
    return r
  }
}

/**
 * `true` if and only if every element in the first set is an element of the second set
 *
 * @since 1.0.0
 */
export const subset = <A>(S: Setoid<A>): ((x: Set<A>, y: Set<A>) => boolean) => {
  const has = elem(S)
  return (x, y) => every(x, a => has(a, y))
}

/**
 * @since 1.0.0
 */
export function filter<A, B extends A>(x: Set<A>, predicate: Refinement<A, B>): Set<B>
export function filter<A>(x: Set<A>, predicate: Predicate<A>): Set<A>
export function filter<A>(x: Set<A>, predicate: Predicate<A>): Set<A> {
  const values = x.values()
  let e: IteratorResult<A>
  let r = new Set<A>()
  while (!(e = values.next()).done) {
    const value = e.value
    if (predicate(value)) {
      r.add(value)
    }
  }
  return r
}

/**
 * @since 1.2.0
 */
export function partition<A, B extends A>(x: Set<A>, predicate: Refinement<A, B>): Separated<Set<A>, Set<B>>
export function partition<A>(x: Set<A>, predicate: Predicate<A>): Separated<Set<A>, Set<A>>
export function partition<A>(x: Set<A>, predicate: Predicate<A>): Separated<Set<A>, Set<A>> {
  const values = x.values()
  let e: IteratorResult<A>
  let right = new Set<A>()
  let left = new Set<A>()
  while (!(e = values.next()).done) {
    const value = e.value
    if (predicate(value)) {
      right.add(value)
    } else {
      left.add(value)
    }
  }
  return { left, right }
}

/**
 * Use `elem` instead
 * @since 1.0.0
 * @deprecated
 */
export const member = <A>(S: Setoid<A>): ((set: Set<A>) => (a: A) => boolean) => {
  const has = elem(S)
  return set => a => has(a, set)
}

/**
 * Test if a value is a member of a set
 *
 * @since 1.14.0
 */
export const elem = <A>(S: Setoid<A>) => (a: A, x: Set<A>): boolean => {
  return some(x, (ax: A) => S.equals(a, ax))
}

/**
 * Form the union of two sets
 *
 * @since 1.0.0
 */
export const union = <A>(S: Setoid<A>): ((x: Set<A>, y: Set<A>) => Set<A>) => {
  const has = elem(S)
  return (x, y) => {
    const r = new Set(x)
    y.forEach(e => {
      if (!has(e, r)) {
        r.add(e)
      }
    })
    return r
  }
}

/**
 * The set of elements which are in both the first and second set
 *
 * @since 1.0.0
 */
export const intersection = <A>(S: Setoid<A>): ((x: Set<A>, y: Set<A>) => Set<A>) => {
  const has = elem(S)
  return (x, y) => {
    const r = new Set<A>()
    x.forEach(e => {
      if (has(e, y)) {
        r.add(e)
      }
    })
    return r
  }
}

/**
 * @since 1.2.0
 */
export const partitionMap = <L, R>(SL: Setoid<L>, SR: Setoid<R>) => <A>(
  x: Set<A>,
  f: (a: A) => Either<L, R>
): Separated<Set<L>, Set<R>> => {
  const values = x.values()
  let e: IteratorResult<A>
  let left = new Set<L>()
  let right = new Set<R>()
  const hasL = elem(SL)
  const hasR = elem(SR)
  while (!(e = values.next()).done) {
    const v = f(e.value)
    if (v.isLeft()) {
      if (!hasL(v.value, left)) {
        left.add(v.value)
      }
    } else {
      if (!hasR(v.value, right)) {
        right.add(v.value)
      }
    }
  }
  return { left, right }
}

/**
 * Use `difference2v` instead
 *
 * @since 1.0.0
 * @deprecated
 */
export const difference = <A>(S: Setoid<A>): ((x: Set<A>, y: Set<A>) => Set<A>) => {
  const d = difference2v(S)
  return (x, y) => d(y, x)
}

/**
 * Form the set difference (`x` - `y`)
 *
 * @example
 * import { difference2v }  from  'fp-ts/lib/Set.ts'
 * import { setoidNumber }  from  'fp-ts/lib/Setoid.ts'
 *
 * assert.deepStrictEqual(difference2v(setoidNumber)(new Set([1, 2]), new Set([1, 3])), new Set([2]))
 *
 *
 * @since 1.12.0
 */
export const difference2v = <A>(S: Setoid<A>): ((x: Set<A>, y: Set<A>) => Set<A>) => {
  const has = elem(S)
  return (x, y) => filter(x, a => !has(a, y))
}

/**
 * @since 1.0.0
 */
export const getUnionMonoid = <A>(S: Setoid<A>): Monoid<Set<A>> => {
  return {
    concat: union(S),
    empty
  }
}

/**
 * @since 1.0.0
 */
export const getIntersectionSemigroup = <A>(S: Setoid<A>): Semigroup<Set<A>> => {
  return {
    concat: intersection(S)
  }
}

/**
 * @since 1.0.0
 */
export const reduce = <A>(O: Ord<A>): (<B>(fa: Set<A>, b: B, f: (b: B, a: A) => B) => B) => {
  const toArrayO = toArray(O)
  return (fa, b, f) => toArrayO(fa).reduce(f, b)
}

/**
 * @since 1.14.0
 */
export const foldMap = <A, M>(O: Ord<A>, M: Monoid<M>): ((fa: Set<A>, f: (a: A) => M) => M) => {
  const toArrayO = toArray(O)
  return (fa, f) => toArrayO(fa).reduce((b, a) => M.concat(b, f(a)), M.empty)
}

/**
 * Create a set with one element
 *
 * @since 1.0.0
 */
export const singleton = <A>(a: A): Set<A> => {
  return new Set([a])
}

/**
 * Insert a value into a set
 *
 * @since 1.0.0
 */
export const insert = <A>(S: Setoid<A>): ((a: A, x: Set<A>) => Set<A>) => {
  const has = elem(S)
  return (a, x) => {
    if (!has(a, x)) {
      const r = new Set(x)
      r.add(a)
      return r
    } else {
      return x
    }
  }
}

/**
 * Delete a value from a set
 *
 * @since 1.0.0
 */
export const remove = <A>(S: Setoid<A>) => (a: A, x: Set<A>): Set<A> => {
  return filter(x, (ax: A) => !S.equals(a, ax))
}

/**
 * Create a set from an array
 *
 * @since 1.2.0
 */
export const fromArray = <A>(S: Setoid<A>) => (as: Array<A>): Set<A> => {
  const len = as.length
  const r = new Set<A>()
  const has = elem(S)
  for (let i = 0; i < len; i++) {
    const a = as[i]
    if (!has(a, r)) {
      r.add(a)
    }
  }
  return r
}

/**
 * @since 1.12.0
 */
export const compact = <A>(S: Setoid<A>): ((fa: Set<Option<A>>) => Set<A>) => {
  const filterMapS = filterMap(S)
  return fa => filterMapS(fa, identity)
}

/**
 * @since 1.12.0
 */
export const separate = <L, R>(SL: Setoid<L>, SR: Setoid<R>) => (fa: Set<Either<L, R>>): Separated<Set<L>, Set<R>> => {
  const hasL = elem(SL)
  const hasR = elem(SR)
  const left: Set<L> = new Set()
  const right: Set<R> = new Set()
  fa.forEach(e => {
    if (e.isLeft()) {
      if (!hasL(e.value, left)) {
        left.add(e.value)
      }
    } else {
      if (!hasR(e.value, right)) {
        right.add(e.value)
      }
    }
  })
  return { left, right }
}

/**
 * @since 1.12.0
 */
export const filterMap = <B>(S: Setoid<B>): (<A>(fa: Set<A>, f: (a: A) => Option<B>) => Set<B>) => {
  const has = elem(S)
  return (fa, f) => {
    const r: Set<B> = new Set()
    fa.forEach(a => {
      const ob = f(a)
      if (ob.isSome() && !has(ob.value, r)) {
        r.add(ob.value)
      }
    })
    return r
  }
}

import { Applicative, Applicative1, Applicative2, Applicative3 }  from  './Applicative.ts'
import { Chain, Chain1, Chain2, Chain3 }  from  './Chain.ts'
import { Functor, Functor1, Functor2, Functor3 }  from  './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monad, Monad1, Monad2, Monad3 }  from  './Monad.ts'
import { State }  from  './State.ts'
import { Endomorphism }  from  './function.ts'

export interface StateT2v<M> {
  readonly map: <S, A, B>(fa: (s: S) => HKT<M, [A, S]>, f: (a: A) => B) => (s: S) => HKT<M, [B, S]>
  readonly of: <S, A>(a: A) => (s: S) => HKT<M, [A, S]>
  readonly ap: <S, A, B>(
    fab: (s: S) => HKT<M, [(a: A) => B, S]>,
    fa: (s: S) => HKT<M, [A, S]>
  ) => (s: S) => HKT<M, [B, S]>
  readonly chain: <S, A, B>(
    fa: (s: S) => HKT<M, [A, S]>,
    f: (a: A) => (s: S) => HKT<M, [B, S]>
  ) => (s: S) => HKT<M, [B, S]>
}

export interface StateT2v1<M extends URIS> {
  readonly map: <S, A, B>(fa: (s: S) => Type<M, [A, S]>, f: (a: A) => B) => (s: S) => Type<M, [B, S]>
  readonly of: <S, A>(a: A) => (s: S) => Type<M, [A, S]>
  readonly ap: <S, A, B>(
    fab: (s: S) => Type<M, [(a: A) => B, S]>,
    fa: (s: S) => Type<M, [A, S]>
  ) => (s: S) => Type<M, [B, S]>
  readonly chain: <S, A, B>(
    fa: (s: S) => Type<M, [A, S]>,
    f: (a: A) => (s: S) => Type<M, [B, S]>
  ) => (s: S) => Type<M, [B, S]>
}

export interface StateT2v2<M extends URIS2> {
  readonly map: <L, S, A, B>(fa: (s: S) => Type2<M, L, [A, S]>, f: (a: A) => B) => (s: S) => Type2<M, L, [B, S]>
  readonly of: <L, S, A>(a: A) => (s: S) => Type2<M, L, [A, S]>
  readonly ap: <L, S, A, B>(
    fab: (s: S) => Type2<M, L, [(a: A) => B, S]>,
    fa: (s: S) => Type2<M, L, [A, S]>
  ) => (s: S) => Type2<M, L, [B, S]>
  readonly chain: <L, S, A, B>(
    fa: (s: S) => Type2<M, L, [A, S]>,
    f: (a: A) => (s: S) => Type2<M, L, [B, S]>
  ) => (s: S) => Type2<M, L, [B, S]>
}

export interface StateT2v3<M extends URIS3> {
  readonly map: <U, L, S, A, B>(
    fa: (s: S) => Type3<M, U, L, [A, S]>,
    f: (a: A) => B
  ) => (s: S) => Type3<M, U, L, [B, S]>
  readonly of: <U, L, S, A>(a: A) => (s: S) => Type3<M, U, L, [A, S]>
  readonly ap: <U, L, S, A, B>(
    fab: (s: S) => Type3<M, U, L, [(a: A) => B, S]>,
    fa: (s: S) => Type3<M, U, L, [A, S]>
  ) => (s: S) => Type3<M, U, L, [B, S]>
  readonly chain: <U, L, S, A, B>(
    fa: (s: S) => Type3<M, U, L, [A, S]>,
    f: (a: A) => (s: S) => Type3<M, U, L, [B, S]>
  ) => (s: S) => Type3<M, U, L, [B, S]>
}

/**
 * @since 1.14.0
 */
export function get2v<F extends URIS3>(F: Applicative3<F>): <S, U, L>(s: S) => Type3<F, U, L, [S, S]>
export function get2v<F extends URIS2>(F: Applicative2<F>): <S, L>(s: S) => Type2<F, L, [S, S]>
export function get2v<F extends URIS>(F: Applicative1<F>): <S>(s: S) => Type<F, [S, S]>
export function get2v<F>(F: Applicative<F>): <S>(s: S) => HKT<F, [S, S]>
export function get2v<F>(F: Applicative<F>): <S>(s: S) => HKT<F, [S, S]> {
  return s => F.of([s, s])
}

/**
 * @since 1.0.0
 */
export function put<F extends URIS3>(F: Applicative3<F>): <S>(s: S) => <U, L>() => Type3<F, U, L, [void, S]>
export function put<F extends URIS2>(F: Applicative2<F>): <S>(s: S) => <L>() => Type2<F, L, [void, S]>
export function put<F extends URIS>(F: Applicative1<F>): <S>(s: S) => () => Type<F, [void, S]>
export function put<F>(F: Applicative<F>): <S>(s: S) => () => HKT<F, [void, S]>
export function put<F>(F: Applicative<F>): <S>(s: S) => () => HKT<F, [void, S]> {
  return s => () => F.of([undefined, s])
}

/**
 * @since 1.0.0
 */
export function modify<F extends URIS3>(
  F: Applicative3<F>
): <S>(f: Endomorphism<S>) => <U, L>(s: S) => Type3<F, U, L, [void, S]>
export function modify<F extends URIS2>(
  F: Applicative2<F>
): <S>(f: Endomorphism<S>) => <L>(s: S) => Type2<F, L, [void, S]>
export function modify<F extends URIS>(F: Applicative1<F>): <S>(f: Endomorphism<S>) => (s: S) => Type<F, [void, S]>
export function modify<F>(F: Applicative<F>): <S>(f: Endomorphism<S>) => (s: S) => HKT<F, [void, S]>
export function modify<F>(F: Applicative<F>): <S>(f: Endomorphism<S>) => (s: S) => HKT<F, [void, S]> {
  return f => s => F.of([undefined, f(s)])
}

/**
 * @since 1.0.0
 */
export function gets<F extends URIS3>(
  F: Applicative3<F>
): <S, A>(f: (s: S) => A) => <U, L>(s: S) => Type3<F, U, L, [A, S]>
export function gets<F extends URIS2>(F: Applicative2<F>): <S, A>(f: (s: S) => A) => <L>(s: S) => Type2<F, L, [A, S]>
export function gets<F extends URIS>(F: Applicative1<F>): <S, A>(f: (s: S) => A) => (s: S) => Type<F, [A, S]>
export function gets<F>(F: Applicative<F>): <S, A>(f: (s: S) => A) => (s: S) => HKT<F, [A, S]>
export function gets<F>(F: Applicative<F>): <S, A>(f: (s: S) => A) => (s: S) => HKT<F, [A, S]> {
  return f => s => F.of([f(s), s])
}

/**
 * @since 1.2.0
 */
export function fromState<F extends URIS3>(
  F: Applicative3<F>
): <S, A, U, L>(fa: State<S, A>) => (s: S) => Type3<F, U, L, [A, S]>
export function fromState<F extends URIS2>(
  F: Applicative2<F>
): <S, A, L>(fa: State<S, A>) => (s: S) => Type2<F, L, [A, S]>
export function fromState<F extends URIS>(F: Applicative1<F>): <S, A>(fa: State<S, A>) => (s: S) => Type<F, [A, S]>
export function fromState<F>(F: Applicative<F>): <S, A>(fa: State<S, A>) => (s: S) => HKT<F, [A, S]>
export function fromState<F>(F: Applicative<F>): <S, A>(fa: State<S, A>) => (s: S) => HKT<F, [A, S]> {
  return fa => s => F.of(fa.run(s))
}

/**
 * @since 1.2.0
 */
export function liftF<F extends URIS3>(
  F: Functor3<F>
): <U, L, S, A>(fa: Type3<F, U, L, A>) => (s: S) => Type3<F, U, L, [A, S]>
export function liftF<F extends URIS2>(F: Functor2<F>): <L, S, A>(fa: Type2<F, L, A>) => (s: S) => Type2<F, L, [A, S]>
export function liftF<F extends URIS>(F: Functor1<F>): <S, A>(fa: Type<F, A>) => (s: S) => Type<F, [A, S]>
export function liftF<F>(F: Functor<F>): <S, A>(fa: HKT<F, A>) => (s: S) => HKT<F, [A, S]>
export function liftF<F>(F: Functor<F>): <S, A>(fa: HKT<F, A>) => (s: S) => HKT<F, [A, S]> {
  return fa => s => F.map(fa, a => [a, s])
}

/**
 * @since 1.14.0
 */
export function getStateT2v<M extends URIS3>(M: Monad3<M>): StateT2v3<M>
export function getStateT2v<M extends URIS2>(M: Monad2<M>): StateT2v2<M>
export function getStateT2v<M extends URIS>(M: Monad1<M>): StateT2v1<M>
export function getStateT2v<M>(M: Monad<M>): StateT2v<M>
export function getStateT2v<M>(M: Monad<M>): StateT2v<M> {
  return {
    map: (fa, f) => s => M.map(fa(s), ([a, s1]) => [f(a), s1]),
    of: a => s => M.of([a, s]),
    ap: (fab, fa) => s => M.chain(fab(s), ([f, s]) => M.map(fa(s), ([a, s]) => [f(a), s])),
    chain: (fa, f) => s => M.chain(fa(s), ([a, s1]) => f(a)(s1))
  }
}

/** @deprecated */
export interface StateT<M> {
  readonly map: <S, A, B>(f: (a: A) => B, fa: (s: S) => HKT<M, [A, S]>) => (s: S) => HKT<M, [B, S]>
  readonly of: <S, A>(a: A) => (s: S) => HKT<M, [A, S]>
  readonly ap: <S, A, B>(
    fab: (s: S) => HKT<M, [(a: A) => B, S]>,
    fa: (s: S) => HKT<M, [A, S]>
  ) => (s: S) => HKT<M, [B, S]>
  readonly chain: <S, A, B>(
    f: (a: A) => (s: S) => HKT<M, [B, S]>,
    fa: (s: S) => HKT<M, [A, S]>
  ) => (s: S) => HKT<M, [B, S]>
}

/** @deprecated */
export interface StateT1<M extends URIS> {
  readonly map: <S, A, B>(f: (a: A) => B, fa: (s: S) => Type<M, [A, S]>) => (s: S) => Type<M, [B, S]>
  readonly of: <S, A>(a: A) => (s: S) => Type<M, [A, S]>
  readonly ap: <S, A, B>(
    fab: (s: S) => Type<M, [(a: A) => B, S]>,
    fa: (s: S) => Type<M, [A, S]>
  ) => (s: S) => Type<M, [B, S]>
  readonly chain: <S, A, B>(
    f: (a: A) => (s: S) => Type<M, [B, S]>,
    fa: (s: S) => Type<M, [A, S]>
  ) => (s: S) => Type<M, [B, S]>
}

/** @deprecated */
export interface StateT2<M extends URIS2> {
  readonly map: <L, S, A, B>(f: (a: A) => B, fa: (s: S) => Type2<M, L, [A, S]>) => (s: S) => Type2<M, L, [B, S]>
  readonly of: <L, S, A>(a: A) => (s: S) => Type2<M, L, [A, S]>
  readonly ap: <L, S, A, B>(
    fab: (s: S) => Type2<M, L, [(a: A) => B, S]>,
    fa: (s: S) => Type2<M, L, [A, S]>
  ) => (s: S) => Type2<M, L, [B, S]>
  readonly chain: <L, S, A, B>(
    f: (a: A) => (s: S) => Type2<M, L, [B, S]>,
    fa: (s: S) => Type2<M, L, [A, S]>
  ) => (s: S) => Type2<M, L, [B, S]>
}

/** @deprecated */
export interface StateT3<M extends URIS3> {
  readonly map: <U, L, S, A, B>(
    f: (a: A) => B,
    fa: (s: S) => Type3<M, U, L, [A, S]>
  ) => (s: S) => Type3<M, U, L, [B, S]>
  readonly of: <U, L, S, A>(a: A) => (s: S) => Type3<M, U, L, [A, S]>
  readonly ap: <U, L, S, A, B>(
    fab: (s: S) => Type3<M, U, L, [(a: A) => B, S]>,
    fa: (s: S) => Type3<M, U, L, [A, S]>
  ) => (s: S) => Type3<M, U, L, [B, S]>
  readonly chain: <U, L, S, A, B>(
    f: (a: A) => (s: S) => Type3<M, U, L, [B, S]>,
    fa: (s: S) => Type3<M, U, L, [A, S]>
  ) => (s: S) => Type3<M, U, L, [B, S]>
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function map<F extends URIS3>(
  F: Functor3<F>
): <U, L, S, A, B>(f: (a: A) => B, fa: (s: S) => Type3<F, U, L, [A, S]>) => (s: S) => Type3<F, U, L, [B, S]>
/** @deprecated */
export function map<F extends URIS2>(
  F: Functor2<F>
): <L, S, A, B>(f: (a: A) => B, fa: (s: S) => Type2<F, L, [A, S]>) => (s: S) => Type2<F, L, [B, S]>
/** @deprecated */
export function map<F extends URIS>(
  F: Functor1<F>
): <S, A, B>(f: (a: A) => B, fa: (s: S) => Type<F, [A, S]>) => (s: S) => Type<F, [B, S]>
/** @deprecated */
export function map<F>(
  F: Functor<F>
): <S, A, B>(f: (a: A) => B, fa: (s: S) => HKT<F, [A, S]>) => (s: S) => HKT<F, [B, S]>
/** @deprecated */
export function map<F>(
  F: Functor<F>
): <S, A, B>(f: (a: A) => B, fa: (s: S) => HKT<F, [A, S]>) => (s: S) => HKT<F, [B, S]> {
  return (f, fa) => s => F.map(fa(s), ([a, s1]) => [f(a), s1])
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function ap<F extends URIS3>(
  F: Chain3<F>
): <U, L, S, A, B>(
  fab: (s: S) => Type3<F, U, L, [(a: A) => B, S]>,
  fa: (s: S) => Type3<F, U, L, [A, S]>
) => (s: S) => Type3<F, U, L, [B, S]>
/** @deprecated */
export function ap<F extends URIS2>(
  F: Chain2<F>
): <L, S, A, B>(
  fab: (s: S) => Type2<F, L, [(a: A) => B, S]>,
  fa: (s: S) => Type2<F, L, [A, S]>
) => (s: S) => Type2<F, L, [B, S]>
/** @deprecated */
export function ap<F extends URIS>(
  F: Chain1<F>
): <S, A, B>(fab: (s: S) => Type<F, [(a: A) => B, S]>, fa: (s: S) => Type<F, [A, S]>) => (s: S) => Type<F, [B, S]>
/** @deprecated */
export function ap<F>(
  F: Chain<F>
): <S, A, B>(fab: (s: S) => HKT<F, [(a: A) => B, S]>, fa: (s: S) => HKT<F, [A, S]>) => (s: S) => HKT<F, [B, S]>
/** @deprecated */
export function ap<F>(
  F: Chain<F>
): <S, A, B>(fab: (s: S) => HKT<F, [(a: A) => B, S]>, fa: (s: S) => HKT<F, [A, S]>) => (s: S) => HKT<F, [B, S]> {
  return (fab, fa) => s => F.chain(fab(s), ([f, s]) => F.map(fa(s), ([a, s]) => [f(a), s]))
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function chain<F extends URIS3>(
  F: Chain3<F>
): <U, L, S, A, B>(
  f: (a: A) => (s: S) => Type3<F, U, L, [B, S]>,
  fa: (s: S) => Type3<F, U, L, [A, S]>
) => (s: S) => Type3<F, U, L, [B, S]>
/** @deprecated */
export function chain<F extends URIS2>(
  F: Chain2<F>
): <L, S, A, B>(
  f: (a: A) => (s: S) => Type2<F, L, [B, S]>,
  fa: (s: S) => Type2<F, L, [A, S]>
) => (s: S) => Type2<F, L, [B, S]>
/** @deprecated */
export function chain<F extends URIS>(
  F: Chain1<F>
): <S, A, B>(f: (a: A) => (s: S) => Type<F, [B, S]>, fa: (s: S) => Type<F, [A, S]>) => (s: S) => Type<F, [B, S]>
/** @deprecated */
export function chain<F>(
  F: Chain<F>
): <S, A, B>(f: (a: A) => (s: S) => HKT<F, [B, S]>, fa: (s: S) => HKT<F, [A, S]>) => (s: S) => HKT<F, [B, S]>
/** @deprecated */
export function chain<F>(
  F: Chain<F>
): <S, A, B>(f: (a: A) => (s: S) => HKT<F, [B, S]>, fa: (s: S) => HKT<F, [A, S]>) => (s: S) => HKT<F, [B, S]> {
  return (f, fa) => s => F.chain(fa(s), ([a, s1]) => f(a)(s1))
}

/**
 * Use `getStateT2v` instead
 * @since 1.0.0
 * @deprecated
 */
// tslint:disable-next-line: deprecation
export function getStateT<M extends URIS3>(M: Monad3<M>): StateT3<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getStateT<M extends URIS2>(M: Monad2<M>): StateT2<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getStateT<M extends URIS>(M: Monad1<M>): StateT1<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getStateT<M>(M: Monad<M>): StateT<M>
/** @deprecated */
// tslint:disable-next-line: deprecation
export function getStateT<M>(M: Monad<M>): StateT<M> {
  return {
    // tslint:disable-next-line: deprecation
    map: map(M),
    // tslint:disable-next-line: deprecation
    of: of(M),
    // tslint:disable-next-line: deprecation
    ap: ap(M),
    // tslint:disable-next-line: deprecation
    chain: chain(M)
  }
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function of<F extends URIS3>(F: Applicative3<F>): <U, L, S, A>(a: A) => (s: S) => Type3<F, U, L, [A, S]>
/** @deprecated */
export function of<F extends URIS2>(F: Applicative2<F>): <L, S, A>(a: A) => (s: S) => Type2<F, L, [A, S]>
/** @deprecated */
export function of<F extends URIS>(F: Applicative1<F>): <S, A>(a: A) => (s: S) => Type<F, [A, S]>
/** @deprecated */
export function of<F>(F: Applicative<F>): <S, A>(a: A) => (s: S) => HKT<F, [A, S]>
/** @deprecated */
export function of<F>(F: Applicative<F>): <S, A>(a: A) => (s: S) => HKT<F, [A, S]> {
  return a => s => F.of([a, s])
}

/**
 * @since 1.0.0
 * @deprecated
 */
export function get<F extends URIS3>(F: Applicative3<F>): <S>() => <U, L>(s: S) => Type3<F, U, L, [S, S]>
/** @deprecated */
export function get<F extends URIS2>(F: Applicative2<F>): <S>() => <L>(s: S) => Type2<F, L, [S, S]>
/** @deprecated */
export function get<F extends URIS>(F: Applicative1<F>): <S>() => (s: S) => Type<F, [S, S]>
/** @deprecated */
export function get<F>(F: Applicative<F>): <S>() => (s: S) => HKT<F, [S, S]>
/** @deprecated */
export function get<F>(F: Applicative<F>): <S>() => (s: S) => HKT<F, [S, S]> {
  return () => s => F.of([s, s])
}

/**
 * @file Adapted from https://github.com/purescript/purescript-maps
 */
import { Applicative, Applicative1, Applicative2, Applicative3 }  from  './Applicative.ts'
import { Compactable1, Separated }  from  './Compactable.ts'
import { Either }  from  './Either.ts'
import { FilterableWithIndex1 }  from  './FilterableWithIndex.ts'
import { Foldable, Foldable1, Foldable2, Foldable3 }  from  './Foldable.ts'
import { Foldable2v1 }  from  './Foldable2v.ts'
import { FoldableWithIndex1 }  from  './FoldableWithIndex.ts'
import { Predicate, Refinement }  from  './function.ts'
import { FunctorWithIndex1 }  from  './FunctorWithIndex.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monoid }  from  './Monoid.ts'
import { Option }  from  './Option.ts'
import * as R  from  './Record.ts'
import { getLastSemigroup, Semigroup }  from  './Semigroup.ts'
import { Setoid, fromEquals }  from  './Setoid.ts'
import { TraversableWithIndex1 }  from  './TraversableWithIndex.ts'
import { Unfoldable, Unfoldable1 }  from  './Unfoldable.ts'
import { Witherable1 }  from  './Witherable.ts'
import { Show }  from  './Show.ts'

declare module './HKT.ts'
  interface URI2HKT<A> {
    StrMap: StrMap<A>
  }
}

export const URI = 'StrMap'

export type URI = typeof URI

const liftSeparated = <L, R>({
  left,
  right
}: Separated<Record<string, L>, Record<string, R>>): Separated<StrMap<L>, StrMap<R>> => {
  return {
    left: new StrMap(left),
    right: new StrMap(right)
  }
}

/**
 * @data
 * @constructor StrMap
 * @since 1.0.0
 */
export class StrMap<A> {
  readonly _A!: A
  readonly _URI!: URI
  constructor(readonly value: { [key: string]: A }) {}
  mapWithKey<B>(f: (k: string, a: A) => B): StrMap<B> {
    return new StrMap(R.mapWithKey(this.value, f))
  }
  map<B>(f: (a: A) => B): StrMap<B> {
    return this.mapWithKey((_, a) => f(a))
  }
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    return R.reduce(this.value, b, f)
  }
  /**
   * @since 1.12.0
   */
  foldr<B>(b: B, f: (a: A, b: B) => B): B {
    return R.foldr(this.value, b, f)
  }
  /**
   * @since 1.12.0
   */
  reduceWithKey<B>(b: B, f: (k: string, b: B, a: A) => B): B {
    return R.reduceWithKey(this.value, b, f)
  }
  /**
   * @since 1.12.0
   */
  foldrWithKey<B>(b: B, f: (k: string, a: A, b: B) => B): B {
    return R.foldrWithKey(this.value, b, f)
  }
  /**
   * @since 1.4.0
   */
  filter<B extends A>(p: Refinement<A, B>): StrMap<B>
  filter(p: Predicate<A>): StrMap<A>
  filter(p: Predicate<A>): StrMap<A> {
    return this.filterWithKey((_, a) => p(a))
  }
  /**
   * @since 1.12.0
   */
  filterMap<B>(f: (a: A) => Option<B>): StrMap<B> {
    return this.filterMapWithKey((_, a) => f(a))
  }
  /**
   * @since 1.12.0
   */
  partition(p: Predicate<A>): Separated<StrMap<A>, StrMap<A>> {
    return this.partitionWithKey((_, a) => p(a))
  }
  /**
   * @since 1.12.0
   */
  partitionMap<RL, RR>(f: (a: A) => Either<RL, RR>): Separated<StrMap<RL>, StrMap<RR>> {
    return this.partitionMapWithKey((_, a) => f(a))
  }
  /**
   * @since 1.12.0
   */
  separate<RL, RR>(this: StrMap<Either<RL, RR>>): Separated<StrMap<RL>, StrMap<RR>> {
    return liftSeparated(R.separate(this.value))
  }
  /**
   * Use `partitionMapWithKey` instead
   * @since 1.12.0
   * @deprecated
   */
  partitionMapWithIndex<RL, RR>(f: (i: string, a: A) => Either<RL, RR>): Separated<StrMap<RL>, StrMap<RR>> {
    return this.partitionMapWithKey(f)
  }
  /**
   * @since 1.14.0
   */
  partitionMapWithKey<RL, RR>(f: (i: string, a: A) => Either<RL, RR>): Separated<StrMap<RL>, StrMap<RR>> {
    return liftSeparated(R.partitionMapWithKey(this.value, f))
  }
  /**
   * Use `partitionWithKey` instead
   * @since 1.12.0
   * @deprecated
   */
  partitionWithIndex(p: (i: string, a: A) => boolean): Separated<StrMap<A>, StrMap<A>> {
    return this.partitionWithKey(p)
  }
  /**
   * @since 1.14.0
   */
  partitionWithKey(p: (i: string, a: A) => boolean): Separated<StrMap<A>, StrMap<A>> {
    return liftSeparated(R.partitionWithKey(this.value, p))
  }
  /**
   * Use `filterMapWithKey` instead
   * @since 1.12.0
   * @deprecated
   */
  filterMapWithIndex<B>(f: (i: string, a: A) => Option<B>): StrMap<B> {
    return this.filterMapWithKey(f)
  }
  /**
   * @since 1.14.0
   */
  filterMapWithKey<B>(f: (i: string, a: A) => Option<B>): StrMap<B> {
    return new StrMap(R.filterMapWithKey(this.value, f))
  }
  /**
   * Use `filterWithKey` instead
   * @since 1.12.0
   * @deprecated
   */
  filterWithIndex(p: (i: string, a: A) => boolean): StrMap<A> {
    return this.filterWithKey(p)
  }
  /**
   * @since 1.14.0
   */
  filterWithKey(p: (i: string, a: A) => boolean): StrMap<A> {
    return new StrMap(R.filterWithKey(this.value, p))
  }
  /**
   * @since 1.14.0
   */
  every(predicate: (a: A) => boolean): boolean {
    return R.every(this.value, predicate)
  }
  /**
   * @since 1.14.0
   */
  some(predicate: (a: A) => boolean): boolean {
    return R.some(this.value, predicate)
  }
}

/**
 * @since 1.17.0
 */
export const getShow = <A>(S: Show<A>): Show<StrMap<A>> => {
  const SR = R.getShow(S)
  return {
    show: s => `new StrMap(${SR.show(s.value)})`
  }
}

/**
 *
 * @since 1.10.0
 */
const empty: StrMap<never> = new StrMap(R.empty)

const concat = <A>(S: Semigroup<A>): ((x: StrMap<A>, y: StrMap<A>) => StrMap<A>) => {
  const concat = R.getMonoid(S).concat
  return (x, y) => new StrMap(concat(x.value, y.value))
}

/**
 *
 * @since 1.0.0
 */
export const getMonoid = <A = never>(S: Semigroup<A> = getLastSemigroup()): Monoid<StrMap<A>> => {
  return {
    concat: concat(S),
    empty
  }
}

const map = <A, B>(fa: StrMap<A>, f: (a: A) => B): StrMap<B> => {
  return fa.map(f)
}

const reduce = <A, B>(fa: StrMap<A>, b: B, f: (b: B, a: A) => B): B => {
  return fa.reduce(b, f)
}

const foldMap = <M>(M: Monoid<M>): (<A>(fa: StrMap<A>, f: (a: A) => M) => M) => {
  const foldMapM = R.foldMap(M)
  return (fa, f) => foldMapM(fa.value, f)
}

const foldr = <A, B>(fa: StrMap<A>, b: B, f: (a: A, b: B) => B): B => {
  return fa.foldr(b, f)
}

const reduceWithIndex = <A, B>(fa: StrMap<A>, b: B, f: (k: string, b: B, a: A) => B): B => {
  return fa.reduceWithKey(b, f)
}

const foldMapWithIndex = <M>(M: Monoid<M>): (<A>(fa: StrMap<A>, f: (k: string, a: A) => M) => M) => {
  const foldMapWithKey = R.foldMapWithKey(M)
  return (fa, f) => foldMapWithKey(fa.value, f)
}

const foldrWithIndex = <A, B>(fa: StrMap<A>, b: B, f: (k: string, a: A, b: B) => B): B => {
  return fa.foldrWithKey(b, f)
}

/**
 * Use `strmap.traverseWithIndex` instead
 * @since 1.0.0
 * @deprecated
 */
export function traverseWithKey<F extends URIS3>(
  F: Applicative3<F>
): <U, L, A, B>(ta: StrMap<A>, f: (k: string, a: A) => Type3<F, U, L, B>) => Type3<F, U, L, StrMap<B>>
export function traverseWithKey<F extends URIS2>(
  F: Applicative2<F>
): <L, A, B>(ta: StrMap<A>, f: (k: string, a: A) => Type2<F, L, B>) => Type2<F, L, StrMap<B>>
export function traverseWithKey<F extends URIS>(
  F: Applicative1<F>
): <A, B>(ta: StrMap<A>, f: (k: string, a: A) => Type<F, B>) => Type<F, StrMap<B>>
export function traverseWithKey<F>(
  F: Applicative<F>
): <A, B>(ta: StrMap<A>, f: (k: string, a: A) => HKT<F, B>) => HKT<F, StrMap<B>>
export function traverseWithKey<F>(
  F: Applicative<F>
): <A, B>(ta: StrMap<A>, f: (k: string, a: A) => HKT<F, B>) => HKT<F, StrMap<B>> {
  const traverseWithKeyF = R.traverseWithKey(F)
  return (ta, f) => F.map(traverseWithKeyF(ta.value, f), d => new StrMap(d))
}

function traverse<F>(F: Applicative<F>): <A, B>(ta: StrMap<A>, f: (a: A) => HKT<F, B>) => HKT<F, StrMap<B>> {
  const traverseWithKeyF = traverseWithKey(F)
  return (ta, f) => traverseWithKeyF(ta, (_, a) => f(a))
}

function sequence<F>(F: Applicative<F>): <A>(ta: StrMap<HKT<F, A>>) => HKT<F, StrMap<A>> {
  const traverseWithKeyF = traverseWithKey(F)
  return ta => traverseWithKeyF(ta, (_, a) => a)
}

/**
 * Test whether one dictionary contains all of the keys and values contained in another dictionary
 *
 * @since 1.0.0
 */
export const isSubdictionary = <A>(S: Setoid<A>): ((d1: StrMap<A>, d2: StrMap<A>) => boolean) => {
  const isSubrecordS = R.isSubrecord(S)
  return (d1, d2) => isSubrecordS(d1.value, d2.value)
}

/**
 * Calculate the number of key/value pairs in a dictionary
 *
 * @since 1.0.0
 */
export const size = <A>(d: StrMap<A>): number => {
  return R.size(d.value)
}

/**
 * Test whether a dictionary is empty
 *
 * @since 1.0.0
 */
export const isEmpty = <A>(d: StrMap<A>): boolean => {
  return R.isEmpty(d.value)
}

/**
 *
 * @since 1.0.0
 */
export const getSetoid = <A>(S: Setoid<A>): Setoid<StrMap<A>> => {
  const isSubrecordS = R.isSubrecord(S)
  return fromEquals((x, y) => isSubrecordS(x.value, y.value) && isSubrecordS(y.value, x.value))
}

/**
 * Create a dictionary with one key/value pair
 *
 * @since 1.0.0
 */
export const singleton = <A>(k: string, a: A): StrMap<A> => {
  return new StrMap(R.singleton(k, a))
}

/**
 * Lookup the value for a key in a dictionary
 *
 * @since 1.0.0
 */
export const lookup = <A>(k: string, d: StrMap<A>): Option<A> => {
  return R.lookup(k, d.value)
}

/**
 * Create a dictionary from a foldable collection of key/value pairs, using the
 * specified function to combine values for duplicate keys.
 *
 * @since 1.0.0
 */
export function fromFoldable<F extends URIS3>(
  F: Foldable3<F>
): <U, L, A>(ta: Type3<F, U, L, [string, A]>, onConflict: (existing: A, a: A) => A) => StrMap<A>
export function fromFoldable<F extends URIS2>(
  F: Foldable2<F>
): <L, A>(ta: Type2<F, L, [string, A]>, onConflict: (existing: A, a: A) => A) => StrMap<A>
export function fromFoldable<F extends URIS>(
  F: Foldable1<F>
): <A>(ta: Type<F, [string, A]>, onConflict: (existing: A, a: A) => A) => StrMap<A>
export function fromFoldable<F>(
  // tslint:disable-next-line: deprecation
  F: Foldable<F>
): <A>(ta: HKT<F, [string, A]>, onConflict: (existing: A, a: A) => A) => StrMap<A>
export function fromFoldable<F>(
  // tslint:disable-next-line: deprecation
  F: Foldable<F>
): <A>(ta: HKT<F, [string, A]>, onConflict: (existing: A, a: A) => A) => StrMap<A> {
  const fromFoldableF = R.fromFoldable(F)
  return (ta, onConflict) => new StrMap(fromFoldableF(ta, onConflict))
}

/**
 *
 * @since 1.0.0
 */
export const collect = <A, B>(d: StrMap<A>, f: (k: string, a: A) => B): Array<B> => {
  return R.collect(d.value, f)
}

/**
 *
 * @since 1.0.0
 */
export const toArray = <A>(d: StrMap<A>): Array<[string, A]> => {
  return R.toArray(d.value)
}

/**
 * Unfolds a dictionary into a list of key/value pairs
 *
 * @since 1.0.0
 */
export function toUnfoldable<F extends URIS>(U: Unfoldable1<F>): <A>(d: StrMap<A>) => Type<F, [string, A]>
export function toUnfoldable<F>(U: Unfoldable<F>): <A>(d: StrMap<A>) => HKT<F, [string, A]>
export function toUnfoldable<F>(U: Unfoldable<F>): <A>(d: StrMap<A>) => HKT<F, [string, A]> {
  const toUnfoldableU = R.toUnfoldable(U)
  return <A>(d: StrMap<A>) => toUnfoldableU<string, A>(d.value)
}

/**
 * Insert or replace a key/value pair in a map
 *
 * @since 1.0.0
 */
export const insert = <A>(k: string, a: A, d: StrMap<A>): StrMap<A> => {
  const value = R.insert(k, a, d.value)
  return value === d.value ? d : new StrMap(value)
}

/**
 * Delete a key and value from a map
 *
 * @since 1.0.0
 */
export const remove = <A>(k: string, d: StrMap<A>): StrMap<A> => {
  const value = R.remove(k, d.value)
  return value === d.value ? d : new StrMap(value)
}

/**
 * Delete a key and value from a map, returning the value as well as the subsequent map
 *
 * @since 1.0.0
 */
export const pop = <A>(k: string, d: StrMap<A>): Option<[A, StrMap<A>]> => {
  return R.pop(k, d.value).map(([a, d]) => [a, new StrMap(d)])
}

/**
 * @since 1.14.0
 */
export function elem<A>(S: Setoid<A>): (a: A, fa: StrMap<A>) => boolean {
  return (a, fa) => fa.some(x => S.equals(x, a))
}

const filterMap = <A, B>(fa: StrMap<A>, f: (a: A) => Option<B>): StrMap<B> => {
  return fa.filterMap(f)
}

const filter = <A>(fa: StrMap<A>, p: Predicate<A>): StrMap<A> => {
  return fa.filter(p)
}

const compact = <A>(fa: StrMap<Option<A>>): StrMap<A> => {
  return new StrMap(R.compact(fa.value))
}

const separate = <RL, RR>(fa: StrMap<Either<RL, RR>>): Separated<StrMap<RL>, StrMap<RR>> => {
  return fa.separate()
}

const partitionMap = <RL, RR, A>(fa: StrMap<A>, f: (a: A) => Either<RL, RR>): Separated<StrMap<RL>, StrMap<RR>> => {
  return fa.partitionMap(f)
}

const partition = <A>(fa: StrMap<A>, p: Predicate<A>): Separated<StrMap<A>, StrMap<A>> => {
  return fa.partition(p)
}

const wither = <F>(F: Applicative<F>): (<A, B>(wa: StrMap<A>, f: (a: A) => HKT<F, Option<B>>) => HKT<F, StrMap<B>>) => {
  const traverseF = traverse(F)
  return (wa, f) => F.map(traverseF(wa, f), compact)
}

const wilt = <F>(
  F: Applicative<F>
): (<RL, RR, A>(wa: StrMap<A>, f: (a: A) => HKT<F, Either<RL, RR>>) => HKT<F, Separated<StrMap<RL>, StrMap<RR>>>) => {
  const traverseF = traverse(F)
  return (wa, f) => F.map(traverseF(wa, f), separate)
}

const mapWithIndex = <A, B>(fa: StrMap<A>, f: (i: string, a: A) => B): StrMap<B> => {
  return fa.mapWithKey(f)
}

// tslint:disable-next-line: deprecation
const traverseWithIndex = traverseWithKey

const partitionMapWithIndex = <RL, RR, A>(
  fa: StrMap<A>,
  f: (i: string, a: A) => Either<RL, RR>
): Separated<StrMap<RL>, StrMap<RR>> => {
  return fa.partitionMapWithKey(f)
}

const partitionWithIndex = <A>(fa: StrMap<A>, p: (i: string, a: A) => boolean): Separated<StrMap<A>, StrMap<A>> => {
  return fa.partitionWithKey(p)
}

const filterMapWithIndex = <A, B>(fa: StrMap<A>, f: (i: string, a: A) => Option<B>): StrMap<B> => {
  return fa.filterMapWithKey(f)
}

const filterWithIndex = <A>(fa: StrMap<A>, p: (i: string, a: A) => boolean): StrMap<A> => {
  return fa.filterWithKey(p)
}

/**
 * @since 1.0.0
 */
export const strmap: FunctorWithIndex1<URI, string> &
  Foldable2v1<URI> &
  TraversableWithIndex1<URI, string> &
  Compactable1<URI> &
  FilterableWithIndex1<URI, string> &
  Witherable1<URI> &
  FoldableWithIndex1<URI, string> = {
  URI,
  map,
  reduce,
  foldMap,
  foldr,
  traverse,
  sequence,
  compact,
  separate,
  filter,
  filterMap,
  partition,
  partitionMap,
  wither,
  wilt,
  mapWithIndex,
  reduceWithIndex,
  foldMapWithIndex,
  foldrWithIndex,
  traverseWithIndex,
  partitionMapWithIndex,
  partitionWithIndex,
  filterMapWithIndex,
  filterWithIndex
}

/**
 * @file `TaskEither<L, A>` represents an asynchronous computation that either yields a value of type `A` or fails yielding an
 * error of type `L`. If you want to represent an asynchronous computation that never fails, please see `Task`.
 */
import { Alt2 }  from  './Alt.ts'
import { Bifunctor2 }  from  './Bifunctor.ts'
import {
  Either,
  fromPredicate as eitherFromPredicate,
  getApplySemigroup as eitherGetApplySemigroup,
  getSemigroup as eitherGetSemigroup,
  left as eitherLeft,
  right as eitherRight
} from './Either.ts'
import * as eitherT  from  './EitherT.ts'
import { constant, constIdentity, Lazy, Predicate, Refinement, identity }  from  './function.ts'
import { IO }  from  './IO.ts'
import { IOEither }  from  './IOEither.ts'
import { Monad2 }  from  './Monad.ts'
import { MonadIO2 }  from  './MonadIO.ts'
import { MonadTask2 }  from  './MonadTask.ts'
import { MonadThrow2 }  from  './MonadThrow.ts'
import { Monoid }  from  './Monoid.ts'
import { Semigroup }  from  './Semigroup.ts'
import { fromIO as taskFromIO, getSemigroup as taskGetSemigroup, Task, task, tryCatch as taskTryCatch }  from  './Task.ts'

declare module './HKT.ts'
  interface URI2HKT2<L, A> {
    TaskEither: TaskEither<L, A>
  }
}

export const URI = 'TaskEither'

export type URI = typeof URI

const T = eitherT.getEitherT2v(task)
const foldT = eitherT.fold(task)

/**
 * @since 1.0.0
 */
export class TaskEither<L, A> {
  readonly _A!: A
  readonly _L!: L
  readonly _URI!: URI
  constructor(readonly value: Task<Either<L, A>>) {}
  /** Runs the inner `Task` */
  run(): Promise<Either<L, A>> {
    return this.value.run()
  }
  map<B>(f: (a: A) => B): TaskEither<L, B> {
    return new TaskEither(T.map(this.value, f))
  }
  ap<B>(fab: TaskEither<L, (a: A) => B>): TaskEither<L, B> {
    return new TaskEither(T.ap(fab.value, this.value))
  }
  /**
   * Flipped version of `ap`
   */
  ap_<B, C>(this: TaskEither<L, (b: B) => C>, fb: TaskEither<L, B>): TaskEither<L, C> {
    return fb.ap(this)
  }
  /**
   * Combine two (parallel) effectful actions, keeping only the result of the first
   * @since 1.6.0
   */
  applyFirst<B>(fb: TaskEither<L, B>): TaskEither<L, A> {
    return fb.ap(this.map(constant))
  }
  /**
   * Combine two (parallel) effectful actions, keeping only the result of the second
   * @since 1.5.0
   */
  applySecond<B>(fb: TaskEither<L, B>): TaskEither<L, B> {
    return fb.ap(this.map<(b: B) => B>(constIdentity))
  }
  /**
   * Combine two (sequential) effectful actions, keeping only the result of the first
   * @since 1.12.0
   */
  chainFirst<B>(fb: TaskEither<L, B>): TaskEither<L, A> {
    return this.chain(a => fb.map(() => a))
  }
  /**
   * Combine two (sequential) effectful actions, keeping only the result of the second
   * @since 1.12.0
   */
  chainSecond<B>(fb: TaskEither<L, B>): TaskEither<L, B> {
    return this.chain(() => fb)
  }
  chain<B>(f: (a: A) => TaskEither<L, B>): TaskEither<L, B> {
    return new TaskEither(T.chain(this.value, a => f(a).value))
  }
  fold<R>(onLeft: (l: L) => R, onRight: (a: A) => R): Task<R> {
    return foldT(onLeft, onRight, this.value)
  }
  /**
   * Similar to `fold`, but the result is flattened.
   * @since 1.10.0
   */
  foldTask<R>(onLeft: (l: L) => Task<R>, onRight: (a: A) => Task<R>): Task<R> {
    return this.value.chain(e => e.fold(onLeft, onRight))
  }
  /**
   * Similar to `fold`, but the result is flattened.
   * @since 1.10.0
   */
  foldTaskEither<M, B>(onLeft: (l: L) => TaskEither<M, B>, onRight: (a: A) => TaskEither<M, B>): TaskEither<M, B> {
    return new TaskEither(this.value.chain(e => e.fold(onLeft, onRight).value))
  }
  /**
   * Similar to `fold`, return the value from Right or the given argument if Left.
   * @since 1.17.0
   */
  getOrElse(a: A): Task<A> {
    return this.getOrElseL(() => a)
  }
  /**
   * @since 1.17.0
   */
  getOrElseL(f: (l: L) => A): Task<A> {
    return this.fold(f, identity)
  }
  mapLeft<M>(f: (l: L) => M): TaskEither<M, A> {
    return new TaskEither(this.value.map(e => e.mapLeft(f)))
  }
  /**
   * Transforms the failure value of the `TaskEither` into a new `TaskEither`
   */
  orElse<M>(f: (l: L) => TaskEither<M, A>): TaskEither<M, A> {
    return new TaskEither(this.value.chain(e => e.fold<Task<Either<M, A>>>(l => f(l).value, T.of)))
  }
  /**
   * @since 1.6.0
   */
  alt(fy: TaskEither<L, A>): TaskEither<L, A> {
    return this.orElse(() => fy)
  }
  /**
   * @since 1.2.0
   */
  bimap<V, B>(f: (l: L) => V, g: (a: A) => B): TaskEither<V, B> {
    return new TaskEither(this.value.map(e => e.bimap(f, g)))
  }
  /**
   * Return `Right` if the given action succeeds, `Left` if it throws
   * @since 1.10.0
   */
  attempt<M = L>(): TaskEither<M, Either<L, A>> {
    return new TaskEither(this.value.map<Either<M, Either<L, A>>>(eitherRight))
  }
  /**
   * @since 1.11.0
   */
  filterOrElse<B extends A>(p: Refinement<A, B>, zero: L): TaskEither<L, B>
  filterOrElse(p: Predicate<A>, zero: L): TaskEither<L, A>
  filterOrElse(p: Predicate<A>, zero: L): TaskEither<L, A> {
    return new TaskEither(this.value.map(e => e.filterOrElse(p, zero)))
  }
  /**
   * @since 1.11.0
   */
  filterOrElseL<B extends A>(p: Refinement<A, B>, zero: (a: A) => L): TaskEither<L, B>
  filterOrElseL(p: Predicate<A>, zero: (a: A) => L): TaskEither<L, A>
  filterOrElseL(p: Predicate<A>, zero: (a: A) => L): TaskEither<L, A> {
    return new TaskEither(this.value.map(e => e.filterOrElseL(p, zero)))
  }
}

const map = <L, A, B>(fa: TaskEither<L, A>, f: (a: A) => B): TaskEither<L, B> => {
  return fa.map(f)
}

const of = <L, A>(a: A): TaskEither<L, A> => {
  return new TaskEither(T.of(a))
}

const ap = <L, A, B>(fab: TaskEither<L, (a: A) => B>, fa: TaskEither<L, A>): TaskEither<L, B> => {
  return fa.ap(fab)
}

const chain = <L, A, B>(fa: TaskEither<L, A>, f: (a: A) => TaskEither<L, B>): TaskEither<L, B> => {
  return fa.chain(f)
}

const alt = <L, A>(fx: TaskEither<L, A>, fy: TaskEither<L, A>): TaskEither<L, A> => {
  return fx.alt(fy)
}

const bimap = <L, V, A, B>(fa: TaskEither<L, A>, f: (l: L) => V, g: (a: A) => B): TaskEither<V, B> => {
  return fa.bimap(f, g)
}

/**
 * @since 1.0.0
 */
export const right = <L, A>(fa: Task<A>): TaskEither<L, A> => {
  return new TaskEither(fa.map<Either<L, A>>(eitherRight))
}

/**
 * @since 1.0.0
 */
export const left = <L, A>(fl: Task<L>): TaskEither<L, A> => {
  return new TaskEither(fl.map<Either<L, A>>(eitherLeft))
}

/**
 * @since 1.0.0
 */
export const fromEither = <L, A>(fa: Either<L, A>): TaskEither<L, A> => {
  return new TaskEither(task.of(fa))
}

/**
 * @since 1.5.0
 */
export const fromIO = <L, A>(fa: IO<A>): TaskEither<L, A> => {
  return right(taskFromIO(fa))
}

/**
 * @since 1.3.0
 */
export const fromLeft = <L, A>(l: L): TaskEither<L, A> => {
  return fromEither(eitherLeft(l))
}

/**
 * @since 1.6.0
 */
export const fromIOEither = <L, A>(fa: IOEither<L, A>): TaskEither<L, A> => {
  return new TaskEither(taskFromIO(fa.value))
}

/**
 * @since 1.6.0
 */
export function fromPredicate<L, A, B extends A>(
  predicate: Refinement<A, B>,
  onFalse: (a: A) => L
): (a: A) => TaskEither<L, B>
export function fromPredicate<L, A>(predicate: Predicate<A>, onFalse: (a: A) => L): (a: A) => TaskEither<L, A>
export function fromPredicate<L, A>(predicate: Predicate<A>, onFalse: (a: A) => L): (a: A) => TaskEither<L, A> {
  const f = eitherFromPredicate(predicate, onFalse)
  return a => fromEither(f(a))
}

/**
 * @since 1.9.0
 */
export const getSemigroup = <L, A>(S: Semigroup<A>): Semigroup<TaskEither<L, A>> => {
  const S2 = taskGetSemigroup(eitherGetSemigroup<L, A>(S))
  return {
    concat: (x, y) => new TaskEither<L, A>(S2.concat(x.value, y.value))
  }
}

/**
 * @since 1.9.0
 */
export const getApplySemigroup = <L, A>(S: Semigroup<A>): Semigroup<TaskEither<L, A>> => {
  const S2 = taskGetSemigroup(eitherGetApplySemigroup<L, A>(S))
  return {
    concat: (x, y) => new TaskEither<L, A>(S2.concat(x.value, y.value))
  }
}

/**
 * @since 1.9.0
 */
export const getApplyMonoid = <L, A>(M: Monoid<A>): Monoid<TaskEither<L, A>> => {
  return {
    ...getApplySemigroup(M),
    empty: of(M.empty)
  }
}

/**
 * Transforms a `Promise` into a `TaskEither`, catching the possible error.
 *
 * @example
 * import { createHash }  from  'crypto.ts'
 * import { TaskEither, tryCatch }  from  'fp-ts/lib/TaskEither.ts'
 * import { createReadStream }  from  'fs.ts'
 * import { left }  from  'fp-ts/lib/Either.ts'
 *
 * const md5 = (path: string): TaskEither<string, string> => {
 *   const mkHash = (p: string) =>
 *     new Promise<string>((resolve, reject) => {
 *       const hash = createHash('md5')
 *       const rs = createReadStream(p)
 *       rs.on('error', (error: Error) => reject(error.message))
 *       rs.on('data', (chunk: string) => hash.update(chunk))
 *       rs.on('end', () => {
 *         return resolve(hash.digest('hex'))
 *       })
 *     })
 *   return tryCatch(() => mkHash(path), message => `cannot create md5 hash: ${String(message)}`)
 * }
 *
 * md5('foo')
 *   .run()
 *   .then(x => {
 *     assert.deepStrictEqual(x, left(`cannot create md5 hash: ENOENT: no such file or directory, open 'foo'`))
 *   })
 *
 *
 * @since 1.0.0
 */
export const tryCatch = <L, A>(f: Lazy<Promise<A>>, onrejected: (reason: unknown) => L): TaskEither<L, A> => {
  return new TaskEither(taskTryCatch(f, onrejected))
}

/**
 * Convert a node style callback function to one returning a `TaskEither`
 *
 * **Note**. If the function `f` admits multiple overloadings, `taskify` will pick last one. If you want a different
 * behaviour, add an explicit type annotation
 *
 * ```ts
 * // readFile admits multiple overloadings
 *
 * // const readFile: (a: string) => TaskEither<NodeJS.ErrnoException, Buffer>
 * const readFile = taskify(fs.readFile)
 *
 * const readFile2: (filename: string, encoding: string) => TaskEither<NodeJS.ErrnoException, Buffer> = taskify(
 *   fs.readFile
 * )
 * ```
 *
 * @example
 * import { taskify }  from  'fp-ts/lib/TaskEither.ts'
 * import * as fs  from  'fs.ts'
 *
 * // const stat: (a: string | Buffer) => TaskEither<NodeJS.ErrnoException, fs.Stats>
 * const stat = taskify(fs.stat)
 * assert.strictEqual(stat.length, 0)
 *
 *
 * @since 1.5.0
 */
export function taskify<L, R>(f: (cb: (e: L | null | undefined, r?: R) => void) => void): () => TaskEither<L, R>
export function taskify<A, L, R>(
  f: (a: A, cb: (e: L | null | undefined, r?: R) => void) => void
): (a: A) => TaskEither<L, R>
export function taskify<A, B, L, R>(
  f: (a: A, b: B, cb: (e: L | null | undefined, r?: R) => void) => void
): (a: A, b: B) => TaskEither<L, R>
export function taskify<A, B, C, L, R>(
  f: (a: A, b: B, c: C, cb: (e: L | null | undefined, r?: R) => void) => void
): (a: A, b: B, c: C) => TaskEither<L, R>
export function taskify<A, B, C, D, L, R>(
  f: (a: A, b: B, c: C, d: D, cb: (e: L | null | undefined, r?: R) => void) => void
): (a: A, b: B, c: C, d: D) => TaskEither<L, R>
export function taskify<A, B, C, D, E, L, R>(
  f: (a: A, b: B, c: C, d: D, e: E, cb: (e: L | null | undefined, r?: R) => void) => void
): (a: A, b: B, c: C, d: D, e: E) => TaskEither<L, R>
export function taskify<L, R>(f: Function): () => TaskEither<L, R> {
  return function() {
    const args = Array.prototype.slice.call(arguments)
    return new TaskEither(
      new Task(
        () =>
          new Promise(resolve => {
            const cbResolver = (e: L, r: R) =>
              e != null ? resolve(eitherLeft<L, R>(e)) : resolve(eitherRight<L, R>(r))
            f.apply(null, args.concat(cbResolver))
          })
      )
    )
  }
}

const fromTask = right

/**
 * Make sure that a resource is cleaned up in the event of an exception. The
 * release action is called regardless of whether the body action throws or
 * returns.
 *
 * @since 1.10.0
 */
export const bracket = <L, A, B>(
  acquire: TaskEither<L, A>,
  use: (a: A) => TaskEither<L, B>,
  release: (a: A, e: Either<L, B>) => TaskEither<L, void>
): TaskEither<L, B> => {
  return acquire.chain(a =>
    use(a)
      .attempt()
      .chain(e => release(a, e).chain(() => e.fold<TaskEither<L, B>>(fromLeft, taskEither.of)))
  )
}

const throwError = fromLeft

/**
 * @since 1.0.0
 */
export const taskEither: Monad2<URI> &
  Bifunctor2<URI> &
  Alt2<URI> &
  MonadIO2<URI> &
  MonadTask2<URI> &
  MonadThrow2<URI> = {
  URI,
  bimap,
  map,
  of,
  ap,
  chain,
  alt,
  fromIO,
  fromTask,
  throwError,
  fromEither,
  fromOption: (o, e) => (o.isNone() ? throwError(e) : of(o.value))
}

/**
 * Like `TaskEither` but `ap` is sequential
 *
 * @since 1.10.0
 */
export const taskEitherSeq: typeof taskEither = {
  ...taskEither,
  ap: (fab, fa) => fab.chain(f => fa.map(f))
}

/**
 * @file A data structure providing "inclusive-or" as opposed to `Either`'s "exclusive-or".
 *
 * If you interpret `Either<L, A>` as suggesting the computation may either fail or succeed (exclusively), then
 * `These<L, A>` may fail, succeed, or do both at the same time.
 *
 * There are a few ways to interpret the both case:
 *
 * - You can think of a computation that has a non-fatal error.
 * - You can think of a computation that went as far as it could before erroring.
 * - You can think of a computation that keeps track of errors as it completes.
 *
 * Another way you can think of `These<L, A>` is saying that we want to handle `L` kind of data, `A` kind of data, or
 * both `L` and `A` kind of data at the same time. This is particularly useful when it comes to displaying UI's.
 *
 * (description adapted from https://package.elm-lang.org/packages/joneshf/elm-these)
 *
 * Adapted from https://github.com/purescript-contrib/purescript-these
 */
import { Applicative }  from  './Applicative.ts'
import { Bifunctor2 }  from  './Bifunctor.ts'
import { Either }  from  './Either.ts'
import { Foldable2v2 }  from  './Foldable2v.ts'
import { phantom, toString }  from  './function.ts'
import { Functor2 }  from  './Functor.ts'
import { HKT }  from  './HKT.ts'
import { Monad2C }  from  './Monad.ts'
import { Monoid }  from  './Monoid.ts'
import { none, Option, some }  from  './Option.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Setoid, fromEquals }  from  './Setoid.ts'
import { Traversable2v2 }  from  './Traversable2v.ts'
import { Show }  from  './Show.ts'

declare module './HKT.ts'
  interface URI2HKT2<L, A> {
    These: These<L, A>
  }
}

export const URI = 'These'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export type These<L, A> = This<L, A> | That<L, A> | Both<L, A>

export class This<L, A> {
  readonly _tag: 'This' = 'This'
  readonly _A!: A
  readonly _L!: L
  readonly _URI!: URI
  constructor(readonly value: L) {}
  map<B>(f: (a: A) => B): These<L, B> {
    return this as any
  }
  bimap<M, B>(f: (l: L) => M, g: (a: A) => B): These<M, B> {
    return new This(f(this.value))
  }
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    return b
  }
  /** Applies a function to each case in the data structure */
  fold<B>(this_: (l: L) => B, that: (a: A) => B, both: (l: L, a: A) => B): B {
    return this_(this.value)
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `this_(${toString(this.value)})`
  }
  /** Returns `true` if the these is `This`, `false` otherwise */
  isThis(): this is This<L, A> {
    return true
  }
  /** Returns `true` if the these is `That`, `false` otherwise */
  isThat(): this is That<L, A> {
    return false
  }
  /** Returns `true` if the these is `Both`, `false` otherwise */
  isBoth(): this is Both<L, A> {
    return false
  }
}

export class That<L, A> {
  readonly _tag: 'That' = 'That'
  readonly _A!: A
  readonly _L!: L
  readonly _URI!: URI
  constructor(readonly value: A) {}
  map<B>(f: (a: A) => B): These<L, B> {
    return new That(f(this.value))
  }
  bimap<M, B>(f: (l: L) => M, g: (a: A) => B): These<M, B> {
    return new That(g(this.value))
  }
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    return f(b, this.value)
  }
  fold<B>(this_: (l: L) => B, that: (a: A) => B, both: (l: L, a: A) => B): B {
    return that(this.value)
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `that(${toString(this.value)})`
  }
  isThis(): this is This<L, A> {
    return false
  }
  isThat(): this is That<L, A> {
    return true
  }
  isBoth(): this is Both<L, A> {
    return false
  }
}

export class Both<L, A> {
  readonly _tag: 'Both' = 'Both'
  readonly _A!: A
  readonly _L!: L
  readonly _URI!: URI
  constructor(readonly l: L, readonly a: A) {}
  map<B>(f: (a: A) => B): These<L, B> {
    return new Both(this.l, f(this.a))
  }
  bimap<M, B>(f: (l: L) => M, g: (a: A) => B): These<M, B> {
    return new Both(f(this.l), g(this.a))
  }
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    return f(b, this.a)
  }
  fold<B>(this_: (l: L) => B, that: (a: A) => B, both: (l: L, a: A) => B): B {
    return both(this.l, this.a)
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `both(${toString(this.l)}, ${toString(this.a)})`
  }
  isThis(): this is This<L, A> {
    return false
  }
  isThat(): this is That<L, A> {
    return false
  }
  isBoth(): this is Both<L, A> {
    return true
  }
}

/**
 * @since 1.17.0
 */
export const getShow = <L, A>(SL: Show<L>, SA: Show<A>): Show<These<L, A>> => {
  return {
    show: t =>
      t.fold(l => `this_(${SL.show(l)})`, a => `that(${SA.show(a)})`, (l, a) => `both(${SL.show(l)}, ${SA.show(a)})`)
  }
}

/**
 * @since 1.0.0
 */
export const getSetoid = <L, A>(SL: Setoid<L>, SA: Setoid<A>): Setoid<These<L, A>> => {
  return fromEquals((x, y) =>
    x.isThis()
      ? y.isThis() && SL.equals(x.value, y.value)
      : x.isThat()
      ? y.isThat() && SA.equals(x.value, y.value)
      : y.isBoth() && SL.equals(x.l, y.l) && SA.equals(x.a, y.a)
  )
}

/**
 * @since 1.0.0
 */
export const getSemigroup = <L, A>(SL: Semigroup<L>, SA: Semigroup<A>): Semigroup<These<L, A>> => {
  return {
    concat: (x, y) =>
      x.isThis()
        ? y.isThis()
          ? this_(SL.concat(x.value, y.value))
          : y.isThat()
          ? both(x.value, y.value)
          : both(SL.concat(x.value, y.l), y.a)
        : x.isThat()
        ? y.isThis()
          ? both(y.value, x.value)
          : y.isThat()
          ? that(SA.concat(x.value, y.value))
          : both(y.l, SA.concat(x.value, y.a))
        : y.isThis()
        ? both(SL.concat(x.l, y.value), x.a)
        : y.isThat()
        ? both(x.l, SA.concat(x.a, y.value))
        : both(SL.concat(x.l, y.l), SA.concat(x.a, y.a))
  }
}

const map = <L, A, B>(fa: These<L, A>, f: (a: A) => B): These<L, B> => {
  return fa.map(f)
}

/**
 * @since 1.0.0
 */
export const that = <L, A>(a: A): These<L, A> => {
  return new That<L, A>(a)
}

const of = that

const ap = <L>(S: Semigroup<L>) => <A, B>(fab: These<L, (a: A) => B>, fa: These<L, A>) => {
  return chain(S)(fab, f => map(fa, f))
}

const chain = <L>(S: Semigroup<L>) => <A, B>(fa: These<L, A>, f: (a: A) => These<L, B>): These<L, B> => {
  if (fa.isThis()) {
    return this_(fa.value)
  } else if (fa.isThat()) {
    return f(fa.value)
  } else {
    const fb = f(fa.a)
    return fb.isThis()
      ? this_(S.concat(fa.l, fb.value))
      : fb.isThat()
      ? both(fa.l, fb.value)
      : both(S.concat(fa.l, fb.l), fb.a)
  }
}

/**
 * @since 1.0.0
 */
export const getMonad = <L>(S: Semigroup<L>): Monad2C<URI, L> => {
  return {
    URI,
    _L: phantom,
    map,
    of,
    ap: ap(S),
    chain: chain(S)
  }
}

const bimap = <L, M, A, B>(fla: These<L, A>, f: (l: L) => M, g: (a: A) => B): These<M, B> => {
  return fla.bimap(f, g)
}

const reduce = <L, A, B>(fa: These<L, A>, b: B, f: (b: B, a: A) => B): B => {
  return fa.reduce(b, f)
}

const foldMap = <M>(M: Monoid<M>) => <L, A>(fa: These<L, A>, f: (a: A) => M): M => {
  return fa.isThis() ? M.empty : fa.isThat() ? f(fa.value) : f(fa.a)
}

const foldr = <L, A, B>(fa: These<L, A>, b: B, f: (a: A, b: B) => B): B => {
  return fa.isThis() ? b : fa.isThat() ? f(fa.value, b) : f(fa.a, b)
}

const traverse = <F>(F: Applicative<F>) => <L, A, B>(ta: These<L, A>, f: (a: A) => HKT<F, B>): HKT<F, These<L, B>> => {
  return ta.isThis()
    ? F.of(this_(ta.value))
    : ta.isThat()
    ? F.map(f(ta.value), that as (b: B) => These<L, B>)
    : F.map(f(ta.a), b => both(ta.l, b))
}

const sequence = <F>(F: Applicative<F>) => <L, A>(ta: These<L, HKT<F, A>>): HKT<F, These<L, A>> => {
  return ta.isThis()
    ? F.of(this_(ta.value))
    : ta.isThat()
    ? F.map(ta.value, that as (a: A) => These<L, A>)
    : F.map(ta.a, b => both(ta.l, b))
}

/**
 * @since 1.0.0
 */
export const this_ = <L, A>(l: L): These<L, A> => {
  return new This(l)
}

/**
 * @since 1.0.0
 */
export const both = <L, A>(l: L, a: A): These<L, A> => {
  return new Both(l, a)
}

/**
 *
 * @example
 * import { fromThese, this_, that, both }  from  'fp-ts/lib/These.ts'
 *
 * const from = fromThese('a', 1)
 * assert.deepStrictEqual(from(this_('b')), ['b', 1])
 * assert.deepStrictEqual(from(that(2)), ['a', 2])
 * assert.deepStrictEqual(from(both('b', 2)), ['b', 2])
 *
 * @since 1.0.0
 */
export const fromThese = <L, A>(defaultThis: L, defaultThat: A) => (fa: These<L, A>): [L, A] => {
  return fa.isThis() ? [fa.value, defaultThat] : fa.isThat() ? [defaultThis, fa.value] : [fa.l, fa.a]
}

/**
 * Returns an `L` value if possible
 *
 * @example
 * import { theseLeft, this_, that, both }  from  'fp-ts/lib/These.ts'
 * import { none, some }  from  'fp-ts/lib/Option.ts'
 *
 * assert.deepStrictEqual(theseLeft(this_('a')), some('a'))
 * assert.deepStrictEqual(theseLeft(that(1)), none)
 * assert.deepStrictEqual(theseLeft(both('a', 1)), some('a'))
 *
 * @since 1.0.0
 */
export const theseLeft = <L, A>(fa: These<L, A>): Option<L> => {
  return fa.isThis() ? some(fa.value) : fa.isThat() ? none : some(fa.l)
}

/**
 * Returns an `A` value if possible
 *
 * @example
 * import { theseRight, this_, that, both }  from  'fp-ts/lib/These.ts'
 * import { none, some }  from  'fp-ts/lib/Option.ts'
 *
 * assert.deepStrictEqual(theseRight(this_('a')), none)
 * assert.deepStrictEqual(theseRight(that(1)), some(1))
 * assert.deepStrictEqual(theseRight(both('a', 1)), some(1))
 *
 * @since 1.0.0
 */
export const theseRight = <L, A>(fa: These<L, A>): Option<A> => {
  return fa.isThis() ? none : fa.isThat() ? some(fa.value) : some(fa.a)
}

/**
 * Returns `true` if the these is an instance of `This`, `false` otherwise
 *
 * @since 1.0.0
 */
export const isThis = <L, A>(fa: These<L, A>): fa is This<L, A> => {
  return fa.isThis()
}

/**
 * Returns `true` if the these is an instance of `That`, `false` otherwise
 *
 * @since 1.0.0
 */
export const isThat = <L, A>(fa: These<L, A>): fa is That<L, A> => {
  return fa.isThat()
}

/**
 * Returns `true` if the these is an instance of `Both`, `false` otherwise
 *
 * @since 1.0.0
 */
export const isBoth = <L, A>(fa: These<L, A>): fa is Both<L, A> => {
  return fa.isBoth()
}

/**
 * @example
 * import { thisOrBoth, this_, both }  from  'fp-ts/lib/These.ts'
 * import { none, some }  from  'fp-ts/lib/Option.ts'
 *
 * assert.deepStrictEqual(thisOrBoth('a', none), this_('a'))
 * assert.deepStrictEqual(thisOrBoth('a', some(1)), both('a', 1))
 *
 * @since 1.13.0
 */
export const thisOrBoth = <L, A>(defaultThis: L, ma: Option<A>): These<L, A> => {
  return ma.isNone() ? this_(defaultThis) : both(defaultThis, ma.value)
}

/**
 * @example
 * import { thatOrBoth, that, both }  from  'fp-ts/lib/These.ts'
 * import { none, some }  from  'fp-ts/lib/Option.ts'
 *
 * assert.deepStrictEqual(thatOrBoth(1, none), that(1))
 * assert.deepStrictEqual(thatOrBoth(1, some('a')), both('a', 1))
 *
 * @since 1.13.0
 */
export const thatOrBoth = <L, A>(defaultThat: A, ml: Option<L>): These<L, A> => {
  return ml.isNone() ? that(defaultThat) : both(ml.value, defaultThat)
}

/**
 * Returns the `L` value if and only if the value is constructed with `This`
 *
 * @example
 * import { theseThis, this_, that, both }  from  'fp-ts/lib/These.ts'
 * import { none, some }  from  'fp-ts/lib/Option.ts'
 *
 * assert.deepStrictEqual(theseThis(this_('a')), some('a'))
 * assert.deepStrictEqual(theseThis(that(1)), none)
 * assert.deepStrictEqual(theseThis(both('a', 1)), none)
 *
 * @since 1.13.0
 */
export const theseThis = <L, A>(fa: These<L, A>): Option<L> => {
  return fa.isThis() ? some(fa.value) : none
}

/**
 * Returns the `A` value if and only if the value is constructed with `That`
 *
 * @example
 * import { theseThat, this_, that, both }  from  'fp-ts/lib/These.ts'
 * import { none, some }  from  'fp-ts/lib/Option.ts'
 *
 * assert.deepStrictEqual(theseThat(this_('a')), none)
 * assert.deepStrictEqual(theseThat(that(1)), some(1))
 * assert.deepStrictEqual(theseThat(both('a', 1)), none)
 *
 *
 * @since 1.13.0
 */
export const theseThat = <L, A>(fa: These<L, A>): Option<A> => {
  return fa.isThat() ? some(fa.value) : none
}

/**
 * Takes a pair of `Option`s and attempts to create a `These` from them
 *
 * @example
 * import { fromOptions, this_, that, both }  from  'fp-ts/lib/These.ts'
 * import { none, some }  from  'fp-ts/lib/Option.ts'
 *
 * assert.deepStrictEqual(fromOptions(none, none), none)
 * assert.deepStrictEqual(fromOptions(some('a'), none), some(this_('a')))
 * assert.deepStrictEqual(fromOptions(none, some(1)), some(that(1)))
 * assert.deepStrictEqual(fromOptions(some('a'), some(1)), some(both('a', 1)))
 *
 * @since 1.13.0
 */
export const fromOptions = <L, A>(fl: Option<L>, fa: Option<A>): Option<These<L, A>> => {
  return fl.foldL(
    () => fa.fold(none, a => some(that<L, A>(a))),
    l => fa.foldL(() => some(this_(l)), a => some(both(l, a)))
  )
}

/**
 * @example
 * import { fromEither, this_, that }  from  'fp-ts/lib/These.ts'
 * import { left, right }  from  'fp-ts/lib/Either.ts'
 *
 * assert.deepStrictEqual(fromEither(left('a')), this_('a'))
 * assert.deepStrictEqual(fromEither(right(1)), that(1))
 *
 * @since 1.13.0
 */
export const fromEither = <L, A>(fa: Either<L, A>): These<L, A> => {
  return fa.isLeft() ? this_(fa.value) : that(fa.value)
}

/**
 * @since 1.0.0
 */
export const these: Functor2<URI> & Bifunctor2<URI> & Foldable2v2<URI> & Traversable2v2<URI> = {
  URI,
  map,
  bimap,
  reduce,
  foldMap,
  foldr,
  traverse,
  sequence
}

import { Applicative, Applicative1, Applicative2, Applicative2C, Applicative3, Applicative3C }  from  './Applicative.ts'
import {
  Foldable,
  Foldable1,
  Foldable2,
  Foldable2C,
  Foldable3,
  Foldable3C,
  FoldableComposition,
  FoldableComposition11,
  getFoldableComposition
} from './Foldable.ts'
import {
  Functor,
  Functor1,
  Functor2,
  Functor2C,
  Functor3,
  Functor3C,
  FunctorComposition,
  FunctorComposition11,
  getFunctorComposition
} from './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'

/**
 * Use `Traversable2v` instead
 * @deprecated
 */
// tslint:disable-next-line: deprecation
export interface Traversable<T> extends Functor<T>, Foldable<T> {
  /**
   * Runs an action for every element in a data structure and accumulates the results
   */
  readonly traverse: Traverse<T>
}

export interface Traversable1<T extends URIS> extends Functor1<T>, Foldable1<T> {
  readonly traverse: Traverse1<T>
}

export interface Traversable2<T extends URIS2> extends Functor2<T>, Foldable2<T> {
  readonly traverse: Traverse2<T>
}

export interface Traversable2C<T extends URIS2, TL> extends Functor2C<T, TL>, Foldable2C<T, TL> {
  readonly traverse: Traverse2C<T, TL>
}

export interface Traversable3<T extends URIS3> extends Functor3<T>, Foldable3<T> {
  readonly traverse: Traverse3<T>
}

export interface Traversable3C<T extends URIS3, TU, TL> extends Functor3C<T, TU, TL>, Foldable3C<T, TU, TL> {
  readonly traverse: Traverse3C<T, TU, TL>
}

/**
 * @since 1.7.0
 */
export interface Traverse<T> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A, B>(
    ta: HKT<T, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, HKT<T, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: HKT<T, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, HKT<T, B>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A, B>(
    ta: HKT<T, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, HKT<T, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A, B>(
    ta: HKT<T, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, HKT<T, B>>
  <F extends URIS>(F: Applicative1<F>): <A, B>(ta: HKT<T, A>, f: (a: A) => Type<F, B>) => Type<F, HKT<T, B>>
  <F>(F: Applicative<F>): <A, B>(ta: HKT<T, A>, f: (a: A) => HKT<F, B>) => HKT<F, HKT<T, B>>
}

/**
 * @since 1.7.0
 */
export interface Traverse1<T extends URIS> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A, B>(
    ta: Type<T, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type<T, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: Type<T, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type<T, B>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A, B>(
    ta: Type<T, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type<T, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A, B>(
    ta: Type<T, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type<T, B>>
  <F extends URIS>(F: Applicative1<F>): <A, B>(ta: Type<T, A>, f: (a: A) => Type<F, B>) => Type<F, Type<T, B>>
  <F>(F: Applicative<F>): <A, B>(ta: Type<T, A>, f: (a: A) => HKT<F, B>) => HKT<F, Type<T, B>>
}

/**
 * @since 1.7.0
 */
export interface Traverse2<T extends URIS2> {
  <F extends URIS3>(F: Applicative3<F>): <TL, FU, FL, A, B>(
    ta: Type2<T, TL, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type2<T, TL, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <TL, A, B>(
    ta: Type2<T, TL, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type2<T, TL, B>>
  <F extends URIS2>(F: Applicative2<F>): <TL, FL, A, B>(
    ta: Type2<T, TL, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type2<T, TL, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <TL, A, B>(
    ta: Type2<T, TL, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type2<T, TL, B>>
  <F extends URIS>(F: Applicative1<F>): <TL, A, B>(
    ta: Type2<T, TL, A>,
    f: (a: A) => Type<F, B>
  ) => Type<F, Type2<T, TL, B>>
  <F>(F: Applicative<F>): <TL, A, B>(ta: Type2<T, TL, A>, f: (a: A) => HKT<F, B>) => HKT<F, Type2<T, TL, B>>
}

/**
 * @since 1.7.0
 */
export interface Traverse2C<T extends URIS2, TL> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A, B>(
    ta: Type2<T, TL, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type2<T, TL, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: Type2<T, TL, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type2<T, TL, B>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A, B>(
    ta: Type2<T, TL, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type2<T, TL, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A, B>(
    ta: Type2<T, TL, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type2<T, TL, B>>
  <F extends URIS>(F: Applicative1<F>): <A, B>(ta: Type2<T, TL, A>, f: (a: A) => Type<F, B>) => Type<F, Type2<T, TL, B>>
  <F>(F: Applicative<F>): <A, B>(ta: Type2<T, TL, A>, f: (a: A) => HKT<F, B>) => HKT<F, Type2<T, TL, B>>
}

/**
 * @since 1.7.0
 */
export interface Traverse3<T extends URIS3> {
  <F extends URIS3>(F: Applicative3<F>): <TU, TL, FU, FL, A, B>(
    ta: Type3<T, TU, TL, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type3<T, TU, TL, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <TU, TL, A, B>(
    ta: Type3<T, TU, TL, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type3<T, TU, TL, B>>
  <F extends URIS2>(F: Applicative2<F>): <TU, TL, FL, A, B>(
    ta: Type3<T, TU, TL, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type3<T, TU, TL, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <TU, TL, A, B>(
    ta: Type3<T, TU, TL, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type3<T, TU, TL, B>>
  <F extends URIS>(F: Applicative1<F>): <TU, TL, A, B>(
    ta: Type3<T, TU, TL, A>,
    f: (a: A) => Type<F, B>
  ) => Type<F, Type3<T, TU, TL, B>>
  <F>(F: Applicative<F>): <TU, TL, A, B>(ta: Type3<T, TU, TL, A>, f: (a: A) => HKT<F, B>) => HKT<F, Type3<T, TU, TL, B>>
}

/**
 * @since 1.7.0
 */
export interface Traverse3C<T extends URIS3, TU, TL> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A, B>(
    ta: Type3<T, TU, TL, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type3<T, TU, TL, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: Type3<T, TU, TL, A>,
    f: (a: A) => Type3<F, FU, FL, B>
  ) => Type3<F, FU, FL, Type3<T, TU, TL, B>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A, B>(
    ta: Type3<T, TU, TL, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type3<T, TU, TL, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A, B>(
    ta: Type3<T, TU, TL, A>,
    f: (a: A) => Type2<F, FL, B>
  ) => Type2<F, FL, Type3<T, TU, TL, B>>
  <F extends URIS>(F: Applicative1<F>): <A, B>(
    ta: Type3<T, TU, TL, A>,
    f: (a: A) => Type<F, B>
  ) => Type<F, Type3<T, TU, TL, B>>
  <F>(F: Applicative<F>): <A, B>(ta: Type3<T, TU, TL, A>, f: (a: A) => HKT<F, B>) => HKT<F, Type3<T, TU, TL, B>>
}

export interface TraversableComposition<F, G> extends FoldableComposition<F, G>, FunctorComposition<F, G> {
  readonly traverse: <H>(
    H: Applicative<H>
  ) => <A, B>(fga: HKT<F, HKT<G, A>>, f: (a: A) => HKT<H, B>) => HKT<H, HKT<F, HKT<G, B>>>
}

export interface TraverseComposition11<F extends URIS, G extends URIS> {
  <H extends URIS3>(H: Applicative3<H>): <HU, HL, A, B>(
    fga: Type<F, Type<G, A>>,
    f: (a: A) => Type3<H, HU, HL, B>
  ) => Type3<H, HU, HL, Type<F, Type<G, B>>>
  <H extends URIS3, HU, HL>(H: Applicative3C<H, HU, HL>): <A, B>(
    fga: Type<F, Type<G, A>>,
    f: (a: A) => Type3<H, HU, HL, B>
  ) => Type3<H, HU, HL, Type<F, Type<G, B>>>
  <H extends URIS2>(H: Applicative2<H>): <HL, A, B>(
    fga: Type<F, Type<G, A>>,
    f: (a: A) => Type2<H, HL, B>
  ) => Type2<H, HL, Type<F, Type<G, B>>>
  <H extends URIS2, HL>(H: Applicative2C<H, HL>): <A, B>(
    fga: Type<F, Type<G, A>>,
    f: (a: A) => Type2<H, HL, B>
  ) => Type2<H, HL, Type<F, Type<G, B>>>
  <H extends URIS>(H: Applicative1<H>): <A, B>(
    fga: Type<F, Type<G, A>>,
    f: (a: A) => Type<H, B>
  ) => Type<H, Type<F, Type<G, B>>>
  <H>(H: Applicative<H>): <A, B>(fga: Type<F, Type<G, A>>, f: (a: A) => HKT<H, B>) => HKT<H, Type<F, Type<G, B>>>
}

export interface TraversableComposition11<F extends URIS, G extends URIS>
  extends FoldableComposition11<F, G>,
    FunctorComposition11<F, G> {
  readonly traverse: TraverseComposition11<F, G>
}

/**
 * Use `traverse` contained in each traversable data structure instead.
 *
 *
 * @example
 * import { array }  from  'fp-ts/lib/Array.ts'
 * import { none, option, some }  from  'fp-ts/lib/Option.ts'
 *
 * assert.deepStrictEqual(array.traverse(option)([1, 2, 3], n => (n >= 0 ? some(n) : none)), some([1, 2, 3]))
 * assert.deepStrictEqual(array.traverse(option)([-1, 2, 3], n => (n >= 0 ? some(n) : none)), none)
 *
 * @since 1.0.0
 * @deprecated
 */
export function traverse<F extends URIS3, T extends URIS2>(
  F: Applicative3<F>,
  T: Traversable2<T>
): <UF, LF, LT, A, B>(ta: Type2<T, LT, A>, f: (a: A) => Type3<F, UF, LF, B>) => Type3<F, UF, LF, Type2<T, LT, B>>
export function traverse<F extends URIS2, T extends URIS2>(
  F: Applicative2<F>,
  T: Traversable2<T>
): <LF, LT, A, B>(ta: Type2<T, LT, A>, f: (a: A) => Type2<F, LF, B>) => Type2<F, LF, Type2<T, LT, B>>
export function traverse<F extends URIS2, T extends URIS2, LF>(
  F: Applicative2C<F, LF>,
  T: Traversable2<T>
): <LT, A, B>(ta: Type2<T, LT, A>, f: (a: A) => Type2<F, LF, B>) => Type2<F, LF, Type2<T, LT, B>>
export function traverse<F extends URIS, T extends URIS2>(
  F: Applicative1<F>,
  T: Traversable2<T>
): <LT, A, B>(ta: Type2<T, LT, A>, f: (a: A) => Type<F, B>) => Type<F, Type2<T, LT, B>>
export function traverse<F extends URIS3, T extends URIS>(
  F: Applicative3<F>,
  T: Traversable1<T>
): <U, L, A, B>(ta: Type<T, A>, f: (a: A) => Type3<F, U, L, B>) => Type3<F, U, L, Type<T, B>>
export function traverse<F extends URIS2, T extends URIS>(
  F: Applicative2<F>,
  T: Traversable1<T>
): <L, A, B>(ta: Type<T, A>, f: (a: A) => Type2<F, L, B>) => Type2<F, L, Type<T, B>>
export function traverse<F extends URIS2, T extends URIS, L>(
  F: Applicative2C<F, L>,
  T: Traversable1<T>
): <A, B>(ta: Type<T, A>, f: (a: A) => Type2<F, L, B>) => Type2<F, L, Type<T, B>>
export function traverse<F extends URIS, T extends URIS>(
  F: Applicative1<F>,
  T: Traversable1<T>
): <A, B>(ta: Type<T, A>, f: (a: A) => Type<F, B>) => Type<F, Type<T, B>>
export function traverse<F, T>(
  F: Applicative<F>,
  // tslint:disable-next-line: deprecation
  T: Traversable<T>
): <A, B>(ta: HKT<T, A>, f: (a: A) => HKT<F, B>) => HKT<F, HKT<T, B>>
export function traverse<F, T>(
  F: Applicative<F>,
  // tslint:disable-next-line: deprecation
  T: Traversable<T>
): <A, B>(ta: HKT<T, A>, f: (a: A) => HKT<F, B>) => HKT<F, HKT<T, B>> {
  return T.traverse(F)
}

/**
 * Use `sequence` contained in each traversable data structure instead.
 *
 * @example
 * import { array }  from  'fp-ts/lib/Array.ts'
 * import { none, option, some }  from  'fp-ts/lib/Option.ts'
 *
 * assert.deepStrictEqual(array.sequence(option)([some(1), some(2), some(3)]), some([1, 2, 3]))
 * assert.deepStrictEqual(array.sequence(option)([none, some(2), some(3)]), none)
 *
 * @since 1.0.0
 * @deprecated
 */
export function sequence<F extends URIS2, T extends URIS2>(
  F: Applicative2<F>,
  T: Traversable2<T>
): <LF, LT, A>(tfa: Type2<T, LT, Type2<F, LF, A>>) => Type2<F, LF, Type2<T, LT, A>>
export function sequence<F extends URIS2, T extends URIS2, LF>(
  F: Applicative2C<F, LF>,
  T: Traversable2<T>
): <LT, A>(tfa: Type2<T, LT, Type2<F, LF, A>>) => Type2<F, LF, Type2<T, LT, A>>
export function sequence<F extends URIS, T extends URIS2>(
  F: Applicative1<F>,
  T: Traversable2<T>
): <L, A>(tfa: Type2<T, L, Type<F, A>>) => Type<F, Type2<T, L, A>>
export function sequence<F extends URIS3, T extends URIS>(
  F: Applicative3<F>,
  T: Traversable1<T>
): <U, L, A>(tfa: Type<T, Type3<F, U, L, A>>) => Type3<F, U, L, Type<T, A>>
export function sequence<F extends URIS3, T extends URIS, U, L>(
  F: Applicative3C<F, U, L>,
  T: Traversable1<T>
): <A>(tfa: Type<T, Type3<F, U, L, A>>) => Type3<F, U, L, Type<T, A>>
export function sequence<F extends URIS2, T extends URIS>(
  F: Applicative2<F>,
  T: Traversable1<T>
): <L, A>(tfa: Type<T, Type2<F, L, A>>) => Type2<F, L, Type<T, A>>
export function sequence<F extends URIS2, T extends URIS, L>(
  F: Applicative2C<F, L>,
  T: Traversable1<T>
): <A>(tfa: Type<T, Type2<F, L, A>>) => Type2<F, L, Type<T, A>>
export function sequence<F extends URIS, T extends URIS>(
  F: Applicative1<F>,
  T: Traversable1<T>
): <A>(tfa: Type<T, Type<F, A>>) => Type<F, Type<T, A>>
export function sequence<F, T extends URIS>(
  F: Applicative<F>,
  T: Traversable1<T>
): <A>(tfa: Type<T, HKT<F, A>>) => HKT<F, Type<T, A>>
// tslint:disable-next-line: deprecation
export function sequence<F, T>(F: Applicative<F>, T: Traversable<T>): <A>(tfa: HKT<T, HKT<F, A>>) => HKT<F, HKT<T, A>>
// tslint:disable-next-line: deprecation
export function sequence<F, T>(F: Applicative<F>, T: Traversable<T>): <A>(tfa: HKT<T, HKT<F, A>>) => HKT<F, HKT<T, A>> {
  return tfa => T.traverse(F)(tfa, fa => fa)
}

/**
 * Use `Traversable2v`'s `getTraversableComposition` instead.
 *
 * @since 1.0.0
 * @deprecated
 */
export function getTraversableComposition<F extends URIS, G extends URIS>(
  F: Traversable1<F>,
  G: Traversable1<G>
): TraversableComposition11<F, G>
// tslint:disable-next-line: deprecation
export function getTraversableComposition<F, G>(F: Traversable<F>, G: Traversable<G>): TraversableComposition<F, G>
// tslint:disable-next-line: deprecation
export function getTraversableComposition<F, G>(F: Traversable<F>, G: Traversable<G>): TraversableComposition<F, G> {
  return {
    ...getFunctorComposition(F, G),
    ...getFoldableComposition(F, G),
    traverse: H => {
      const traverseF = F.traverse(H)
      const traverseG = G.traverse(H)
      return (fga, f) => traverseF(fga, ga => traverseG(ga, f))
    }
  }
}

/**
 * @file `Traversable` represents data structures which can be _traversed_ accumulating results and effects in some
 * `Applicative` functor.
 *
 * `traverse` signature:
 *
 * ```ts
 * <F>(F: Applicative<F>) => <A, B>(ta: HKT<T, A>, f: (a: A) => HKT<F, B>) => HKT<F, HKT<T, B>>
 * ```
 *
 * `sequence` signature:
 *
 * ```ts
 * <F>(F: Applicative<F>) => <A>(ta: HKT<T, HKT<F, A>>) => HKT<F, HKT<T, A>>
 * ```
 */
import { Applicative, Applicative1, Applicative2, Applicative2C, Applicative3, Applicative3C }  from  './Applicative.ts'
import {
  Foldable2v,
  Foldable2v1,
  Foldable2v2,
  Foldable2v2C,
  Foldable2v3,
  Foldable2v3C,
  Foldable2vComposition,
  Foldable2vComposition11,
  getFoldableComposition
} from './Foldable2v.ts'
import {
  Functor,
  Functor1,
  Functor2,
  Functor2C,
  Functor3,
  Functor3C,
  FunctorComposition,
  FunctorComposition11,
  getFunctorComposition
} from './Functor.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Traverse, Traverse1, Traverse2, Traverse2C, Traverse3, Traverse3C }  from  './Traversable.ts'

/**
 * @since 1.10.0
 */
export interface Traversable2v<T> extends Functor<T>, Foldable2v<T> {
  /**
   * Runs an action for every element in a data structure and accumulates the results
   */
  readonly traverse: Traverse<T>
  readonly sequence: Sequence<T>
}

/**
 * @since 1.10.0
 */
export interface Traversable2v1<T extends URIS> extends Functor1<T>, Foldable2v1<T> {
  readonly traverse: Traverse1<T>
  readonly sequence: Sequence1<T>
}

/**
 * @since 1.10.0
 */
export interface Traversable2v2<T extends URIS2> extends Functor2<T>, Foldable2v2<T> {
  readonly traverse: Traverse2<T>
  readonly sequence: Sequence2<T>
}

/**
 * @since 1.10.0
 */
export interface Traversable2v2C<T extends URIS2, TL> extends Functor2C<T, TL>, Foldable2v2C<T, TL> {
  readonly traverse: Traverse2C<T, TL>
  readonly sequence: Sequence2C<T, TL>
}

/**
 * @since 1.10.0
 */
export interface Traversable2v3<T extends URIS3> extends Functor3<T>, Foldable2v3<T> {
  readonly traverse: Traverse3<T>
  readonly sequence: Sequence3<T>
}

/**
 * @since 1.10.0
 */
export interface Traversable2v3C<T extends URIS3, TU, TL> extends Functor3C<T, TU, TL>, Foldable2v3C<T, TU, TL> {
  readonly traverse: Traverse3C<T, TU, TL>
  readonly sequence: Sequence3C<T, TU, TL>
}

/**
 * @since 1.10.0
 */
export interface Sequence<T> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A>(ta: HKT<T, Type3<F, FU, FL, A>>) => Type3<F, FU, FL, HKT<T, A>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A>(
    ta: HKT<T, Type3<F, FU, FL, A>>
  ) => Type3<F, FU, FL, HKT<T, A>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A>(ta: HKT<T, Type2<F, FL, A>>) => Type2<F, FL, HKT<T, A>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A>(ta: HKT<T, Type2<F, FL, A>>) => Type2<F, FL, HKT<T, A>>
  <F extends URIS>(F: Applicative1<F>): <A>(ta: HKT<T, Type<F, A>>) => Type<F, HKT<T, A>>
  <F>(F: Applicative<F>): <A>(ta: HKT<T, HKT<F, A>>) => HKT<F, HKT<T, A>>
}

/**
 * @since 1.10.0
 */
export interface Sequence1<T extends URIS> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A>(ta: Type<T, Type3<F, FU, FL, A>>) => Type3<F, FU, FL, Type<T, A>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A>(
    ta: Type<T, Type3<F, FU, FL, A>>
  ) => Type3<F, FU, FL, Type<T, A>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A>(ta: Type<T, Type2<F, FL, A>>) => Type2<F, FL, Type<T, A>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A>(ta: Type<T, Type2<F, FL, A>>) => Type2<F, FL, Type<T, A>>
  <F extends URIS>(F: Applicative1<F>): <A>(ta: Type<T, Type<F, A>>) => Type<F, Type<T, A>>
  <F>(F: Applicative<F>): <A>(ta: Type<T, HKT<F, A>>) => HKT<F, Type<T, A>>
}

/**
 * @since 1.10.0
 */
export interface Sequence2<T extends URIS2> {
  <F extends URIS3>(F: Applicative3<F>): <TL, FU, FL, A>(
    ta: Type2<T, TL, Type3<F, FU, FL, A>>
  ) => Type3<F, FU, FL, Type2<T, TL, A>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <TL, A>(
    ta: Type2<T, TL, Type3<F, FU, FL, A>>
  ) => Type3<F, FU, FL, Type2<T, TL, A>>
  <F extends URIS2>(F: Applicative2<F>): <TL, FL, A>(ta: Type2<T, TL, Type2<F, FL, A>>) => Type2<F, FL, Type2<T, TL, A>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <TL, A>(
    ta: Type2<T, TL, Type2<F, FL, A>>
  ) => Type2<F, FL, Type2<T, TL, A>>
  <F extends URIS>(F: Applicative1<F>): <TL, A>(ta: Type2<T, TL, Type<F, A>>) => Type<F, Type2<T, TL, A>>
  <F>(F: Applicative<F>): <TL, A>(ta: Type2<T, TL, HKT<F, A>>) => HKT<F, Type2<T, TL, A>>
}

/**
 * @since 1.10.0
 */
export interface Sequence2C<T extends URIS2, TL> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A>(
    ta: Type2<T, TL, Type3<F, FU, FL, A>>
  ) => Type3<F, FU, FL, Type2<T, TL, A>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A>(
    ta: Type2<T, TL, Type3<F, FU, FL, A>>
  ) => Type3<F, FU, FL, Type2<T, TL, A>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A>(ta: Type2<T, TL, Type2<F, FL, A>>) => Type2<F, FL, Type2<T, TL, A>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A>(
    ta: Type2<T, TL, Type2<F, FL, A>>
  ) => Type2<F, FL, Type2<T, TL, A>>
  <F extends URIS>(F: Applicative1<F>): <A>(ta: Type2<T, TL, Type<F, A>>) => Type<F, Type2<T, TL, A>>
  <F>(F: Applicative<F>): <A>(ta: Type2<T, TL, HKT<F, A>>) => HKT<F, Type2<T, TL, A>>
}

/**
 * @since 1.10.0
 */
export interface Sequence3<T extends URIS3> {
  <F extends URIS3>(F: Applicative3<F>): <TU, TL, FU, FL, A>(
    ta: Type3<T, TU, TL, Type3<F, FU, FL, A>>
  ) => Type3<F, FU, FL, Type3<T, TU, TL, A>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <TU, TL, A>(
    ta: Type3<T, TU, TL, Type3<F, FU, FL, A>>
  ) => Type3<F, FU, FL, Type3<T, TU, TL, A>>
  <F extends URIS2>(F: Applicative2<F>): <TU, TL, FL, A>(
    ta: Type3<T, TU, TL, Type2<F, FL, A>>
  ) => Type2<F, FL, Type3<T, TU, TL, A>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <TU, TL, A>(
    ta: Type3<T, TU, TL, Type2<F, FL, A>>
  ) => Type2<F, FL, Type3<T, TU, TL, A>>
  <F extends URIS>(F: Applicative1<F>): <TU, TL, A>(ta: Type3<T, TU, TL, Type<F, A>>) => Type<F, Type3<T, TU, TL, A>>
  <F>(F: Applicative<F>): <TU, TL, A>(ta: Type3<T, TU, TL, HKT<F, A>>) => HKT<F, Type3<T, TU, TL, A>>
}

/**
 * @since 1.10.0
 */
export interface Sequence3C<T extends URIS3, TU, TL> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A>(
    ta: Type3<T, TU, TL, Type3<F, FU, FL, A>>
  ) => Type3<F, FU, FL, Type3<T, TU, TL, A>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A>(
    ta: Type3<T, TU, TL, Type3<F, FU, FL, A>>
  ) => Type3<F, FU, FL, Type3<T, TU, TL, A>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A>(
    ta: Type3<T, TU, TL, Type2<F, FL, A>>
  ) => Type2<F, FL, Type3<T, TU, TL, A>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A>(
    ta: Type3<T, TU, TL, Type2<F, FL, A>>
  ) => Type2<F, FL, Type3<T, TU, TL, A>>
  <F extends URIS>(F: Applicative1<F>): <A>(ta: Type3<T, TU, TL, Type<F, A>>) => Type<F, Type3<T, TU, TL, A>>
  <F>(F: Applicative<F>): <A>(ta: Type3<T, TU, TL, HKT<F, A>>) => HKT<F, Type3<T, TU, TL, A>>
}

export interface Traversable2vComposition<F, G> extends Foldable2vComposition<F, G>, FunctorComposition<F, G> {
  readonly traverse: <H>(
    H: Applicative<H>
  ) => <A, B>(fga: HKT<F, HKT<G, A>>, f: (a: A) => HKT<H, B>) => HKT<H, HKT<F, HKT<G, B>>>
  readonly sequence: <H>(H: Applicative<H>) => <A>(fga: HKT<F, HKT<G, HKT<H, A>>>) => HKT<H, HKT<F, HKT<G, A>>>
}

export interface TraverseComposition11<F extends URIS, G extends URIS> {
  <H extends URIS3>(H: Applicative3<H>): <HU, HL, A, B>(
    fga: Type<F, Type<G, A>>,
    f: (a: A) => Type3<H, HU, HL, B>
  ) => Type3<H, HU, HL, Type<F, Type<G, B>>>
  <H extends URIS3, HU, HL>(H: Applicative3C<H, HU, HL>): <A, B>(
    fga: Type<F, Type<G, A>>,
    f: (a: A) => Type3<H, HU, HL, B>
  ) => Type3<H, HU, HL, Type<F, Type<G, B>>>
  <H extends URIS2>(H: Applicative2<H>): <HL, A, B>(
    fga: Type<F, Type<G, A>>,
    f: (a: A) => Type2<H, HL, B>
  ) => Type2<H, HL, Type<F, Type<G, B>>>
  <H extends URIS2, HL>(H: Applicative2C<H, HL>): <A, B>(
    fga: Type<F, Type<G, A>>,
    f: (a: A) => Type2<H, HL, B>
  ) => Type2<H, HL, Type<F, Type<G, B>>>
  <H extends URIS>(H: Applicative1<H>): <A, B>(
    fga: Type<F, Type<G, A>>,
    f: (a: A) => Type<H, B>
  ) => Type<H, Type<F, Type<G, B>>>
  <H>(H: Applicative<H>): <A, B>(fga: Type<F, Type<G, A>>, f: (a: A) => HKT<H, B>) => HKT<H, Type<F, Type<G, B>>>
}

export interface SequenceComposition11<F extends URIS, G extends URIS> {
  <H extends URIS3>(H: Applicative3<H>): <HU, HL, A>(
    fga: Type<F, Type<G, Type3<H, HU, HL, A>>>
  ) => Type3<H, HU, HL, Type<F, Type<G, A>>>
  <H extends URIS3, HU, HL>(H: Applicative3C<H, HU, HL>): <A>(
    fga: Type<F, Type<G, Type3<H, HU, HL, A>>>
  ) => Type3<H, HU, HL, Type<F, Type<G, A>>>
  <H extends URIS2>(H: Applicative2<H>): <HL, A>(
    fga: Type<F, Type<G, Type2<H, HL, A>>>
  ) => Type2<H, HL, Type<F, Type<G, A>>>
  <H extends URIS2, HL>(H: Applicative2C<H, HL>): <A>(
    fga: Type<F, Type<G, Type2<H, HL, A>>>
  ) => Type2<H, HL, Type<F, Type<G, A>>>
  <H extends URIS>(H: Applicative1<H>): <A>(fga: Type<F, Type<G, Type<H, A>>>) => Type<H, Type<F, Type<G, A>>>
  <H>(H: Applicative<H>): <A>(fga: Type<F, Type<G, HKT<H, A>>>) => HKT<H, Type<F, Type<G, A>>>
}

export interface Traversable2vComposition11<F extends URIS, G extends URIS>
  extends Foldable2vComposition11<F, G>,
    FunctorComposition11<F, G> {
  readonly traverse: TraverseComposition11<F, G>
  readonly sequence: SequenceComposition11<F, G>
}

/**
 * Returns the composition of two traversables
 *
 * @example
 * import { array }  from  'fp-ts/lib/Array.ts'
 * import { io, IO }  from  'fp-ts/lib/IO.ts'
 * import { none, option, some }  from  'fp-ts/lib/Option.ts'
 * import { getTraversableComposition }  from  'fp-ts/lib/Traversable2v.ts'
 *
 * const T = getTraversableComposition(array, option)
 * const state: Record<string, number | undefined> = {
 *   a: 1,
 *   b: 2
 * }
 * const read = (s: string) => new IO(() => state[s])
 * const x = T.sequence(io)([some(read('a')), none, some(read('b')), some(read('c'))])
 * assert.deepStrictEqual(x.run(), [some(1), none, some(2), some(undefined)])
 *
 * @since 1.10.0
 */
export function getTraversableComposition<F extends URIS, G extends URIS>(
  F: Traversable2v1<F>,
  G: Traversable2v1<G>
): Traversable2vComposition11<F, G>
export function getTraversableComposition<F, G>(
  F: Traversable2v<F>,
  G: Traversable2v<G>
): Traversable2vComposition<F, G>
export function getTraversableComposition<F, G>(
  F: Traversable2v<F>,
  G: Traversable2v<G>
): Traversable2vComposition<F, G> {
  return {
    ...getFunctorComposition(F, G),
    ...getFoldableComposition(F, G),
    traverse: H => {
      const traverseF = F.traverse(H)
      const traverseG = G.traverse(H)
      return (fga, f) => traverseF(fga, ga => traverseG(ga, f))
    },
    sequence: H => {
      const sequenceF = F.sequence(H)
      const sequenceG = G.sequence(H)
      return fgha => sequenceF(F.map(fgha, sequenceG))
    }
  }
}

/**
 * @file Multi-way trees (aka rose trees) and forests, where a forest is
 *
 * ```ts
 * type Forest<A> = Array<Tree<A>>
 * ```
 */
import { Applicative }  from  './Applicative.ts'
import { getSetoid as getArraySetoid, traverse as arrayTraverse, empty }  from  './Array.ts'
import { Comonad1 }  from  './Comonad.ts'
import { Foldable2v1 }  from  './Foldable2v.ts'
import { concat, identity, toString }  from  './function.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monad, Monad1, Monad2, Monad2C, Monad3, Monad3C }  from  './Monad.ts'
import { Monoid }  from  './Monoid.ts'
import { Setoid, fromEquals }  from  './Setoid.ts'
import { Traversable2v1 }  from  './Traversable2v.ts'
import { Show }  from  './Show.ts'

declare module './HKT.ts'
  interface URI2HKT<A> {
    Tree: Tree<A>
  }
}

export const URI = 'Tree'

export type URI = typeof URI

export type Forest<A> = Array<Tree<A>>

/**
 * @since 1.6.0
 */
export class Tree<A> {
  readonly _A!: A
  readonly _URI!: URI
  constructor(readonly value: A, readonly forest: Forest<A>) {}
  map<B>(f: (a: A) => B): Tree<B> {
    return new Tree(f(this.value), this.forest.map(tree => tree.map(f)))
  }
  ap<B>(fab: Tree<(a: A) => B>): Tree<B> {
    return fab.chain(f => this.map(f)) // <- derived
  }
  /**
   * Flipped version of `ap`
   * @since 1.6.0
   */
  ap_<B, C>(this: Tree<(b: B) => C>, fb: Tree<B>): Tree<C> {
    return fb.ap(this)
  }
  chain<B>(f: (a: A) => Tree<B>): Tree<B> {
    const { value, forest } = f(this.value)
    return new Tree(value, concat(forest, this.forest.map(t => t.chain(f))))
  }
  extract(): A {
    return this.value
  }
  extend<B>(f: (fa: Tree<A>) => B): Tree<B> {
    return new Tree(f(this), this.forest.map(t => t.extend(f)))
  }
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    let r: B = f(b, this.value)
    const len = this.forest.length
    for (let i = 0; i < len; i++) {
      r = this.forest[i].reduce(r, f)
    }
    return r
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `new Tree(${toString(this.value)}, ${toString(this.forest)})`
  }
}

/**
 * @since 1.17.0
 */
export const getShow = <A>(S: Show<A>): Show<Tree<A>> => {
  const show = (t: Tree<A>): string => {
    return `new Tree(${S.show(t.value)}, [${t.forest.map(show).join(', ')}])`
  }
  return {
    show
  }
}

const map = <A, B>(fa: Tree<A>, f: (a: A) => B): Tree<B> => {
  return fa.map(f)
}

const of = <A>(a: A): Tree<A> => {
  return new Tree(a, empty)
}

const ap = <A, B>(fab: Tree<(a: A) => B>, fa: Tree<A>): Tree<B> => {
  return fa.ap(fab)
}

const chain = <A, B>(fa: Tree<A>, f: (a: A) => Tree<B>): Tree<B> => {
  return fa.chain(f)
}

const extract = <A>(fa: Tree<A>): A => {
  return fa.extract()
}

const extend = <A, B>(fa: Tree<A>, f: (fa: Tree<A>) => B): Tree<B> => {
  return fa.extend(f)
}

const reduce = <A, B>(fa: Tree<A>, b: B, f: (b: B, a: A) => B): B => {
  return fa.reduce(b, f)
}

const foldMap = <M>(M: Monoid<M>) => <A>(fa: Tree<A>, f: (a: A) => M): M => {
  return fa.reduce(M.empty, (acc, a) => M.concat(acc, f(a)))
}

const foldr = <A, B>(fa: Tree<A>, b: B, f: (a: A, b: B) => B): B => {
  let r: B = b
  const len = fa.forest.length
  for (let i = len - 1; i >= 0; i--) {
    r = foldr(fa.forest[i], r, f)
  }
  return f(fa.value, r)
}

function traverse<F>(F: Applicative<F>): <A, B>(ta: Tree<A>, f: (a: A) => HKT<F, B>) => HKT<F, Tree<B>> {
  const traverseF = arrayTraverse(F)
  const r = <A, B>(ta: Tree<A>, f: (a: A) => HKT<F, B>): HKT<F, Tree<B>> =>
    F.ap(
      F.map(f(ta.value), (value: B) => (forest: Forest<B>) => new Tree(value, forest)),
      traverseF(ta.forest, t => r(t, f))
    )
  return r
}

function sequence<F>(F: Applicative<F>): <A>(ta: Tree<HKT<F, A>>) => HKT<F, Tree<A>> {
  const traverseF = traverse(F)
  return ta => traverseF(ta, identity)
}

/**
 * @since 1.6.0
 */
export const getSetoid = <A>(S: Setoid<A>): Setoid<Tree<A>> => {
  let SA: Setoid<Array<Tree<A>>>
  const R: Setoid<Tree<A>> = fromEquals((x, y) => S.equals(x.value, y.value) && SA.equals(x.forest, y.forest))
  SA = getArraySetoid(R)
  return R
}

/**
 * @since 1.6.0
 */
export const tree: Monad1<URI> & Foldable2v1<URI> & Traversable2v1<URI> & Comonad1<URI> = {
  URI,
  map,
  of,
  ap,
  chain,
  reduce,
  foldMap,
  foldr,
  traverse,
  sequence,
  extract,
  extend
}

const draw = (indentation: string, forest: Forest<string>): string => {
  let r: string = ''
  const len = forest.length
  let tree: Tree<string>
  for (let i = 0; i < len; i++) {
    tree = forest[i]
    const isLast = i === len - 1
    r += indentation + (isLast ? '└' : '├') + '─ ' + tree.value
    r += draw(indentation + (len > 1 && !isLast ? '│  ' : '   '), tree.forest)
  }
  return r
}

/**
 * Neat 2-dimensional drawing of a forest
 *
 * @since 1.6.0
 */
export const drawForest = (forest: Forest<string>): string => {
  return draw('\n', forest)
}

/**
 * Neat 2-dimensional drawing of a tree
 *
 * @example
 * import { Tree, drawTree, tree }  from  'fp-ts/lib/Tree.ts'
 *
 * const fa = new Tree('a', [
 *   tree.of('b'),
 *   tree.of('c'),
 *   new Tree('d', [tree.of('e'), tree.of('f')])
 * ])
 *
 * assert.strictEqual(drawTree(fa), `a
 * ├─ b
 * ├─ c
 * └─ d
 *    ├─ e
 *    └─ f`)
 *
 *
 * @since 1.6.0
 */
export const drawTree = (tree: Tree<string>): string => {
  return tree.value + drawForest(tree.forest)
}

/**
 * Build a tree from a seed value
 *
 * @since 1.6.0
 */
export const unfoldTree = <A, B>(b: B, f: (b: B) => [A, Array<B>]): Tree<A> => {
  const [a, bs] = f(b)
  return new Tree(a, unfoldForest(bs, f))
}

/**
 * Build a tree from a seed value
 *
 * @since 1.6.0
 */
export const unfoldForest = <A, B>(bs: Array<B>, f: (b: B) => [A, Array<B>]): Forest<A> => {
  return bs.map(b => unfoldTree(b, f))
}

/**
 * Monadic tree builder, in depth-first order
 *
 * @since 1.6.0
 */
export function unfoldTreeM<M extends URIS3>(
  M: Monad3<M>
): <U, L, A, B>(b: B, f: (b: B) => Type3<M, U, L, [A, Array<B>]>) => Type3<M, U, L, Tree<A>>
export function unfoldTreeM<M extends URIS3, U, L>(
  M: Monad3C<M, U, L>
): <A, B>(b: B, f: (b: B) => Type3<M, U, L, [A, Array<B>]>) => Type3<M, U, L, Tree<A>>
export function unfoldTreeM<M extends URIS2>(
  M: Monad2<M>
): <L, A, B>(b: B, f: (b: B) => Type2<M, L, [A, Array<B>]>) => Type2<M, L, Tree<A>>
export function unfoldTreeM<M extends URIS2, L>(
  M: Monad2C<M, L>
): <A, B>(b: B, f: (b: B) => Type2<M, L, [A, Array<B>]>) => Type2<M, L, Tree<A>>
export function unfoldTreeM<M extends URIS>(
  M: Monad1<M>
): <A, B>(b: B, f: (b: B) => Type<M, [A, Array<B>]>) => Type<M, Tree<A>>
export function unfoldTreeM<M>(M: Monad<M>): <A, B>(b: B, f: (b: B) => HKT<M, [A, Array<B>]>) => HKT<M, Tree<A>>
export function unfoldTreeM<M>(M: Monad<M>): <A, B>(b: B, f: (b: B) => HKT<M, [A, Array<B>]>) => HKT<M, Tree<A>> {
  const unfoldForestMM = unfoldForestM(M)
  return (b, f) => M.chain(f(b), ([a, bs]) => M.chain(unfoldForestMM(bs, f), ts => M.of(new Tree(a, ts))))
}

/**
 * Monadic forest builder, in depth-first order
 *
 * @since 1.6.0
 */
export function unfoldForestM<M extends URIS3>(
  M: Monad3<M>
): <U, L, A, B>(bs: Array<B>, f: (b: B) => Type3<M, U, L, [A, Array<B>]>) => Type3<M, U, L, Forest<A>>
export function unfoldForestM<M extends URIS3, U, L>(
  M: Monad3C<M, U, L>
): <A, B>(bs: Array<B>, f: (b: B) => Type3<M, U, L, [A, Array<B>]>) => Type3<M, U, L, Forest<A>>
export function unfoldForestM<M extends URIS2>(
  M: Monad2<M>
): <L, A, B>(bs: Array<B>, f: (b: B) => Type2<M, L, [A, Array<B>]>) => Type2<M, L, Forest<A>>
export function unfoldForestM<M extends URIS2, L>(
  M: Monad2C<M, L>
): <A, B>(bs: Array<B>, f: (b: B) => Type2<M, L, [A, Array<B>]>) => Type2<M, L, Forest<A>>
export function unfoldForestM<M extends URIS>(
  M: Monad1<M>
): <A, B>(bs: Array<B>, f: (b: B) => Type<M, [A, Array<B>]>) => Type<M, Forest<A>>
export function unfoldForestM<M>(
  M: Monad<M>
): <A, B>(bs: Array<B>, f: (b: B) => HKT<M, [A, Array<B>]>) => HKT<M, Forest<A>>
export function unfoldForestM<M>(
  M: Monad<M>
): <A, B>(bs: Array<B>, f: (b: B) => HKT<M, [A, Array<B>]>) => HKT<M, Forest<A>> {
  const traverseM = arrayTraverse(M)
  let unfoldTree: <A, B>(b: B, f: (b: B) => HKT<M, [A, Array<B>]>) => HKT<M, Tree<A>>
  return (bs, f) => {
    // tslint:disable-next-line
    if (unfoldTree === undefined) {
      unfoldTree = unfoldTreeM(M)
    }
    return traverseM(bs, b => unfoldTree(b, f))
  }
}

/**
 * @since 1.14.0
 */
export function elem<A>(S: Setoid<A>): (a: A, fa: Tree<A>) => boolean {
  const go = (a: A, fa: Tree<A>): boolean => {
    if (S.equals(a, fa.value)) {
      return true
    }
    return fa.forest.some(tree => go(a, tree))
  }
  return go
}

/**
 * `Witherable` represents data structures which can be _partitioned_ with effects in some `Applicative` functor.
 *
 * `wilt` signature (see `Compactable` `Separated`):
 *
 * ```ts
 * <F>(F: Applicative<F>) => <RL, RR, A>(wa: HKT<W, A>, f: (a: A) => HKT<F, Either<RL, RR>>) => HKT<F, Separated<HKT<W, RL>, HKT<W, RR>>>
 * ```
 *
 * `wither` signature:
 *
 * ```ts
 * <F>(F: Applicative<F>) => <A, B>(ta: HKT<W, A>, f: (a: A) => HKT<F, Option<B>>) => HKT<F, HKT<W, B>>
 * ```
 *
 * Adapted from https://github.com/LiamGoodacre/purescript-filterable/blob/master/src/Data/Witherable.purs
 */
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Option }  from  './Option.ts'
import { Traversable, Traversable1, Traversable2, Traversable2C, Traversable3, Traversable3C }  from  './Traversable.ts'
import { Applicative, Applicative1, Applicative2, Applicative2C, Applicative3, Applicative3C }  from  './Applicative.ts'
import { Filterable, Filterable1, Filterable2, Filterable2C, Filterable3, Filterable3C }  from  './Filterable.ts'
import { Either }  from  './Either.ts'
import { Separated }  from  './Compactable.ts'

/**
 * @since 1.7.0
 */
// tslint:disable-next-line: deprecation
export interface Witherable<T> extends Traversable<T>, Filterable<T> {
  /**
   * Partition a structure with effects
   */
  wilt: Wilt<T>

  /**
   * Filter a structure  with effects
   */
  wither: Wither<T>
}

/**
 * @since 1.7.0
 */
export interface Witherable1<T extends URIS> extends Traversable1<T>, Filterable1<T> {
  wilt: Wilt1<T>
  wither: Wither1<T>
}

/**
 * @since 1.7.0
 */
export interface Witherable2<T extends URIS2> extends Traversable2<T>, Filterable2<T> {
  wilt: Wilt2<T>
  wither: Wither2<T>
}

/**
 * @since 1.7.0
 */
export interface Witherable2C<T extends URIS2, TL> extends Traversable2C<T, TL>, Filterable2C<T, TL> {
  wilt: Wilt2C<T, TL>
  wither: Wither2C<T, TL>
}

/**
 * @since 1.7.0
 */
export interface Witherable3<T extends URIS3> extends Traversable3<T>, Filterable3<T> {
  wilt: Wilt3<T>
  wither: Wither3<T>
}

/**
 * @since 1.7.0
 */
export interface Witherable3C<T extends URIS3, TU, TL> extends Traversable3C<T, TU, TL>, Filterable3C<T, TU, TL> {
  wilt: Wilt3C<T, TU, TL>
  wither: Wither3C<T, TU, TL>
}

/**
 * @since 1.7.0
 */
export interface Wither<W> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A, B>(
    ta: HKT<W, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, HKT<W, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: HKT<W, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, HKT<W, B>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A, B>(
    ta: HKT<W, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, HKT<W, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A, B>(
    ta: HKT<W, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, HKT<W, B>>
  <F extends URIS>(F: Applicative1<F>): <A, B>(ta: HKT<W, A>, f: (a: A) => Type<F, Option<B>>) => Type<F, HKT<W, B>>
  <F>(F: Applicative<F>): <A, B>(ta: HKT<W, A>, f: (a: A) => HKT<F, Option<B>>) => HKT<F, HKT<W, B>>
}

/**
 * @since 1.7.0
 */
export interface Wither1<W extends URIS> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A, B>(
    ta: Type<W, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, Type<W, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: Type<W, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, Type<W, B>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A, B>(
    ta: Type<W, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, Type<W, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A, B>(
    ta: Type<W, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, Type<W, B>>
  <F extends URIS>(F: Applicative1<F>): <A, B>(ta: Type<W, A>, f: (a: A) => Type<F, Option<B>>) => Type<F, Type<W, B>>
  <F>(F: Applicative<F>): <A, B>(ta: Type<W, A>, f: (a: A) => HKT<F, Option<B>>) => HKT<F, Type<W, B>>
}

/**
 * @since 1.7.0
 */
export interface Wither2<W extends URIS2> {
  <F extends URIS3>(F: Applicative3<F>): <WL, FU, FL, A, B>(
    ta: Type2<W, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, Type2<W, WL, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <WL, A, B>(
    ta: Type2<W, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, Type2<W, WL, B>>
  <F extends URIS2>(F: Applicative2<F>): <WL, FL, A, B>(
    ta: Type2<W, WL, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, Type2<W, WL, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <WL, A, B>(
    ta: Type2<W, WL, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, Type2<W, WL, B>>
  <F extends URIS>(F: Applicative1<F>): <WL, A, B>(
    ta: Type2<W, WL, A>,
    f: (a: A) => Type<F, Option<B>>
  ) => Type<F, Type2<W, WL, B>>
  <F>(F: Applicative<F>): <WL, A, B>(ta: Type2<W, WL, A>, f: (a: A) => HKT<F, Option<B>>) => HKT<F, Type2<W, WL, B>>
}

/**
 * @since 1.7.0
 */
export interface Wither2C<W extends URIS2, WL> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A, B>(
    ta: Type2<W, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, Type2<W, WL, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: Type2<W, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, Type2<W, WL, B>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A, B>(
    ta: Type2<W, WL, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, Type2<W, WL, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A, B>(
    ta: Type2<W, WL, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, Type2<W, WL, B>>
  <F extends URIS>(F: Applicative1<F>): <A, B>(
    ta: Type2<W, WL, A>,
    f: (a: A) => Type<F, Option<B>>
  ) => Type<F, Type2<W, WL, B>>
  <F>(F: Applicative<F>): <A, B>(ta: Type2<W, WL, A>, f: (a: A) => HKT<F, Option<B>>) => HKT<F, Type2<W, WL, B>>
}

/**
 * @since 1.7.0
 */
export interface Wither3<W extends URIS3> {
  <F extends URIS3>(F: Applicative3<F>): <WU, WL, FU, FL, A, B>(
    ta: Type3<W, WU, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, Type3<W, WU, WL, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <WU, WL, A, B>(
    ta: Type3<W, WU, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, Type3<W, WU, WL, B>>
  <F extends URIS2>(F: Applicative2<F>): <WU, WL, FL, A, B>(
    ta: Type3<W, WU, WL, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, Type3<W, WU, WL, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <WU, WL, A, B>(
    ta: Type3<W, WU, WL, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, Type3<W, WU, WL, B>>
  <F extends URIS>(F: Applicative1<F>): <WU, WL, A, B>(
    ta: Type3<W, WU, WL, A>,
    f: (a: A) => Type<F, Option<B>>
  ) => Type<F, Type3<W, WU, WL, B>>
  <F>(F: Applicative<F>): <WU, WL, A, B>(
    ta: Type3<W, WU, WL, A>,
    f: (a: A) => HKT<F, Option<B>>
  ) => HKT<F, Type3<W, WU, WL, B>>
}

/**
 * @since 1.7.0
 */
export interface Wither3C<W extends URIS3, WU, WL> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, A, B>(
    ta: Type3<W, WU, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, Type3<W, WU, WL, B>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <A, B>(
    ta: Type3<W, WU, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Option<B>>
  ) => Type3<F, FU, FL, Type3<W, WU, WL, B>>
  <F extends URIS2>(F: Applicative2<F>): <FL, A, B>(
    ta: Type3<W, WU, WL, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, Type3<W, WU, WL, B>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <A, B>(
    ta: Type3<W, WU, WL, A>,
    f: (a: A) => Type2<F, FL, Option<B>>
  ) => Type2<F, FL, Type3<W, WU, WL, B>>
  <F extends URIS>(F: Applicative1<F>): <A, B>(
    ta: Type3<W, WU, WL, A>,
    f: (a: A) => Type<F, Option<B>>
  ) => Type<F, Type3<W, WU, WL, B>>
  <F>(F: Applicative<F>): <A, B>(ta: Type3<W, WU, WL, A>, f: (a: A) => HKT<F, Option<B>>) => HKT<F, Type3<W, WU, WL, B>>
}

/**
 * @since 1.7.0
 */
export interface Wilt<W> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, RL, RR, A>(
    wa: HKT<W, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<HKT<W, RL>, HKT<W, RR>>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <RL, RR, A>(
    wa: HKT<W, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<HKT<W, RL>, HKT<W, RR>>>
  <F extends URIS2>(F: Applicative2<F>): <FL, RL, RR, A>(
    wa: HKT<W, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<HKT<W, RL>, HKT<W, RR>>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <RL, RR, A>(
    wa: HKT<W, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<HKT<W, RL>, HKT<W, RR>>>
  <F extends URIS>(F: Applicative1<F>): <RL, RR, A>(
    wa: HKT<W, A>,
    f: (a: A) => Type<F, Either<RL, RR>>
  ) => Type<F, Separated<HKT<W, RL>, HKT<W, RR>>>
  <F>(F: Applicative<F>): <RL, RR, A>(
    wa: HKT<W, A>,
    f: (a: A) => HKT<F, Either<RL, RR>>
  ) => HKT<F, Separated<HKT<W, RL>, HKT<W, RR>>>
}

/**
 * @since 1.7.0
 */
export interface Wilt1<W extends URIS> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, RL, RR, A>(
    wa: Type<W, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<Type<W, RL>, Type<W, RR>>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <RL, RR, A>(
    wa: Type<W, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<Type<W, RL>, Type<W, RR>>>
  <F extends URIS2>(F: Applicative2<F>): <FL, RL, RR, A>(
    wa: Type<W, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<Type<W, RL>, Type<W, RR>>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <RL, RR, A>(
    wa: Type<W, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<Type<W, RL>, Type<W, RR>>>
  <F extends URIS>(F: Applicative1<F>): <RL, RR, A>(
    wa: Type<W, A>,
    f: (a: A) => Type<F, Either<RL, RR>>
  ) => Type<F, Separated<Type<W, RL>, Type<W, RR>>>
  <F>(F: Applicative<F>): <RL, RR, A>(
    wa: Type<W, A>,
    f: (a: A) => HKT<F, Either<RL, RR>>
  ) => HKT<F, Separated<Type<W, RL>, Type<W, RR>>>
}

/**
 * @since 1.7.0
 */
export interface Wilt2<W extends URIS2> {
  <F extends URIS3>(F: Applicative3<F>): <WL, FU, FL, RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <WL, RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
  <F extends URIS2>(F: Applicative2<F>): <WL, FL, RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <WL, RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
  <F extends URIS>(F: Applicative1<F>): <WL, RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => Type<F, Either<RL, RR>>
  ) => Type<F, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
  <F>(F: Applicative<F>): <WL, RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => HKT<F, Either<RL, RR>>
  ) => HKT<F, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
}

/**
 * @since 1.7.0
 */
export interface Wilt2C<W extends URIS2, WL> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
  <F extends URIS2>(F: Applicative2<F>): <FL, RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
  <F extends URIS>(F: Applicative1<F>): <RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => Type<F, Either<RL, RR>>
  ) => Type<F, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
  <F>(F: Applicative<F>): <RL, RR, A>(
    wa: Type2<W, WL, A>,
    f: (a: A) => HKT<F, Either<RL, RR>>
  ) => HKT<F, Separated<Type2<W, WL, RL>, Type2<W, WL, RR>>>
}

/**
 * @since 1.7.0
 */
export interface Wilt3<W extends URIS3> {
  <F extends URIS3>(F: Applicative3<F>): <WU, WL, FU, FL, RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <WU, WL, RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
  <F extends URIS2>(F: Applicative2<F>): <WU, WL, FL, RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <WU, WL, RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
  <F extends URIS>(F: Applicative1<F>): <WU, WL, RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => Type<F, Either<RL, RR>>
  ) => Type<F, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
  <F>(F: Applicative<F>): <WU, WL, RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => HKT<F, Either<RL, RR>>
  ) => HKT<F, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
}

/**
 * @since 1.7.0
 */
export interface Wilt3C<W extends URIS3, WU, WL> {
  <F extends URIS3>(F: Applicative3<F>): <FU, FL, RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
  <F extends URIS3, FU, FL>(F: Applicative3C<F, FU, FL>): <RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => Type3<F, FU, FL, Either<RL, RR>>
  ) => Type3<F, FU, FL, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
  <F extends URIS2>(F: Applicative2<F>): <FL, RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
  <F extends URIS2, FL>(F: Applicative2C<F, FL>): <RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => Type2<F, FL, Either<RL, RR>>
  ) => Type2<F, FL, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
  <F extends URIS>(F: Applicative1<F>): <RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => Type<F, Either<RL, RR>>
  ) => Type<F, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
  <F>(F: Applicative<F>): <RL, RR, A>(
    wa: Type3<W, WU, WL, A>,
    f: (a: A) => HKT<F, Either<RL, RR>>
  ) => HKT<F, Separated<Type3<W, WU, WL, RL>, Type3<W, WU, WL, RR>>>
}

/**
 * @file Provides a pointed array, which is a non-empty zipper-like array structure that tracks an index (focus)
 * position in an array. Focus can be moved forward and backwards through the array.
 *
 * The array `[1, 2, 3, 4]` with focus on `3` is represented by `new Zipper([1, 2], 3, [4])`
 *
 * Adapted from
 *
 * - https://github.com/DavidHarrison/purescript-list-zipper
 * - https://github.com/thunklife/purescript-zipper
 * - https://github.com/scalaz/scalaz/blob/series/7.3.x/core/src/main/scala/scalaz/Zipper.scala
 */
import { Applicative, Applicative1 }  from  './Applicative.ts'
import { array, cons, drop, empty, isEmpty, isOutOfBound, snoc, take, getShow as getArrayShow }  from  './Array.ts'
import { Comonad1 }  from  './Comonad.ts'
import { Foldable2v1 }  from  './Foldable2v.ts'
import { decrement, increment, toString }  from  './function.ts'
import { HKT }  from  './HKT.ts'
import { Monoid }  from  './Monoid.ts'
import { NonEmptyArray }  from  './NonEmptyArray.ts'
import { NonEmptyArray as NonEmptyArray2v }  from  './NonEmptyArray2v.ts'
import { none, Option, some }  from  './Option.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Traversable2v1 }  from  './Traversable2v.ts'
import { Show }  from  './Show.ts'

declare module './HKT.ts'
  interface URI2HKT<A> {
    Zipper: Zipper<A>
  }
}

export const URI = 'Zipper'

export type URI = typeof URI

/**
 * @since 1.9.0
 */
export class Zipper<A> {
  readonly _A!: A
  readonly _URI!: URI
  length: number
  constructor(readonly lefts: Array<A>, readonly focus: A, readonly rights: Array<A>) {
    this.length = lefts.length + 1 + rights.length
  }
  /**
   * Update the focus in this zipper.
   * @since 1.9.0
   */
  update(a: A): Zipper<A> {
    return new Zipper(this.lefts, a, this.rights)
  }
  /**
   * Apply `f` to the focus and update with the result.
   * @since 1.9.0
   */
  modify(f: (a: A) => A): Zipper<A> {
    return this.update(f(this.focus))
  }
  /**
   * @since 1.9.0
   */
  toArray(): Array<A> {
    return snoc(this.lefts, this.focus).concat(this.rights)
  }
  /**
   * @since 1.9.0
   */
  isOutOfBound(index: number): boolean {
    return index < 0 || index >= this.length
  }
  /**
   * Moves focus in the zipper, or `None` if there is no such element.
   * @since 1.9.0
   */
  move(f: (currentIndex: number) => number): Option<Zipper<A>> {
    const newIndex = f(this.lefts.length)
    if (this.isOutOfBound(newIndex)) {
      return none
    } else {
      return fromArray(this.toArray(), newIndex)
    }
  }
  /**
   * @since 1.9.0
   */
  up(): Option<Zipper<A>> {
    return this.move(decrement)
  }
  /**
   * @since 1.9.0
   */
  down(): Option<Zipper<A>> {
    return this.move(increment)
  }
  /**
   * Moves focus to the start of the zipper.
   * @since 1.9.0
   */
  start(): Zipper<A> {
    if (isEmpty(this.lefts)) {
      return this
    } else {
      return new Zipper(empty, this.lefts[0], snoc(drop(1, this.lefts), this.focus).concat(this.rights))
    }
  }
  /**
   * Moves focus to the end of the zipper.
   * @since 1.9.0
   */
  end(): Zipper<A> {
    const len = this.rights.length
    if (len === 0) {
      return this
    } else {
      return new Zipper(snoc(this.lefts, this.focus).concat(take(len - 1, this.rights)), this.rights[len - 1], empty)
    }
  }
  /**
   * Inserts an element to the left of focus and focuses on the new element.
   * @since 1.9.0
   */
  insertLeft(a: A): Zipper<A> {
    return new Zipper(this.lefts, a, cons(this.focus, this.rights))
  }
  /**
   * Inserts an element to the right of focus and focuses on the new element.
   * @since 1.9.0
   */
  insertRight(a: A): Zipper<A> {
    return new Zipper(snoc(this.lefts, this.focus), a, this.rights)
  }
  /**
   * Deletes the element at focus and moves the focus to the left. If there is no element on the left,
   * focus is moved to the right.
   * @since 1.9.0
   */
  deleteLeft(): Option<Zipper<A>> {
    const len = this.lefts.length
    return fromArray(this.lefts.concat(this.rights), len > 0 ? len - 1 : 0)
  }
  /**
   * Deletes the element at focus and moves the focus to the right. If there is no element on the right,
   * focus is moved to the left.
   * @since 1.9.0
   */

  deleteRight(): Option<Zipper<A>> {
    const lenl = this.lefts.length
    const lenr = this.rights.length
    return fromArray(this.lefts.concat(this.rights), lenr > 0 ? lenl : lenl - 1)
  }
  /**
   * @since 1.9.0
   */
  map<B>(f: (a: A) => B): Zipper<B> {
    return new Zipper(this.lefts.map(f), f(this.focus), this.rights.map(f))
  }
  /**
   * @since 1.9.0
   */
  ap<B>(fab: Zipper<(a: A) => B>): Zipper<B> {
    return new Zipper(array.ap(fab.lefts, this.lefts), fab.focus(this.focus), array.ap(fab.rights, this.rights))
  }
  /**
   * @since 1.9.0
   */
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    return this.rights.reduce(f, f(this.lefts.reduce(f, b), this.focus))
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `new Zipper(${toString(this.lefts)}, ${toString(this.focus)}, ${toString(this.rights)})`
  }
}

/**
 * @since 1.17.0
 */
export const getShow = <A>(S: Show<A>): Show<Zipper<A>> => {
  const SA = getArrayShow(S)
  return {
    show: z => `new Zipper(${SA.show(z.lefts)}, ${S.show(z.focus)}, ${SA.show(z.rights)})`
  }
}

/**
 * @since 1.9.0
 */
export const fromArray = <A>(as: Array<A>, focusIndex: number = 0): Option<Zipper<A>> => {
  if (isEmpty(as) || isOutOfBound(focusIndex, as)) {
    return none
  } else {
    return some(new Zipper(take(focusIndex, as), as[focusIndex], drop(focusIndex + 1, as)))
  }
}

/**
 * @since 1.9.0
 */
export const fromNonEmptyArray = <A>(nea: NonEmptyArray<A>): Zipper<A> => {
  return new Zipper(empty, nea.head, nea.tail)
}

/**
 * @since 1.17.0
 */
export const fromNonEmptyArray2v = <A>(nea: NonEmptyArray2v<A>): Zipper<A> => {
  return new Zipper(empty, nea[0], nea.slice(1))
}

const map = <A, B>(fa: Zipper<A>, f: (a: A) => B): Zipper<B> => {
  return fa.map(f)
}

const of = <A>(a: A): Zipper<A> => {
  return new Zipper(empty, a, empty)
}

const ap = <A, B>(fab: Zipper<(a: A) => B>, fa: Zipper<A>): Zipper<B> => {
  return fa.ap(fab)
}

const reduce = <A, B>(fa: Zipper<A>, b: B, f: (b: B, a: A) => B): B => {
  return fa.reduce(b, f)
}

const foldMap = <M>(M: Monoid<M>) => <A>(fa: Zipper<A>, f: (a: A) => M): M => {
  const lefts = fa.lefts.reduce((acc, a) => M.concat(acc, f(a)), M.empty)
  const rights = fa.rights.reduce((acc, a) => M.concat(acc, f(a)), M.empty)
  return M.concat(M.concat(lefts, f(fa.focus)), rights)
}

const foldr = <A, B>(fa: Zipper<A>, b: B, f: (a: A, b: B) => B): B => {
  const rights = fa.rights.reduceRight((acc, a) => f(a, acc), b)
  const focus = f(fa.focus, rights)
  return fa.lefts.reduceRight((acc, a) => f(a, acc), focus)
}

function traverse<F>(F: Applicative<F>): <A, B>(ta: Zipper<A>, f: (a: A) => HKT<F, B>) => HKT<F, Zipper<B>> {
  const traverseF = array.traverse(F)
  return <A, B>(ta: Zipper<A>, f: (a: A) => HKT<F, B>) =>
    F.ap(
      F.ap(
        F.map(traverseF(ta.lefts, f), lefts => (focus: B) => (rights: Array<B>) => new Zipper(lefts, focus, rights)),
        f(ta.focus)
      ),
      traverseF(ta.rights, f)
    )
}

function sequence<F>(F: Applicative<F>): <A>(ta: Zipper<HKT<F, A>>) => HKT<F, Zipper<A>> {
  const sequenceF = array.sequence(F)
  return <A>(ta: Zipper<HKT<F, A>>) =>
    F.ap(
      F.ap(
        F.map(sequenceF(ta.lefts), lefts => (focus: A) => (rights: Array<A>) => new Zipper(lefts, focus, rights)),
        ta.focus
      ),
      sequenceF(ta.rights)
    )
}

const extract = <A>(fa: Zipper<A>): A => {
  return fa.focus
}

const extend = <A, B>(fa: Zipper<A>, f: (fa: Zipper<A>) => B): Zipper<B> => {
  const lefts = fa.lefts.map((a, i) =>
    f(new Zipper(take(i, fa.lefts), a, snoc(drop(i + 1, fa.lefts), fa.focus).concat(fa.rights)))
  )
  const rights = fa.rights.map((a, i) =>
    f(new Zipper(snoc(fa.lefts, fa.focus).concat(take(i, fa.rights)), a, drop(i + 1, fa.rights)))
  )
  return new Zipper(lefts, f(fa), rights)
}

/**
 * @since 1.9.0
 */
export const getSemigroup = <A>(S: Semigroup<A>): Semigroup<Zipper<A>> => {
  return {
    concat: (x, y) => new Zipper(x.lefts.concat(y.lefts), S.concat(x.focus, y.focus), x.rights.concat(y.rights))
  }
}

/**
 * @since 1.9.0
 */
export const getMonoid = <A>(M: Monoid<A>): Monoid<Zipper<A>> => {
  return {
    ...getSemigroup(M),
    empty: new Zipper(empty, M.empty, empty)
  }
}

/**
 * @since 1.9.0
 */
export const zipper: Applicative1<URI> & Foldable2v1<URI> & Traversable2v1<URI> & Comonad1<URI> = {
  URI,
  map,
  of,
  ap,
  extend,
  extract,
  reduce,
  foldMap,
  foldr,
  traverse,
  sequence
}

/**
 * @file Represents a value of one of two possible types (a disjoint union).
 *
 * An instance of `Either` is either an instance of `Left` or `Right`.
 *
 * A common use of `Either` is as an alternative to `Option` for dealing with possible missing values. In this usage,
 * `None` is replaced with a `Left` which can contain useful information. `Right` takes the place of `Some`. Convention
 * dictates that `Left` is used for failure and `Right` is used for success.
 *
 * For example, you could use `Either<string, number>` to detect whether a received input is a `string` or a `number`.
 *
 * ```ts
 * const parse = (errorMessage: string) => (input: string): Either<string, number> => {
 *   const n = parseInt(input, 10)
 *   return isNaN(n) ? left(errorMessage) : right(n)
 * }
 * ```
 *
 * `Either` is right-biased, which means that `Right` is assumed to be the default case to operate on. If it is `Left`,
 * operations like `map`, `chain`, ... return the `Left` value unchanged:
 *
 * ```ts
 * right(12).map(double) // right(24)
 * left(23).map(double)  // left(23)
 * ```
 */

import { Alt2 }  from  './Alt.ts'
import { Applicative }  from  './Applicative.ts'
import { Bifunctor2 }  from  './Bifunctor.ts'
import { ChainRec2, tailRec }  from  './ChainRec.ts'
import { Compactable2C, Separated }  from  './Compactable.ts'
import { Extend2 }  from  './Extend.ts'
import { Filterable2C }  from  './Filterable.ts'
import { Foldable2v2 }  from  './Foldable2v.ts'
import { Lazy, phantom, Predicate, Refinement, toString, identity }  from  './function.ts'
import { HKT }  from  './HKT.ts'
import { Monad2 }  from  './Monad.ts'
import { Monoid }  from  './Monoid.ts'
import { Option }  from  './Option.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Setoid, fromEquals }  from  './Setoid.ts'
import { Traversable2v2 }  from  './Traversable2v.ts'
import { Validation }  from  './Validation.ts'
import { Witherable2C }  from  './Witherable.ts'
import { MonadThrow2 }  from  './MonadThrow.ts'
import { Show }  from  './Show.ts'

declare module './HKT.ts'
  interface URI2HKT2<L, A> {
    Either: Either<L, A>
  }
}

export const URI = 'Either'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export type Either<L, A> = Left<L, A> | Right<L, A>

/**
 * Left side of `Either`
 */
export class Left<L, A> {
  readonly _tag: 'Left' = 'Left'
  readonly _A!: A
  readonly _L!: L
  readonly _URI!: URI
  constructor(readonly value: L) {}
  /** The given function is applied if this is a `Right` */
  map<B>(f: (a: A) => B): Either<L, B> {
    return this as any
  }
  ap<B>(fab: Either<L, (a: A) => B>): Either<L, B> {
    return (fab.isLeft() ? fab : this) as any
  }
  /**
   * Flipped version of `ap`
   */
  ap_<B, C>(this: Either<L, (b: B) => C>, fb: Either<L, B>): Either<L, C> {
    return fb.ap(this)
  }
  /** Binds the given function across `Right` */
  chain<B>(f: (a: A) => Either<L, B>): Either<L, B> {
    return this as any
  }
  bimap<V, B>(f: (l: L) => V, g: (a: A) => B): Either<V, B> {
    return new Left(f(this.value))
  }
  alt(fy: Either<L, A>): Either<L, A> {
    return fy
  }

  /**
   * Lazy version of `alt`
   *
   * @example
   * import { right }  from  'fp-ts/lib/Either.ts'
   *
   * assert.deepStrictEqual(right(1).orElse(() => right(2)), right(1))
   *
   * @since 1.6.0
   */
  orElse<M>(fy: (l: L) => Either<M, A>): Either<M, A> {
    return fy(this.value)
  }
  extend<B>(f: (ea: Either<L, A>) => B): Either<L, B> {
    return this as any
  }
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    return b
  }
  /** Applies a function to each case in the data structure */
  fold<B>(onLeft: (l: L) => B, onRight: (a: A) => B): B {
    return onLeft(this.value)
  }
  /** Returns the value from this `Right` or the given argument if this is a `Left` */
  getOrElse(a: A): A {
    return a
  }
  /** Returns the value from this `Right` or the result of given argument if this is a `Left` */
  getOrElseL(f: (l: L) => A): A {
    return f(this.value)
  }
  /** Maps the left side of the disjunction */
  mapLeft<M>(f: (l: L) => M): Either<M, A> {
    return new Left(f(this.value))
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `left(${toString(this.value)})`
  }
  /** Returns `true` if the either is an instance of `Left`, `false` otherwise */
  isLeft(): this is Left<L, A> {
    return true
  }
  /** Returns `true` if the either is an instance of `Right`, `false` otherwise */
  isRight(): this is Right<L, A> {
    return false
  }
  /** Swaps the disjunction values */
  swap(): Either<A, L> {
    return new Right(this.value)
  }
  /**
   * Returns `Right` with the existing value of `Right` if this is a `Right` and the given predicate `p` holds for the
   * right value, returns `Left(zero)` if this is a `Right` and the given predicate `p` does not hold for the right
   * value, returns `Left` with the existing value of `Left` if this is a `Left`.
   *
   * @example
   * import { right, left }  from  'fp-ts/lib/Either.ts'
   *
   * assert.deepStrictEqual(right(12).filterOrElse(n => n > 10, -1), right(12))
   * assert.deepStrictEqual(right(7).filterOrElse(n => n > 10, -1), left(-1))
   * assert.deepStrictEqual(left<number, number>(12).filterOrElse(n => n > 10, -1), left(12))
   *
   * @since 1.3.0
   */
  filterOrElse<B extends A>(p: Refinement<A, B>, zero: L): Either<L, B>
  filterOrElse(p: Predicate<A>, zero: L): Either<L, A>
  filterOrElse(_: Predicate<A>, zero: L): Either<L, A> {
    return this
  }
  /**
   * Lazy version of `filterOrElse`
   * @since 1.3.0
   */
  filterOrElseL<B extends A>(p: Refinement<A, B>, zero: (a: A) => L): Either<L, B>
  filterOrElseL(p: Predicate<A>, zero: (a: A) => L): Either<L, A>
  filterOrElseL(_: Predicate<A>, zero: (a: A) => L): Either<L, A> {
    return this
  }
  /**
   * Use `filterOrElse` instead
   * @since 1.6.0
   * @deprecated
   */
  refineOrElse<B extends A>(p: Refinement<A, B>, zero: L): Either<L, B> {
    return this as any
  }
  /**
   * Lazy version of `refineOrElse`
   * Use `filterOrElseL` instead
   * @since 1.6.0
   * @deprecated
   */
  refineOrElseL<B extends A>(p: Refinement<A, B>, zero: (a: A) => L): Either<L, B> {
    return this as any
  }
}

/**
 * Right side of `Either`
 */
export class Right<L, A> {
  readonly _tag: 'Right' = 'Right'
  readonly _A!: A
  readonly _L!: L
  readonly _URI!: URI
  constructor(readonly value: A) {}
  map<B>(f: (a: A) => B): Either<L, B> {
    return new Right(f(this.value))
  }
  ap<B>(fab: Either<L, (a: A) => B>): Either<L, B> {
    return fab.isRight() ? this.map(fab.value) : left(fab.value)
  }
  ap_<B, C>(this: Either<L, (b: B) => C>, fb: Either<L, B>): Either<L, C> {
    return fb.ap(this)
  }
  chain<B>(f: (a: A) => Either<L, B>): Either<L, B> {
    return f(this.value)
  }
  bimap<V, B>(f: (l: L) => V, g: (a: A) => B): Either<V, B> {
    return new Right<V, B>(g(this.value))
  }
  alt(fy: Either<L, A>): Either<L, A> {
    return this
  }
  orElse<M>(fy: (l: L) => Either<M, A>): Either<M, A> {
    return this as any
  }
  extend<B>(f: (ea: Either<L, A>) => B): Either<L, B> {
    return new Right(f(this))
  }
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    return f(b, this.value)
  }
  fold<B>(onLeft: (l: L) => B, onRight: (a: A) => B): B {
    return onRight(this.value)
  }
  getOrElse(a: A): A {
    return this.value
  }
  getOrElseL(f: (l: L) => A): A {
    return this.value
  }
  mapLeft<M>(f: (l: L) => M): Either<M, A> {
    return new Right(this.value)
  }
  inspect(): string {
    return this.toString()
  }
  toString(): string {
    return `right(${toString(this.value)})`
  }
  isLeft(): this is Left<L, A> {
    return false
  }
  isRight(): this is Right<L, A> {
    return true
  }
  swap(): Either<A, L> {
    return new Left(this.value)
  }
  filterOrElse<B extends A>(p: Refinement<A, B>, zero: L): Either<L, B>
  filterOrElse(p: Predicate<A>, zero: L): Either<L, A>
  filterOrElse(p: Predicate<A>, zero: L): Either<L, A> {
    return p(this.value) ? this : left(zero)
  }
  filterOrElseL<B extends A>(p: Refinement<A, B>, zero: (a: A) => L): Either<L, B>
  filterOrElseL(p: Predicate<A>, zero: (a: A) => L): Either<L, A>
  filterOrElseL(p: Predicate<A>, zero: (a: A) => L): Either<L, A> {
    return p(this.value) ? this : left(zero(this.value))
  }
  refineOrElse<B extends A>(p: Refinement<A, B>, zero: L): Either<L, B> {
    return p(this.value) ? (this as any) : left(zero)
  }
  refineOrElseL<B extends A>(p: Refinement<A, B>, zero: (a: A) => L): Either<L, B> {
    return p(this.value) ? (this as any) : left(zero(this.value))
  }
}

/**
 * @since 1.17.0
 */
export const getShow = <L, A>(SL: Show<L>, SA: Show<A>): Show<Either<L, A>> => {
  return {
    show: e => e.fold(l => `left(${SL.show(l)})`, a => `right(${SA.show(a)})`)
  }
}

/**
 * @since 1.0.0
 */
export const getSetoid = <L, A>(SL: Setoid<L>, SA: Setoid<A>): Setoid<Either<L, A>> => {
  return fromEquals((x, y) =>
    x.isLeft() ? y.isLeft() && SL.equals(x.value, y.value) : y.isRight() && SA.equals(x.value, y.value)
  )
}

/**
 * Semigroup returning the left-most non-`Left` value. If both operands are `Right`s then the inner values are
 * appended using the provided `Semigroup`
 *
 * @example
 * import { getSemigroup, left, right }  from  'fp-ts/lib/Either.ts'
 * import { semigroupSum }  from  'fp-ts/lib/Semigroup.ts'
 *
 * const S = getSemigroup<string, number>(semigroupSum)
 * assert.deepStrictEqual(S.concat(left('a'), left('b')), left('a'))
 * assert.deepStrictEqual(S.concat(left('a'), right(2)), right(2))
 * assert.deepStrictEqual(S.concat(right(1), left('b')), right(1))
 * assert.deepStrictEqual(S.concat(right(1), right(2)), right(3))
 *
 *
 * @since 1.7.0
 */
export const getSemigroup = <L, A>(S: Semigroup<A>): Semigroup<Either<L, A>> => {
  return {
    concat: (x, y) => (y.isLeft() ? x : x.isLeft() ? y : right(S.concat(x.value, y.value)))
  }
}

/**
 * `Apply` semigroup
 *
 * @example
 * import { getApplySemigroup, left, right }  from  'fp-ts/lib/Either.ts'
 * import { semigroupSum }  from  'fp-ts/lib/Semigroup.ts'
 *
 * const S = getApplySemigroup<string, number>(semigroupSum)
 * assert.deepStrictEqual(S.concat(left('a'), left('b')), left('a'))
 * assert.deepStrictEqual(S.concat(left('a'), right(2)), left('a'))
 * assert.deepStrictEqual(S.concat(right(1), left('b')), left('b'))
 * assert.deepStrictEqual(S.concat(right(1), right(2)), right(3))
 *
 *
 * @since 1.7.0
 */
export const getApplySemigroup = <L, A>(S: Semigroup<A>): Semigroup<Either<L, A>> => {
  return {
    concat: (x, y) => (x.isLeft() ? x : y.isLeft() ? y : right(S.concat(x.value, y.value)))
  }
}

/**
 * @since 1.7.0
 */
export const getApplyMonoid = <L, A>(M: Monoid<A>): Monoid<Either<L, A>> => {
  return {
    ...getApplySemigroup(M),
    empty: right(M.empty)
  }
}

const map = <L, A, B>(fa: Either<L, A>, f: (a: A) => B): Either<L, B> => {
  return fa.map(f)
}

const ap = <L, A, B>(fab: Either<L, (a: A) => B>, fa: Either<L, A>): Either<L, B> => {
  return fa.ap(fab)
}

const chain = <L, A, B>(fa: Either<L, A>, f: (a: A) => Either<L, B>): Either<L, B> => {
  return fa.chain(f)
}

const bimap = <L, V, A, B>(fla: Either<L, A>, f: (u: L) => V, g: (a: A) => B): Either<V, B> => {
  return fla.bimap(f, g)
}

const alt = <L, A>(fx: Either<L, A>, fy: Either<L, A>): Either<L, A> => {
  return fx.alt(fy)
}

const extend = <L, A, B>(ea: Either<L, A>, f: (ea: Either<L, A>) => B): Either<L, B> => {
  return ea.extend(f)
}

const reduce = <L, A, B>(fa: Either<L, A>, b: B, f: (b: B, a: A) => B): B => {
  return fa.reduce(b, f)
}

const foldMap = <M>(M: Monoid<M>) => <L, A>(fa: Either<L, A>, f: (a: A) => M): M => {
  return fa.isLeft() ? M.empty : f(fa.value)
}

const foldr = <L, A, B>(fa: Either<L, A>, b: B, f: (a: A, b: B) => B): B => {
  return fa.isLeft() ? b : f(fa.value, b)
}

const traverse = <F>(F: Applicative<F>) => <L, A, B>(
  ta: Either<L, A>,
  f: (a: A) => HKT<F, B>
): HKT<F, Either<L, B>> => {
  return ta.isLeft() ? F.of(left(ta.value)) : F.map<B, Either<L, B>>(f(ta.value), of)
}

const sequence = <F>(F: Applicative<F>) => <L, A>(ta: Either<L, HKT<F, A>>): HKT<F, Either<L, A>> => {
  return ta.isLeft() ? F.of(left(ta.value)) : F.map<A, Either<L, A>>(ta.value, right)
}

const chainRec = <L, A, B>(a: A, f: (a: A) => Either<L, Either<A, B>>): Either<L, B> => {
  return tailRec(e => {
    if (e.isLeft()) {
      return right(left(e.value))
    } else {
      const r = e.value
      return r.isLeft() ? left(f(r.value)) : right(right(r.value))
    }
  }, f(a))
}

/**
 * Constructs a new `Either` holding a `Left` value. This usually represents a failure, due to the right-bias of this
 * structure
 *
 * @since 1.0.0
 */
export const left = <L, A>(l: L): Either<L, A> => {
  return new Left(l)
}

/**
 * Constructs a new `Either` holding a `Right` value. This usually represents a successful value due to the right bias
 * of this structure
 *
 * @since 1.0.0
 */
export const right = <L, A>(a: A): Either<L, A> => {
  return new Right<L, A>(a)
}

const of = right

/**
 * @since 1.0.0
 */
export function fromPredicate<L, A, B extends A>(
  predicate: Refinement<A, B>,
  onFalse: (a: A) => L
): (a: A) => Either<L, B>
export function fromPredicate<L, A>(predicate: Predicate<A>, onFalse: (a: A) => L): (a: A) => Either<L, A>
export function fromPredicate<L, A>(predicate: Predicate<A>, onFalse: (a: A) => L): (a: A) => Either<L, A> {
  return a => (predicate(a) ? right(a) : left(onFalse(a)))
}

/**
 * Use `fromPredicate` instead
 *
 * @since 1.6.0
 * @deprecated
 */
export const fromRefinement = <L, A, B extends A>(refinement: Refinement<A, B>, onFalse: (a: A) => L) => (
  a: A
): Either<L, B> => {
  return refinement(a) ? right(a) : left(onFalse(a))
}

/**
 * Takes a default and a `Option` value, if the value is a `Some`, turn it into a `Right`, if the value is a `None` use
 * the provided default as a `Left`
 *
 * @since 1.0.0
 */
export const fromOption = <L>(defaultValue: L) => <A>(fa: Option<A>): Either<L, A> => {
  return fa.isNone() ? left(defaultValue) : right(fa.value)
}

/**
 * Lazy version of `fromOption`
 *
 * @since 1.3.0
 */
export const fromOptionL = <L>(defaultValue: Lazy<L>) => <A>(fa: Option<A>): Either<L, A> => {
  return fa.isNone() ? left(defaultValue()) : right(fa.value)
}

/**
 * Takes a default and a nullable value, if the value is not nully, turn it into a `Right`, if the value is nully use
 * the provided default as a `Left`
 *
 * @since 1.0.0
 */
export const fromNullable = <L>(defaultValue: L) => <A>(a: A | null | undefined): Either<L, A> => {
  return a == null ? left(defaultValue) : right(a)
}

/**
 * Default value for the optional `onerror` argument of `tryCatch`
 *
 * @since 1.0.0
 */
export const toError = (e: unknown): Error => {
  if (e instanceof Error) {
    return e
  } else {
    return new Error(String(e))
  }
}

/**
 * Use `tryCatch2v` instead
 *
 * @since 1.0.0
 * @deprecated
 */
export const tryCatch = <A>(f: Lazy<A>, onerror: (e: unknown) => Error = toError): Either<Error, A> => {
  return tryCatch2v(f, onerror)
}

/**
 * Constructs a new `Either` from a function that might throw
 *
 * @example
 * import { Either, left, right, tryCatch2v }  from  'fp-ts/lib/Either.ts'
 *
 * const unsafeHead = <A>(as: Array<A>): A => {
 *   if (as.length > 0) {
 *     return as[0]
 *   } else {
 *     throw new Error('empty array')
 *   }
 * }
 *
 * const head = <A>(as: Array<A>): Either<Error, A> => {
 *   return tryCatch2v(() => unsafeHead(as), e => (e instanceof Error ? e : new Error('unknown error')))
 * }
 *
 * assert.deepStrictEqual(head([]), left(new Error('empty array')))
 * assert.deepStrictEqual(head([1, 2, 3]), right(1))
 *
 * @since 1.11.0
 */
export const tryCatch2v = <L, A>(f: Lazy<A>, onerror: (e: unknown) => L): Either<L, A> => {
  try {
    return right(f())
  } catch (e) {
    return left(onerror(e))
  }
}

/**
 * @since 1.0.0
 */
export const fromValidation = <L, A>(fa: Validation<L, A>): Either<L, A> => {
  return fa.isFailure() ? left(fa.value) : right(fa.value)
}

/**
 * Returns `true` if the either is an instance of `Left`, `false` otherwise
 *
 * @since 1.0.0
 */
export const isLeft = <L, A>(fa: Either<L, A>): fa is Left<L, A> => {
  return fa.isLeft()
}

/**
 * Returns `true` if the either is an instance of `Right`, `false` otherwise
 *
 * @since 1.0.0
 */
export const isRight = <L, A>(fa: Either<L, A>): fa is Right<L, A> => {
  return fa.isRight()
}

/**
 * Builds `Compactable` instance for `Either` given `Monoid` for the left side
 *
 * @since 1.7.0
 */
export function getCompactable<L>(ML: Monoid<L>): Compactable2C<URI, L> {
  const compact = <A>(fa: Either<L, Option<A>>): Either<L, A> => {
    if (fa.isLeft()) {
      return fa as any
    }
    if (fa.value.isNone()) {
      return left(ML.empty)
    }
    return right(fa.value.value)
  }
  const separate = <A, B>(fa: Either<L, Either<A, B>>): Separated<Either<L, A>, Either<L, B>> => {
    if (fa.isLeft()) {
      return {
        left: fa as any,
        right: fa as any
      }
    }
    if (fa.value.isLeft()) {
      return {
        left: right(fa.value.value),
        right: left(ML.empty)
      }
    }
    return {
      left: left(ML.empty),
      right: right(fa.value.value)
    }
  }

  return {
    URI,
    _L: phantom,
    compact,
    separate
  }
}

/**
 * Builds `Filterable` instance for `Either` given `Monoid` for the left side
 *
 * @since 1.7.0
 */
export function getFilterable<L>(ML: Monoid<L>): Filterable2C<URI, L> {
  const C = getCompactable(ML)
  const partitionMap = <RL, RR, A>(
    fa: Either<L, A>,
    f: (a: A) => Either<RL, RR>
  ): Separated<Either<L, RL>, Either<L, RR>> => {
    if (fa.isLeft()) {
      return {
        left: fa as any,
        right: fa as any
      }
    }
    const e = f(fa.value)
    if (e.isLeft()) {
      return {
        left: right(e.value),
        right: left(ML.empty)
      }
    }
    return {
      left: left(ML.empty),
      right: right(e.value)
    }
  }
  const partition = <A>(fa: Either<L, A>, p: Predicate<A>): Separated<Either<L, A>, Either<L, A>> => {
    if (fa.isLeft()) {
      return {
        left: fa,
        right: fa
      }
    }
    if (p(fa.value)) {
      return {
        left: left(ML.empty),
        right: right(fa.value)
      }
    }
    return {
      left: right(fa.value),
      right: left(ML.empty)
    }
  }
  const filterMap = <A, B>(fa: Either<L, A>, f: (a: A) => Option<B>): Either<L, B> => {
    if (fa.isLeft()) {
      return fa as any
    }
    const optionB = f(fa.value)
    if (optionB.isSome()) {
      return right(optionB.value)
    }
    return left(ML.empty)
  }
  const filter = <A>(fa: Either<L, A>, p: Predicate<A>): Either<L, A> => fa.filterOrElse(p, ML.empty)
  return {
    ...C,
    map,
    partitionMap,
    filterMap,
    partition,
    filter
  }
}

/**
 * Builds `Witherable` instance for `Either` given `Monoid` for the left side
 *
 * @since 1.7.0
 */
export function getWitherable<L>(ML: Monoid<L>): Witherable2C<URI, L> {
  const filterableEither = getFilterable(ML)

  const wither = <F>(
    F: Applicative<F>
  ): (<A, B>(wa: Either<L, A>, f: (a: A) => HKT<F, Option<B>>) => HKT<F, Either<L, B>>) => {
    const traverseF = traverse(F)
    return (wa, f) => F.map(traverseF(wa, f), filterableEither.compact)
  }

  const wilt = <F>(
    F: Applicative<F>
  ): (<RL, RR, A>(
    wa: Either<L, A>,
    f: (a: A) => HKT<F, Either<RL, RR>>
  ) => HKT<F, Separated<Either<L, RL>, Either<L, RR>>>) => {
    const traverseF = traverse(F)
    return (wa, f) => F.map(traverseF(wa, f), filterableEither.separate)
  }

  return {
    ...filterableEither,
    traverse,
    reduce,
    wither,
    wilt
  }
}

/**
 * Converts a JavaScript Object Notation (JSON) string into an object.
 *
 * @example
 * import { parseJSON, toError }  from  'fp-ts/lib/Either.ts'
 *
 * assert.deepStrictEqual(parseJSON('{"a":1}', toError).value, { a: 1 })
 * assert.deepStrictEqual(parseJSON('{"a":}', toError).value, new SyntaxError('Unexpected token } in JSON at position 5'))
 *
 * @since 1.16.0
 */
export const parseJSON = <L>(s: string, onError: (reason: unknown) => L): Either<L, unknown> => {
  return tryCatch2v(() => JSON.parse(s), onError)
}

/**
 * Converts a JavaScript value to a JavaScript Object Notation (JSON) string.
 *
 * @example
 * import { stringifyJSON, toError }  from  'fp-ts/lib/Either.ts'
 *
 * assert.deepStrictEqual(stringifyJSON({ a: 1 }, toError).value, '{"a":1}')
 * const circular: any = { ref: null }
 * circular.ref = circular
 * assert.deepStrictEqual(stringifyJSON(circular, toError).value, new TypeError('Converting circular structure to JSON'))
 *
 * @since 1.16.0
 */
export const stringifyJSON = <L>(u: unknown, onError: (reason: unknown) => L): Either<L, string> => {
  return tryCatch2v(() => JSON.stringify(u), onError)
}

const throwError = left

const fromEither = identity

/**
 * @since 1.0.0
 */
export const either: Monad2<URI> &
  Foldable2v2<URI> &
  Traversable2v2<URI> &
  Bifunctor2<URI> &
  Alt2<URI> &
  Extend2<URI> &
  ChainRec2<URI> &
  MonadThrow2<URI> = {
  URI,
  map,
  of,
  ap,
  chain,
  reduce,
  foldMap,
  foldr,
  traverse,
  sequence,
  bimap,
  alt,
  extend,
  chainRec,
  throwError,
  fromEither,
  fromOption: (o, e) => (o.isNone() ? throwError(e) : of(o.value))
}

import { Applicative, Applicative1, Applicative2, Applicative2C, Applicative3, Applicative3C }  from  './Applicative.ts'
import { applyFirst }  from  './Apply.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monad, Monad1, Monad2, Monad2C, Monad3, Monad3C }  from  './Monad.ts'
import { Monoid, unsafeMonoidArray }  from  './Monoid.ts'
import { Option, none, some }  from  './Option.ts'
import { Ord, max, min }  from  './Ord.ts'
import { Plus, Plus1, Plus2, Plus2C, Plus3, Plus3C }  from  './Plus.ts'
import { Semiring }  from  './Semiring.ts'
import { Setoid }  from  './Setoid.ts'
import { Predicate }  from  './function.ts'

/**
 * Use `Foldable2v`
 * @since 1.0.0
 * @deprecated
 */
export interface Foldable<F> {
  readonly URI: F
  readonly reduce: <A, B>(fa: HKT<F, A>, b: B, f: (b: B, a: A) => B) => B
}

export interface Foldable1<F extends URIS> {
  readonly URI: F
  readonly reduce: <A, B>(fa: Type<F, A>, b: B, f: (b: B, a: A) => B) => B
}

export interface Foldable2<F extends URIS2> {
  readonly URI: F
  readonly reduce: <L, A, B>(fa: Type2<F, L, A>, b: B, f: (b: B, a: A) => B) => B
}

export interface Foldable3<F extends URIS3> {
  readonly URI: F
  readonly reduce: <U, L, A, B>(fa: Type3<F, U, L, A>, b: B, f: (b: B, a: A) => B) => B
}

export interface Foldable2C<F extends URIS2, L> {
  readonly URI: F
  readonly _L: L
  readonly reduce: <A, B>(fa: Type2<F, L, A>, b: B, f: (b: B, a: A) => B) => B
}

export interface Foldable3C<F extends URIS3, U, L> {
  readonly URI: F
  readonly _L: L
  readonly _U: U
  readonly reduce: <A, B>(fa: Type3<F, U, L, A>, b: B, f: (b: B, a: A) => B) => B
}

export interface FoldableComposition<F, G> {
  readonly reduce: <A, B>(fga: HKT<F, HKT<G, A>>, b: B, f: (b: B, a: A) => B) => B
}

export interface FoldableComposition11<F extends URIS, G extends URIS> {
  readonly reduce: <A, B>(fga: Type<F, Type<G, A>>, b: B, f: (b: B, a: A) => B) => B
}

export interface FoldableComposition12<F extends URIS, G extends URIS2> {
  readonly reduce: <LG, A, B>(fga: Type<F, Type2<G, LG, A>>, b: B, f: (b: B, a: A) => B) => B
}

export interface FoldableComposition12C<F extends URIS, G extends URIS2, LG> {
  readonly reduce: <A, B>(fga: Type<F, Type2<G, LG, A>>, b: B, f: (b: B, a: A) => B) => B
}

export interface FoldableComposition21<F extends URIS2, G extends URIS> {
  readonly reduce: <LF, A, B>(fga: Type2<F, LF, Type<G, A>>, b: B, f: (b: B, a: A) => B) => B
}

export interface FoldableComposition2C1<F extends URIS2, G extends URIS, LF> {
  readonly reduce: <A, B>(fga: Type2<F, LF, Type<G, A>>, b: B, f: (b: B, a: A) => B) => B
}

export interface FoldableComposition22<F extends URIS2, G extends URIS2> {
  readonly reduce: <LF, LG, A, B>(fga: Type2<F, LF, Type2<G, LG, A>>, b: B, f: (b: B, a: A) => B) => B
}

export interface FoldableComposition22C<F extends URIS2, G extends URIS2, LG> {
  readonly reduce: <LF, A, B>(fga: Type2<F, LF, Type2<G, LG, A>>, b: B, f: (b: B, a: A) => B) => B
}

export interface FoldableComposition3C1<F extends URIS3, G extends URIS, UF, LF> {
  readonly reduce: <A, B>(fga: Type3<F, UF, LF, Type<G, A>>, b: B, f: (b: B, a: A) => B) => B
}

/**
 * @since 1.0.0
 */
export function getFoldableComposition<F extends URIS3, G extends URIS, UF, LF>(
  F: Foldable3C<F, UF, LF>,
  G: Foldable1<G>
): FoldableComposition3C1<F, G, UF, LF>
export function getFoldableComposition<F extends URIS2, G extends URIS2, LG>(
  F: Foldable2C<F, LG>,
  G: Foldable2<G>
): FoldableComposition22C<F, G, LG>
export function getFoldableComposition<F extends URIS2, G extends URIS2>(
  F: Foldable2<F>,
  G: Foldable2<G>
): FoldableComposition22<F, G>
export function getFoldableComposition<F extends URIS2, G extends URIS>(
  F: Foldable2<F>,
  G: Foldable1<G>
): FoldableComposition21<F, G>
export function getFoldableComposition<F extends URIS, G extends URIS2>(
  F: Foldable1<F>,
  G: Foldable2<G>
): FoldableComposition12<F, G>
export function getFoldableComposition<F extends URIS, G extends URIS>(
  F: Foldable1<F>,
  G: Foldable1<G>
): FoldableComposition11<F, G>
// tslint:disable-next-line: deprecation
export function getFoldableComposition<F, G>(F: Foldable<F>, G: Foldable<G>): FoldableComposition<F, G>
// tslint:disable-next-line: deprecation
export function getFoldableComposition<F, G>(F: Foldable<F>, G: Foldable<G>): FoldableComposition<F, G> {
  return {
    reduce: (fga, b, f) => F.reduce(fga, b, (b, ga) => G.reduce(ga, b, f))
  }
}

/**
 * A default implementation of `foldMap` using `foldl`.
 * Map each element of the structure to a monoid, and combine the results.
 *
 * @since 1.0.0
 */
export function foldMap<F extends URIS3, M>(
  F: Foldable3<F>,
  M: Monoid<M>
): <U, L, A>(fa: Type3<F, U, L, A>, f: (a: A) => M) => M
export function foldMap<F extends URIS3, M, U, L>(
  F: Foldable3C<F, U, L>,
  M: Monoid<M>
): <A>(fa: Type3<F, U, L, A>, f: (a: A) => M) => M
export function foldMap<F extends URIS2, M>(
  F: Foldable2<F>,
  M: Monoid<M>
): <L, A>(fa: Type2<F, L, A>, f: (a: A) => M) => M
export function foldMap<F extends URIS2, M, L>(
  F: Foldable2C<F, L>,
  M: Monoid<M>
): <A>(fa: Type2<F, L, A>, f: (a: A) => M) => M
export function foldMap<F extends URIS, M>(F: Foldable1<F>, M: Monoid<M>): <A>(fa: Type<F, A>, f: (a: A) => M) => M
// tslint:disable-next-line: deprecation
export function foldMap<F, M>(F: Foldable<F>, M: Monoid<M>): <A>(fa: HKT<F, A>, f: (a: A) => M) => M
// tslint:disable-next-line: deprecation
export function foldMap<F, M>(F: Foldable<F>, M: Monoid<M>): <A>(fa: HKT<F, A>, f: (a: A) => M) => M {
  return (fa, f) => F.reduce(fa, M.empty, (acc, x) => M.concat(acc, f(x)))
}

/**
 * A default implementation of `foldr` using `foldMap`
 *
 * @since 1.0.0
 */
export function foldr<F extends URIS3>(
  F: Foldable3<F>
): <U, L, A, B>(fa: Type3<F, U, L, A>, b: B, f: (a: A, b: B) => B) => B
export function foldr<F extends URIS3, U, L>(
  F: Foldable3C<F, U, L>
): <A, B>(fa: Type3<F, U, L, A>, b: B, f: (a: A, b: B) => B) => B
export function foldr<F extends URIS2>(F: Foldable2<F>): <L, A, B>(fa: Type2<F, L, A>, b: B, f: (a: A, b: B) => B) => B
export function foldr<F extends URIS2, L>(
  F: Foldable2C<F, L>
): <A, B>(fa: Type2<F, L, A>, b: B, f: (a: A, b: B) => B) => B
export function foldr<F extends URIS>(F: Foldable1<F>): <A, B>(fa: Type<F, A>, b: B, f: (a: A, b: B) => B) => B
// tslint:disable-next-line: deprecation
export function foldr<F>(F: Foldable<F>): <A, B>(fa: HKT<F, A>, b: B, f: (a: A, b: B) => B) => B
// tslint:disable-next-line: deprecation
export function foldr<F>(F: Foldable<F>): <A, B>(fa: HKT<F, A>, b: B, f: (a: A, b: B) => B) => B {
  const toArrayF = toArray(F)
  return (fa, b, f) => toArrayF(fa).reduceRight((acc, a) => f(a, acc), b)
}

/**
 * @since 1.0.0
 */
export function fold<F extends URIS3, M>(F: Foldable3<F>, M: Monoid<M>): <U, L>(fa: Type3<F, U, L, M>) => M
export function fold<F extends URIS3, M, U, L>(F: Foldable3C<F, U, L>, M: Monoid<M>): (fa: Type3<F, U, L, M>) => M
export function fold<F extends URIS2, M>(F: Foldable2<F>, M: Monoid<M>): <L>(fa: Type2<F, L, M>) => M
export function fold<F extends URIS2, M, L>(F: Foldable2C<F, L>, M: Monoid<M>): (fa: Type2<F, L, M>) => M
export function fold<F extends URIS, M>(F: Foldable1<F>, M: Monoid<M>): (fa: Type<F, M>) => M
// tslint:disable-next-line: deprecation
export function fold<F, M>(F: Foldable<F>, M: Monoid<M>): (fa: HKT<F, M>) => M
// tslint:disable-next-line: deprecation
export function fold<F, M>(F: Foldable<F>, M: Monoid<M>): (fa: HKT<F, M>) => M {
  return fa => F.reduce(fa, M.empty, M.concat)
}

/**
 * Similar to 'reduce', but the result is encapsulated in a monad.
 *
 * Note: this function is not generally stack-safe, e.g., for monads which build up thunks a la `IO`.
 *
 * @since 1.0.0
 */
export function foldM<F extends URIS, M extends URIS3>(
  F: Foldable1<F>,
  M: Monad3<M>
): <U, L, A, B>(f: (b: B, a: A) => Type3<M, U, L, B>, b: B, fa: Type<F, A>) => Type3<M, U, L, B>
export function foldM<F extends URIS, M extends URIS3, U, L>(
  F: Foldable1<F>,
  M: Monad3C<M, U, L>
): <A, B>(f: (b: B, a: A) => Type3<M, U, L, B>, b: B, fa: Type<F, A>) => Type3<M, U, L, B>
export function foldM<F extends URIS, M extends URIS2>(
  F: Foldable1<F>,
  M: Monad2<M>
): <L, A, B>(f: (b: B, a: A) => Type2<M, L, B>, b: B, fa: Type<F, A>) => Type2<M, L, B>
export function foldM<F extends URIS, M extends URIS2, L>(
  F: Foldable1<F>,
  M: Monad2C<M, L>
): <A, B>(f: (b: B, a: A) => Type2<M, L, B>, b: B, fa: Type<F, A>) => Type2<M, L, B>
export function foldM<F extends URIS, M extends URIS>(
  F: Foldable1<F>,
  M: Monad1<M>
): <A, B>(f: (b: B, a: A) => Type<M, B>, b: B, fa: Type<F, A>) => Type<M, B>
export function foldM<F, M>(
  // tslint:disable-next-line: deprecation
  F: Foldable<F>,
  M: Monad<M>
): <A, B>(f: (b: B, a: A) => HKT<M, B>, b: B, fa: HKT<F, A>) => HKT<M, B>
export function foldM<F, M>(
  // tslint:disable-next-line: deprecation
  F: Foldable<F>,
  M: Monad<M>
): <A, B>(f: (b: B, a: A) => HKT<M, B>, b: B, fa: HKT<F, A>) => HKT<M, B> {
  return (f, b, fa) => F.reduce(fa, M.of(b), (mb, a) => M.chain(mb, b => f(b, a)))
}

/**
 * Use `traverse` instead
 *
 * @since 1.0.0
 * @deprecated
 */
export function traverse_<M extends URIS3, F extends URIS>(
  M: Applicative3<M>,
  F: Foldable1<F>
): <U, L, A, B>(f: (a: A) => Type3<M, U, L, B>, fa: Type<F, A>) => Type3<M, U, L, void>
export function traverse_<M extends URIS3, F extends URIS, U, L>(
  M: Applicative3C<M, U, L>,
  F: Foldable1<F>
): <A, B>(f: (a: A) => Type3<M, U, L, B>, fa: Type<F, A>) => Type3<M, U, L, void>
export function traverse_<M extends URIS2, F extends URIS>(
  M: Applicative2<M>,
  F: Foldable1<F>
): <L, A, B>(f: (a: A) => Type2<M, L, B>, fa: Type<F, A>) => Type2<M, L, void>
export function traverse_<M extends URIS2, F extends URIS, L>(
  M: Applicative2C<M, L>,
  F: Foldable1<F>
): <A, B>(f: (a: A) => Type2<M, L, B>, fa: Type<F, A>) => Type2<M, L, void>
export function traverse_<M extends URIS, F extends URIS>(
  M: Applicative1<M>,
  F: Foldable1<F>
): <A, B>(f: (a: A) => Type<M, B>, fa: Type<F, A>) => Type<M, void>
export function traverse_<M, F>(
  M: Applicative<M>,
  // tslint:disable-next-line: deprecation
  F: Foldable<F>
): <A, B>(f: (a: A) => HKT<M, B>, fa: HKT<F, A>) => HKT<M, void>
export function traverse_<M, F>(
  M: Applicative<M>,
  // tslint:disable-next-line: deprecation
  F: Foldable<F>
): <A, B>(f: (a: A) => HKT<M, B>, fa: HKT<F, A>) => HKT<M, void> {
  const toArrayF = toArray(F)
  const applyFirstM = applyFirst(M)
  const initialValue = M.of(undefined)
  return (f, fa) => toArrayF(fa).reduce((mu, a) => applyFirstM(mu, f(a)), initialValue)
}

/**
 * Perform all of the effects in some data structure in the order given by the `Foldable` instance, ignoring the final result.
 *
 * @since 1.0.0
 */
export function sequence_<M extends URIS3, F extends URIS>(
  M: Applicative3<M>,
  F: Foldable1<F>
): <U, L, A>(fa: Type<F, Type3<M, U, L, A>>) => Type3<M, U, L, void>
export function sequence_<M extends URIS3, F extends URIS, U, L>(
  M: Applicative3C<M, U, L>,
  F: Foldable1<F>
): <A>(fa: Type<F, Type3<M, U, L, A>>) => Type3<M, U, L, void>
export function sequence_<M extends URIS2, F extends URIS>(
  M: Applicative2<M>,
  F: Foldable1<F>
): <L, A>(fa: Type<F, Type2<M, L, A>>) => Type2<M, L, void>
export function sequence_<M extends URIS2, F extends URIS, L>(
  M: Applicative2C<M, L>,
  F: Foldable1<F>
): <A>(fa: Type<F, Type2<M, L, A>>) => Type2<M, L, void>
export function sequence_<M extends URIS, F extends URIS>(
  M: Applicative1<M>,
  F: Foldable1<F>
): <A>(fa: Type<F, Type<M, A>>) => Type<M, void>
// tslint:disable-next-line: deprecation
export function sequence_<M, F>(M: Applicative<M>, F: Foldable<F>): <A>(fa: HKT<F, HKT<M, A>>) => HKT<M, void>
// tslint:disable-next-line: deprecation
export function sequence_<M, F>(M: Applicative<M>, F: Foldable<F>): <A>(fa: HKT<F, HKT<M, A>>) => HKT<M, void> {
  const traverse_MF = traverse_(M, F)
  return fa => traverse_MF(ma => ma, fa)
}

/**
 * Combines a collection of elements using the `Alt` operation
 *
 * @since 1.0.0
 */
export function oneOf<F extends URIS, P extends URIS3>(
  F: Foldable1<F>,
  P: Plus3<P>
): <U, L, A>(fga: Type<F, Type3<P, U, L, A>>) => Type3<P, U, L, A>
export function oneOf<F extends URIS, P extends URIS3, U, L>(
  F: Foldable1<F>,
  P: Plus3C<P, U, L>
): <A>(fga: Type<F, Type3<P, U, L, A>>) => Type3<P, U, L, A>
export function oneOf<F extends URIS, P extends URIS2>(
  F: Foldable1<F>,
  P: Plus2<P>
): <L, A>(fga: Type<F, Type2<P, L, A>>) => Type2<P, L, A>
export function oneOf<F extends URIS, P extends URIS2, L>(
  F: Foldable1<F>,
  P: Plus2C<P, L>
): <A>(fga: Type<F, Type2<P, L, A>>) => Type2<P, L, A>
export function oneOf<F extends URIS, P extends URIS>(
  F: Foldable1<F>,
  P: Plus1<P>
): <A>(fga: Type<F, Type<P, A>>) => Type<P, A>
// tslint:disable-next-line: deprecation
export function oneOf<F, P>(F: Foldable<F>, P: Plus<P>): <A>(fga: HKT<F, HKT<P, A>>) => HKT<P, A>
// tslint:disable-next-line: deprecation
export function oneOf<F, P>(F: Foldable<F>, P: Plus<P>): <A>(fga: HKT<F, HKT<P, A>>) => HKT<P, A> {
  return fga => F.reduce(fga, P.zero(), (acc, a) => P.alt(acc, a))
}

type Acc<M> = { init: boolean; acc: M }

/**
 * Fold a data structure, accumulating values in some `Monoid`, combining adjacent elements using the specified separator
 *
 * @since 1.0.0
 */
export function intercalate<F extends URIS3, M>(
  F: Foldable3<F>,
  M: Monoid<M>
): (sep: M) => <U, L>(fm: Type3<F, U, L, M>) => M
export function intercalate<F extends URIS3, M, U, L>(
  F: Foldable3C<F, U, L>,
  M: Monoid<M>
): (sep: M) => (fm: Type3<F, U, L, M>) => M
export function intercalate<F extends URIS2, M>(F: Foldable2<F>, M: Monoid<M>): (sep: M) => <L>(fm: Type2<F, L, M>) => M
export function intercalate<F extends URIS2, M, L>(
  F: Foldable2C<F, L>,
  M: Monoid<M>
): (sep: M) => (fm: Type2<F, L, M>) => M
export function intercalate<F extends URIS, M>(F: Foldable1<F>, M: Monoid<M>): (sep: M) => (fm: Type<F, M>) => M
// tslint:disable-next-line: deprecation
export function intercalate<F, M>(F: Foldable<F>, M: Monoid<M>): (sep: M) => (fm: HKT<F, M>) => M
// tslint:disable-next-line: deprecation
export function intercalate<F, M>(F: Foldable<F>, M: Monoid<M>): (sep: M) => (fm: HKT<F, M>) => M {
  return sep => {
    function go({ init, acc }: Acc<M>, x: M): Acc<M> {
      return init ? { init: false, acc: x } : { init: false, acc: M.concat(M.concat(acc, sep), x) }
    }
    return fm => F.reduce(fm, { init: true, acc: M.empty }, go).acc
  }
}

/**
 * Find the sum of the numeric values in a data structure
 *
 * @since 1.0.0
 */
export function sum<F extends URIS3, A>(F: Foldable3<F>, S: Semiring<A>): <U, L>(fa: Type3<F, U, L, A>) => A
export function sum<F extends URIS3, A, U, L>(F: Foldable3C<F, U, L>, S: Semiring<A>): (fa: Type3<F, U, L, A>) => A
export function sum<F extends URIS2, A>(F: Foldable2<F>, S: Semiring<A>): <L>(fa: Type2<F, L, A>) => A
export function sum<F extends URIS2, A, L>(F: Foldable2C<F, L>, S: Semiring<A>): (fa: Type2<F, L, A>) => A
export function sum<F extends URIS, A>(F: Foldable1<F>, S: Semiring<A>): (fa: Type<F, A>) => A
// tslint:disable-next-line: deprecation
export function sum<F, A>(F: Foldable<F>, S: Semiring<A>): (fa: HKT<F, A>) => A
// tslint:disable-next-line: deprecation
export function sum<F, A>(F: Foldable<F>, S: Semiring<A>): (fa: HKT<F, A>) => A {
  return fa => F.reduce(fa, S.zero, (b, a) => S.add(b, a))
}

/**
 * Find the product of the numeric values in a data structure
 *
 * @since 1.0.0
 */
export function product<F extends URIS3, A>(F: Foldable3<F>, S: Semiring<A>): <U, L>(fa: Type3<F, U, L, A>) => A
export function product<F extends URIS3, A, U, L>(F: Foldable3C<F, U, L>, S: Semiring<A>): (fa: Type3<F, U, L, A>) => A
export function product<F extends URIS2, A>(F: Foldable2<F>, S: Semiring<A>): <L>(fa: Type2<F, L, A>) => A
export function product<F extends URIS2, A, L>(F: Foldable2C<F, L>, S: Semiring<A>): (fa: Type2<F, L, A>) => A
export function product<F extends URIS, A>(F: Foldable1<F>, S: Semiring<A>): (fa: Type<F, A>) => A
// tslint:disable-next-line: deprecation
export function product<F, A>(F: Foldable<F>, S: Semiring<A>): (fa: HKT<F, A>) => A
// tslint:disable-next-line: deprecation
export function product<F, A>(F: Foldable<F>, S: Semiring<A>): (fa: HKT<F, A>) => A {
  return fa => F.reduce(fa, S.one, (b, a) => S.mul(b, a))
}

/**
 * Test whether a value is an element of a data structure
 *
 * @since 1.0.0
 */
export function elem<F extends URIS3, A>(F: Foldable3<F>, S: Setoid<A>): <U, L>(a: A, fa: Type3<F, U, L, A>) => boolean
export function elem<F extends URIS3, A, U, L>(
  F: Foldable3C<F, U, L>,
  S: Setoid<A>
): (a: A, fa: Type3<F, U, L, A>) => boolean
export function elem<F extends URIS2, A>(F: Foldable2<F>, S: Setoid<A>): <L>(a: A, fa: Type2<F, L, A>) => boolean
export function elem<F extends URIS2, A, L>(F: Foldable2C<F, L>, S: Setoid<A>): (a: A, fa: Type2<F, L, A>) => boolean
export function elem<F extends URIS, A>(F: Foldable1<F>, S: Setoid<A>): (a: A, fa: Type<F, A>) => boolean
// tslint:disable-next-line: deprecation
export function elem<F, A>(F: Foldable<F>, S: Setoid<A>): (a: A, fa: HKT<F, A>) => boolean
// tslint:disable-next-line: deprecation
export function elem<F, A>(F: Foldable<F>, S: Setoid<A>): (a: A, fa: HKT<F, A>) => boolean {
  return (a, fa) => F.reduce<A, boolean>(fa, false, (b, x) => b || S.equals(x, a))
}

/**
 * Try to find an element in a data structure which satisfies a predicate
 *
 * @since 1.0.0
 */
export function find<F extends URIS3>(F: Foldable3<F>): <U, L, A>(fa: Type3<F, U, L, A>, p: Predicate<A>) => Option<A>
export function find<F extends URIS3, U, L>(
  F: Foldable3C<F, U, L>
): <A>(fa: Type3<F, U, L, A>, p: Predicate<A>) => Option<A>
export function find<F extends URIS2>(F: Foldable2<F>): <L, A>(fa: Type2<F, L, A>, p: Predicate<A>) => Option<A>
export function find<F extends URIS2, L>(F: Foldable2C<F, L>): <A>(fa: Type2<F, L, A>, p: Predicate<A>) => Option<A>
export function find<F extends URIS>(F: Foldable1<F>): <A>(fa: Type<F, A>, p: Predicate<A>) => Option<A>
// tslint:disable-next-line: deprecation
export function find<F>(F: Foldable<F>): <A>(fa: HKT<F, A>, p: Predicate<A>) => Option<A>
// tslint:disable-next-line: deprecation
export function find<F>(F: Foldable<F>): <A>(fa: HKT<F, A>, p: Predicate<A>) => Option<A> {
  return <A>(fa: HKT<F, A>, p: Predicate<A>) =>
    F.reduce<A, Option<A>>(fa, none, (b, a) => {
      if (b.isNone() && p(a)) {
        return some(a)
      } else {
        return b
      }
    })
}

/**
 * Find the smallest element of a structure, according to its `Ord` instance
 *
 * @since 1.0.0
 */
export function minimum<F extends URIS3, A>(F: Foldable3<F>, O: Ord<A>): <U, L>(fa: Type3<F, U, L, A>) => Option<A>
export function minimum<F extends URIS3, A, U, L>(
  F: Foldable3C<F, U, L>,
  O: Ord<A>
): (fa: Type3<F, U, L, A>) => Option<A>
export function minimum<F extends URIS2, A>(F: Foldable2<F>, O: Ord<A>): <L>(fa: Type2<F, L, A>) => Option<A>
export function minimum<F extends URIS2, A, L>(F: Foldable2C<F, L>, O: Ord<A>): (fa: Type2<F, L, A>) => Option<A>
export function minimum<F extends URIS, A>(F: Foldable1<F>, O: Ord<A>): (fa: Type<F, A>) => Option<A>
// tslint:disable-next-line: deprecation
export function minimum<F, A>(F: Foldable<F>, O: Ord<A>): (fa: HKT<F, A>) => Option<A>
// tslint:disable-next-line: deprecation
export function minimum<F, A>(F: Foldable<F>, O: Ord<A>): (fa: HKT<F, A>) => Option<A> {
  const minO = min(O)
  return fa => F.reduce(fa, none, (b: Option<A>, a) => (b.isNone() ? some(a) : some(minO(b.value, a))))
}

/**
 * Find the largest element of a structure, according to its `Ord` instance
 *
 * @since 1.0.0
 */
export function maximum<F extends URIS3, A>(F: Foldable3<F>, O: Ord<A>): <U, L>(fa: Type3<F, U, L, A>) => Option<A>
export function maximum<F extends URIS3, A, U, L>(
  F: Foldable3C<F, U, L>,
  O: Ord<A>
): (fa: Type3<F, U, L, A>) => Option<A>
export function maximum<F extends URIS2, A>(F: Foldable2<F>, O: Ord<A>): <L>(fa: Type2<F, L, A>) => Option<A>
export function maximum<F extends URIS2, A, L>(F: Foldable2C<F, L>, O: Ord<A>): (fa: Type2<F, L, A>) => Option<A>
export function maximum<F extends URIS, A>(F: Foldable1<F>, O: Ord<A>): (fa: Type<F, A>) => Option<A>
// tslint:disable-next-line: deprecation
export function maximum<F, A>(F: Foldable<F>, O: Ord<A>): (fa: HKT<F, A>) => Option<A>
// tslint:disable-next-line: deprecation
export function maximum<F, A>(F: Foldable<F>, O: Ord<A>): (fa: HKT<F, A>) => Option<A> {
  const maxO = max(O)
  return fa => F.reduce(fa, none, (b: Option<A>, a) => (b.isNone() ? some(a) : some(maxO(b.value, a))))
}

/**
 * @since 1.0.0
 */
export function toArray<F extends URIS3>(F: Foldable3<F>): <U, L, A>(fa: Type3<F, U, L, A>) => Array<A>
export function toArray<F extends URIS3, U, L>(F: Foldable3C<F, U, L>): <A>(fa: Type3<F, U, L, A>) => Array<A>
export function toArray<F extends URIS2>(F: Foldable2<F>): <L, A>(fa: Type2<F, L, A>) => Array<A>
export function toArray<F extends URIS2, L>(F: Foldable2C<F, L>): <A>(fa: Type2<F, L, A>) => Array<A>
export function toArray<F extends URIS>(F: Foldable1<F>): <A>(fa: Type<F, A>) => Array<A>
// tslint:disable-next-line: deprecation
export function toArray<F>(F: Foldable<F>): <A>(fa: HKT<F, A>) => Array<A>
// tslint:disable-next-line: deprecation
export function toArray<F>(F: Foldable<F>): <A>(fa: HKT<F, A>) => Array<A> {
  const foldMapF = foldMap(F, unsafeMonoidArray)
  return fa => foldMapF(fa, a => [a])
}

/**
 * Traverse a data structure, performing some effects encoded by an `Applicative` functor at each value, ignoring the
 * final result.
 *
 * @since 1.7.0
 */
export function traverse<M extends URIS3, F extends URIS>(
  M: Applicative3<M>,
  F: Foldable1<F>
): <U, L, A, B>(fa: Type<F, A>, f: (a: A) => Type3<M, U, L, B>) => Type3<M, U, L, void>
export function traverse<M extends URIS3, F extends URIS, U, L>(
  M: Applicative3C<M, U, L>,
  F: Foldable1<F>
): <A, B>(fa: Type<F, A>, f: (a: A) => Type3<M, U, L, B>) => Type3<M, U, L, void>
export function traverse<M extends URIS2, F extends URIS>(
  M: Applicative2<M>,
  F: Foldable1<F>
): <L, A, B>(fa: Type<F, A>, f: (a: A) => Type2<M, L, B>) => Type2<M, L, void>
export function traverse<M extends URIS2, F extends URIS, L>(
  M: Applicative2C<M, L>,
  F: Foldable1<F>
): <A, B>(fa: Type<F, A>, f: (a: A) => Type2<M, L, B>) => Type2<M, L, void>
export function traverse<M extends URIS, F extends URIS>(
  M: Applicative1<M>,
  F: Foldable1<F>
): <A, B>(fa: Type<F, A>, f: (a: A) => Type<M, B>) => Type<M, void>
export function traverse<M, F>(
  M: Applicative<M>,
  // tslint:disable-next-line: deprecation
  F: Foldable<F>
): <A, B>(fa: HKT<F, A>, f: (a: A) => HKT<M, B>) => HKT<M, void>
export function traverse<M, F>(
  M: Applicative<M>,
  // tslint:disable-next-line: deprecation
  F: Foldable<F>
): <A, B>(fa: HKT<F, A>, f: (a: A) => HKT<M, B>) => HKT<M, void> {
  const traverseMF = traverse_(M, F)
  return (fa, f) => traverseMF(f, fa)
}

import { Applicative, Applicative1, Applicative2, Applicative2C, Applicative3, Applicative3C }  from  './Applicative.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monad, Monad1, Monad2, Monad2C, Monad3, Monad3C }  from  './Monad.ts'
import { Monoid, unsafeMonoidArray }  from  './Monoid.ts'
import { Option, none, some }  from  './Option.ts'
import { Ord, max as maxOrd, min as minOrd }  from  './Ord.ts'
import { Plus, Plus1, Plus2, Plus2C, Plus3, Plus3C }  from  './Plus.ts'
import { Semiring }  from  './Semiring.ts'
import { Setoid }  from  './Setoid.ts'
import { Predicate, identity }  from  './function.ts'
import {
  Foldable,
  Foldable1,
  Foldable2,
  Foldable3,
  Foldable2C,
  Foldable3C,
  FoldableComposition,
  FoldableComposition11,
  FoldableComposition12,
  FoldableComposition21,
  FoldableComposition22,
  foldMap,
  FoldableComposition12C,
  FoldableComposition2C1,
  FoldableComposition22C,
  FoldableComposition3C1
} from './Foldable.ts'
import { applyFirst }  from  './Apply.ts'

/**
 * @since 1.10.0
 */
// tslint:disable-next-line: deprecation
export interface Foldable2v<F> extends Foldable<F> {
  readonly foldMap: <M>(M: Monoid<M>) => <A>(fa: HKT<F, A>, f: (a: A) => M) => M
  readonly foldr: <A, B>(fa: HKT<F, A>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2v1<F extends URIS> extends Foldable1<F> {
  readonly foldMap: <M>(M: Monoid<M>) => <A>(fa: Type<F, A>, f: (a: A) => M) => M
  readonly foldr: <A, B>(fa: Type<F, A>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2v2<F extends URIS2> extends Foldable2<F> {
  readonly foldMap: <M>(M: Monoid<M>) => <L, A>(fa: Type2<F, L, A>, f: (a: A) => M) => M
  readonly foldr: <L, A, B>(fa: Type2<F, L, A>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2v3<F extends URIS3> extends Foldable3<F> {
  readonly foldMap: <M>(M: Monoid<M>) => <U, L, A>(fa: Type3<F, U, L, A>, f: (a: A) => M) => M
  readonly foldr: <U, L, A, B>(fa: Type3<F, U, L, A>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2v2C<F extends URIS2, L> extends Foldable2C<F, L> {
  readonly foldMap: <M>(M: Monoid<M>) => <A>(fa: Type2<F, L, A>, f: (a: A) => M) => M
  readonly foldr: <A, B>(fa: Type2<F, L, A>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2v3C<F extends URIS3, U, L> extends Foldable3C<F, U, L> {
  readonly foldMap: <M>(M: Monoid<M>) => <A>(fa: Type3<F, U, L, A>, f: (a: A) => M) => M
  readonly foldr: <A, B>(fa: Type3<F, U, L, A>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2vComposition<F, G> extends FoldableComposition<F, G> {
  readonly foldMap: <M>(M: Monoid<M>) => <A>(fa: HKT<F, HKT<G, A>>, f: (a: A) => M) => M
  readonly foldr: <A, B>(fa: HKT<F, HKT<G, A>>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2vComposition11<F extends URIS, G extends URIS> extends FoldableComposition11<F, G> {
  readonly foldMap: <M>(M: Monoid<M>) => <A>(fa: Type<F, Type<G, A>>, f: (a: A) => M) => M
  readonly foldr: <A, B>(fa: Type<F, Type<G, A>>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2vComposition12<F extends URIS, G extends URIS2> extends FoldableComposition12<F, G> {
  readonly foldMap: <M>(M: Monoid<M>) => <L, A>(fa: Type<F, Type2<G, L, A>>, f: (a: A) => M) => M
  readonly foldr: <LG, A, B>(fa: Type<F, Type2<G, LG, A>>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2vComposition12C<F extends URIS, G extends URIS2, LG>
  extends FoldableComposition12C<F, G, LG> {
  readonly foldMap: <M>(M: Monoid<M>) => <A>(fa: Type<F, Type2<G, LG, A>>, f: (a: A) => M) => M
  readonly foldr: <A, B>(fa: Type<F, Type2<G, LG, A>>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2vComposition21<F extends URIS2, G extends URIS> extends FoldableComposition21<F, G> {
  readonly foldMap: <M>(M: Monoid<M>) => <L, A>(fa: Type2<F, L, Type<G, A>>, f: (a: A) => M) => M
  readonly foldr: <LF, A, B>(fa: Type2<F, LF, Type<G, A>>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2vComposition2C1<F extends URIS2, G extends URIS, LF>
  extends FoldableComposition2C1<F, G, LF> {
  readonly foldMap: <M>(M: Monoid<M>) => <A>(fa: Type2<F, LF, Type<G, A>>, f: (a: A) => M) => M
  readonly foldr: <A, B>(fa: Type2<F, LF, Type<G, A>>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2vComposition22<F extends URIS2, G extends URIS2> extends FoldableComposition22<F, G> {
  readonly foldMap: <M>(M: Monoid<M>) => <LF, LG, A>(fa: Type2<F, LF, Type2<G, LG, A>>, f: (a: A) => M) => M
  readonly foldr: <LF, LG, A, B>(fa: Type2<F, LF, Type2<G, LG, A>>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2vComposition22C<F extends URIS2, G extends URIS2, LG>
  extends FoldableComposition22C<F, G, LG> {
  readonly foldMap: <M>(M: Monoid<M>) => <LF, A>(fa: Type2<F, LF, Type2<G, LG, A>>, f: (a: A) => M) => M
  readonly foldr: <LF, A, B>(fa: Type2<F, LF, Type2<G, LG, A>>, b: B, f: (a: A, b: B) => B) => B
}

export interface Foldable2vComposition3C1<F extends URIS3, G extends URIS, UF, LF>
  extends FoldableComposition3C1<F, G, UF, LF> {
  readonly foldMap: <M>(M: Monoid<M>) => <A>(fa: Type3<F, UF, LF, Type<G, A>>, f: (a: A) => M) => M
  readonly foldr: <LF, A, B>(fa: Type3<F, UF, LF, Type<G, A>>, b: B, f: (a: A, b: B) => B) => B
}

/**
 * Returns the composition of two foldables
 *
 * @example
 * import { getFoldableComposition }  from  'fp-ts/lib/Foldable2v.ts'
 * import { array }  from  'fp-ts/lib/Array.ts'
 * import { option, some, none }  from  'fp-ts/lib/Option.ts'
 * import { monoidString }  from  'fp-ts/lib/Monoid.ts'
 *
 * const F = getFoldableComposition(array, option)
 * assert.strictEqual(F.reduce([some('a'), some('b'), some('c')], '', monoidString.concat), 'abc')
 * assert.strictEqual(F.reduce([some('a'), none, some('c')], '', monoidString.concat), 'ac')
 *
 * @since 1.10.0
 */
export function getFoldableComposition<F extends URIS3, G extends URIS, UF, LF>(
  F: Foldable2v3C<F, UF, LF>,
  G: Foldable2v1<G>
): Foldable2vComposition3C1<F, G, UF, LF>
export function getFoldableComposition<F extends URIS2, G extends URIS2, LG>(
  F: Foldable2v2<F>,
  G: Foldable2v2C<G, LG>
): Foldable2vComposition22C<F, G, LG>
export function getFoldableComposition<F extends URIS2, G extends URIS2>(
  F: Foldable2v2<F>,
  G: Foldable2v2<G>
): Foldable2vComposition22<F, G>
export function getFoldableComposition<F extends URIS2, G extends URIS, LF>(
  F: Foldable2v2C<F, LF>,
  G: Foldable2v1<G>
): Foldable2vComposition2C1<F, G, LF>
export function getFoldableComposition<F extends URIS2, G extends URIS>(
  F: Foldable2v2<F>,
  G: Foldable2v1<G>
): Foldable2vComposition21<F, G>
export function getFoldableComposition<F extends URIS, G extends URIS2, LG>(
  F: Foldable2v1<F>,
  G: Foldable2v2C<G, LG>
): Foldable2vComposition12C<F, G, LG>
export function getFoldableComposition<F extends URIS, G extends URIS2>(
  F: Foldable2v1<F>,
  G: Foldable2v2<G>
): Foldable2vComposition12<F, G>
export function getFoldableComposition<F extends URIS, G extends URIS>(
  F: Foldable2v1<F>,
  G: Foldable2v1<G>
): Foldable2vComposition11<F, G>
export function getFoldableComposition<F, G>(F: Foldable2v<F>, G: Foldable2v<G>): Foldable2vComposition<F, G>
export function getFoldableComposition<F, G>(F: Foldable2v<F>, G: Foldable2v<G>): Foldable2vComposition<F, G> {
  return {
    reduce: (fga, b, f) => F.reduce(fga, b, (b, ga) => G.reduce(ga, b, f)),
    foldMap: M => {
      const foldMapF = F.foldMap(M)
      const foldMapG = G.foldMap(M)
      return (fa, f) => foldMapF(fa, ga => foldMapG(ga, f))
    },
    foldr: (fa, b, f) => F.foldr(fa, b, (ga, b) => G.foldr(ga, b, f))
  }
}

/**
 * A generalization of monoidal `fold`
 *
 * @example
 * import { fold }  from  'fp-ts/lib/Foldable2v.ts'
 * import { Tree, tree }  from  'fp-ts/lib/Tree.ts'
 * import { monoidSum }  from  'fp-ts/lib/Monoid.ts'
 *
 * const t = new Tree(1, [new Tree(2, []), new Tree(3, []), new Tree(4, [])])
 * assert.strictEqual(fold(monoidSum, tree)(t), 10)
 *
 * @since 1.10.0
 */
export function fold<M, F extends URIS3>(M: Monoid<M>, F: Foldable2v3<F>): <U, L>(fa: Type3<F, U, L, M>) => M
export function fold<M, F extends URIS3, U, L>(M: Monoid<M>, F: Foldable2v3C<F, U, L>): (fa: Type3<F, U, L, M>) => M
export function fold<M, F extends URIS2>(M: Monoid<M>, F: Foldable2v2<F>): <L>(fa: Type2<F, L, M>) => M
export function fold<M, F extends URIS2, L>(M: Monoid<M>, F: Foldable2v2C<F, L>): (fa: Type2<F, L, M>) => M
export function fold<M, F extends URIS>(M: Monoid<M>, F: Foldable2v1<F>): (fa: Type<F, M>) => M
export function fold<M, F>(M: Monoid<M>, F: Foldable2v<F>): (fa: HKT<F, M>) => M
export function fold<M, F>(M: Monoid<M>, F: Foldable2v<F>): (fa: HKT<F, M>) => M {
  return fa => F.reduce(fa, M.empty, M.concat)
}

/**
 * Similar to 'reduce', but the result is encapsulated in a monad.
 *
 * Note: this function is not generally stack-safe, e.g., for monads which build up thunks a la `IO`.
 *
 * @example
 * import { foldM }  from  'fp-ts/lib/Foldable2v.ts'
 * import { option, some }  from  'fp-ts/lib/Option.ts'
 * import { Tree, tree }  from  'fp-ts/lib/Tree.ts'
 *
 * const t = new Tree(1, [new Tree(2, []), new Tree(3, []), new Tree(4, [])])
 * assert.deepStrictEqual(foldM(option, tree)(t, 0, (b, a) => (a > 2 ? some(b + a) : some(b))), some(7))
 *
 * @since 1.10.0
 */
export function foldM<M extends URIS3, F extends URIS>(
  M: Monad3<M>,
  F: Foldable2v1<F>
): <U, L, A, B>(fa: Type<F, A>, b: B, f: (b: B, a: A) => Type3<M, U, L, B>) => Type3<M, U, L, B>
export function foldM<M extends URIS3, F extends URIS, U, L>(
  M: Monad3C<M, U, L>,
  F: Foldable2v1<F>
): <A, B>(fa: Type<F, A>, b: B, f: (b: B, a: A) => Type3<M, U, L, B>) => Type3<M, U, L, B>
export function foldM<M extends URIS2, F extends URIS>(
  M: Monad2<M>,
  F: Foldable2v1<F>
): <L, A, B>(fa: Type<F, A>, b: B, f: (b: B, a: A) => Type2<M, L, B>) => Type2<M, L, B>
export function foldM<M extends URIS2, F extends URIS, L>(
  M: Monad2C<M, L>,
  F: Foldable2v1<F>
): <A, B>(fa: Type<F, A>, b: B, f: (b: B, a: A) => Type2<M, L, B>) => Type2<M, L, B>
export function foldM<M extends URIS, F extends URIS>(
  M: Monad1<M>,
  F: Foldable2v1<F>
): <A, B>(fa: Type<F, A>, b: B, f: (b: B, a: A) => Type<M, B>) => Type<M, B>
export function foldM<M, F>(
  M: Monad<M>,
  F: Foldable2v<F>
): <A, B>(fa: HKT<F, A>, b: B, f: (b: B, a: A) => HKT<M, B>) => HKT<M, B>
export function foldM<M, F>(
  M: Monad<M>,
  F: Foldable2v<F>
): <A, B>(fa: HKT<F, A>, b: B, f: (b: B, a: A) => HKT<M, B>) => HKT<M, B> {
  return (fa, b, f) => F.reduce(fa, M.of(b), (mb, a) => M.chain(mb, b => f(b, a)))
}

/**
 * Perform all of the effects in some data structure in the order given by the `Foldable2v` instance, ignoring the final result.
 *
 * @example
 * import { array }  from  'fp-ts/lib/Array.ts'
 * import { sequence_ }  from  'fp-ts/lib/Foldable2v.ts'
 * import { io, IO }  from  'fp-ts/lib/IO.ts'
 *
 * let log = ''
 * const append = (s: string) => new IO(() => (log += s))
 * sequence_(io, array)([append('a'), append('b'), append('c')]).run()
 * assert.strictEqual(log, 'abc')
 *
 * @since 1.10.0
 */
export function sequence_<M extends URIS3, F extends URIS>(
  M: Applicative3<M>,
  F: Foldable2v1<F>
): <U, L, A>(fa: Type<F, Type3<M, U, L, A>>) => Type3<M, U, L, void>
export function sequence_<M extends URIS3, F extends URIS, U, L>(
  M: Applicative3C<M, U, L>,
  F: Foldable2v1<F>
): <A>(fa: Type<F, Type3<M, U, L, A>>) => Type3<M, U, L, void>
export function sequence_<M extends URIS2, F extends URIS>(
  M: Applicative2<M>,
  F: Foldable2v1<F>
): <L, A>(fa: Type<F, Type2<M, L, A>>) => Type2<M, L, void>
export function sequence_<M extends URIS2, F extends URIS, L>(
  M: Applicative2C<M, L>,
  F: Foldable2v1<F>
): <A>(fa: Type<F, Type2<M, L, A>>) => Type2<M, L, void>
export function sequence_<M extends URIS, F extends URIS>(
  M: Applicative1<M>,
  F: Foldable2v1<F>
): <A>(fa: Type<F, Type<M, A>>) => Type<M, void>
export function sequence_<M, F>(M: Applicative<M>, F: Foldable2v<F>): <A>(fa: HKT<F, HKT<M, A>>) => HKT<M, void>
export function sequence_<M, F>(M: Applicative<M>, F: Foldable2v<F>): <A>(fa: HKT<F, HKT<M, A>>) => HKT<M, void> {
  const traverseMF = traverse_(M, F)
  return fa => traverseMF(fa, identity)
}

/**
 * Combines a collection of elements using the `Alt` operation
 *
 * @example
 * import { array }  from  'fp-ts/lib/Array.ts'
 * import { oneOf }  from  'fp-ts/lib/Foldable2v.ts'
 * import { option, some }  from  'fp-ts/lib/Option.ts'
 *
 * assert.deepStrictEqual(oneOf(option, array)([some(2), some(1)]), some(2))
 *
 * @since 1.10.0
 */
export function oneOf<P extends URIS3, F extends URIS>(
  P: Plus3<P>,
  F: Foldable2v1<F>
): <U, L, A>(fga: Type<F, Type3<P, U, L, A>>) => Type3<P, U, L, A>
export function oneOf<P extends URIS3, U, L, F extends URIS>(
  P: Plus3C<P, U, L>,
  F: Foldable2v1<F>
): <A>(fga: Type<F, Type3<P, U, L, A>>) => Type3<P, U, L, A>
export function oneOf<P extends URIS2, F extends URIS>(
  P: Plus2<P>,
  F: Foldable2v1<F>
): <L, A>(fga: Type<F, Type2<P, L, A>>) => Type2<P, L, A>
export function oneOf<P extends URIS2, F extends URIS, L>(
  P: Plus2C<P, L>,
  F: Foldable2v1<F>
): <A>(fga: Type<F, Type2<P, L, A>>) => Type2<P, L, A>
export function oneOf<P extends URIS, F extends URIS>(
  P: Plus1<P>,
  F: Foldable2v1<F>
): <A>(fga: Type<F, Type<P, A>>) => Type<P, A>
export function oneOf<P, F>(P: Plus<P>, F: Foldable2v<F>): <A>(fga: HKT<F, HKT<P, A>>) => HKT<P, A>
export function oneOf<P, F>(P: Plus<P>, F: Foldable2v<F>): <A>(fga: HKT<F, HKT<P, A>>) => HKT<P, A> {
  return fga => F.reduce(fga, P.zero(), P.alt)
}

interface Acc<M> {
  init: boolean
  acc: M
}

/**
 * Fold a data structure, accumulating values in some `Monoid`, combining adjacent elements using the specified separator
 *
 * @example
 * import { intercalate }  from  'fp-ts/lib/Foldable2v.ts'
 * import { monoidString }  from  'fp-ts/lib/Monoid.ts'
 * import { Tree, tree }  from  'fp-ts/lib/Tree.ts'
 *
 * const t = new Tree('a', [new Tree('b', []), new Tree('c', []), new Tree('d', [])])
 * assert.strictEqual(intercalate(monoidString, tree)('|', t), 'a|b|c|d')
 *
 * @since 1.10.0
 */
export function intercalate<M, F extends URIS3>(
  M: Monoid<M>,
  F: Foldable2v3<F>
): <U, L>(sep: M, fm: Type3<F, U, L, M>) => M
export function intercalate<M, F extends URIS3, U, L>(
  M: Monoid<M>,
  F: Foldable2v3C<F, U, L>
): (sep: M, fm: Type3<F, U, L, M>) => M
export function intercalate<M, F extends URIS2>(M: Monoid<M>, F: Foldable2v2<F>): <L>(sep: M, fm: Type2<F, L, M>) => M
export function intercalate<M, F extends URIS2, L>(
  M: Monoid<M>,
  F: Foldable2v2C<F, L>
): (sep: M, fm: Type2<F, L, M>) => M
export function intercalate<M, F extends URIS>(M: Monoid<M>, F: Foldable2v1<F>): (sep: M, fm: Type<F, M>) => M
export function intercalate<M, F>(M: Monoid<M>, F: Foldable2v<F>): (sep: M, fm: HKT<F, M>) => M
export function intercalate<M, F>(M: Monoid<M>, F: Foldable2v<F>): (sep: M, fm: HKT<F, M>) => M {
  return (sep, fm) => {
    const go = ({ init, acc }: Acc<M>, x: M): Acc<M> =>
      init ? { init: false, acc: x } : { init: false, acc: M.concat(M.concat(acc, sep), x) }
    return F.reduce(fm, { init: true, acc: M.empty }, go).acc
  }
}

/**
 * Find the sum of the numeric values in a data structure
 *
 * @example
 * import { fieldNumber }  from  'fp-ts/lib/Field.ts'
 * import { sum }  from  'fp-ts/lib/Foldable2v.ts'
 * import { Tree, tree }  from  'fp-ts/lib/Tree.ts'
 *
 * const t = new Tree(1, [new Tree(2, []), new Tree(3, []), new Tree(4, [])])
 * assert.strictEqual(sum(fieldNumber, tree)(t), 10)
 *
 * @since 1.10.0
 */
export function sum<F extends URIS3, A>(S: Semiring<A>, F: Foldable2v3<F>): <U, L>(fa: Type3<F, U, L, A>) => A
export function sum<F extends URIS3, A, U, L>(S: Semiring<A>, F: Foldable2v3C<F, U, L>): (fa: Type3<F, U, L, A>) => A
export function sum<F extends URIS2, A>(S: Semiring<A>, F: Foldable2v2<F>): <L>(fa: Type2<F, L, A>) => A
export function sum<F extends URIS2, A, L>(S: Semiring<A>, F: Foldable2v2C<F, L>): (fa: Type2<F, L, A>) => A
export function sum<F extends URIS, A>(S: Semiring<A>, F: Foldable2v1<F>): (fa: Type<F, A>) => A
export function sum<F, A>(S: Semiring<A>, F: Foldable2v<F>): (fa: HKT<F, A>) => A
export function sum<F, A>(S: Semiring<A>, F: Foldable2v<F>): (fa: HKT<F, A>) => A {
  return fa => F.reduce(fa, S.zero, S.add)
}

/**
 * Find the product of the numeric values in a data structure
 *
 * @example
 * import { fieldNumber }  from  'fp-ts/lib/Field.ts'
 * import { product }  from  'fp-ts/lib/Foldable2v.ts'
 * import { Tree, tree }  from  'fp-ts/lib/Tree.ts'
 *
 * const t = new Tree(1, [new Tree(2, []), new Tree(3, []), new Tree(4, [])])
 * assert.strictEqual(product(fieldNumber, tree)(t), 24)
 *
 * @since 1.10.0
 */
export function product<F extends URIS3, A>(S: Semiring<A>, F: Foldable2v3<F>): <U, L>(fa: Type3<F, U, L, A>) => A
export function product<F extends URIS3, A, U, L>(
  S: Semiring<A>,
  F: Foldable2v3C<F, U, L>
): (fa: Type3<F, U, L, A>) => A
export function product<F extends URIS2, A>(S: Semiring<A>, F: Foldable2v2<F>): <L>(fa: Type2<F, L, A>) => A
export function product<F extends URIS2, A, L>(S: Semiring<A>, F: Foldable2v2C<F, L>): (fa: Type2<F, L, A>) => A
export function product<F extends URIS, A>(S: Semiring<A>, F: Foldable2v1<F>): (fa: Type<F, A>) => A
export function product<F, A>(S: Semiring<A>, F: Foldable2v<F>): (fa: HKT<F, A>) => A
export function product<F, A>(S: Semiring<A>, F: Foldable2v<F>): (fa: HKT<F, A>) => A {
  return fa => F.reduce(fa, S.one, S.mul)
}

/**
 * Test whether a value is an element of a data structure
 *
 * @example
 * import { elem }  from  'fp-ts/lib/Foldable2v.ts'
 * import { setoidNumber }  from  'fp-ts/lib/Setoid.ts'
 * import { Tree, tree }  from  'fp-ts/lib/Tree.ts'
 *
 * const t = new Tree(1, [new Tree(2, []), new Tree(3, []), new Tree(4, [])])
 * assert.strictEqual(elem(setoidNumber, tree)(2, t), true)
 * assert.strictEqual(elem(setoidNumber, tree)(5, t), false)
 *
 * @since 1.14.0
 */
export function elem<F extends URIS3, A>(
  S: Setoid<A>,
  F: Foldable2v3<F>
): <U, L>(a: A, fa: Type3<F, U, L, A>) => boolean
export function elem<F extends URIS3, A, U, L>(
  S: Setoid<A>,
  F: Foldable2v3C<F, U, L>
): (a: A, fa: Type3<F, U, L, A>) => boolean
export function elem<F extends URIS2, A>(S: Setoid<A>, F: Foldable2v2<F>): <L>(a: A, fa: Type2<F, L, A>) => boolean
export function elem<F extends URIS2, A, L>(S: Setoid<A>, F: Foldable2v2C<F, L>): (a: A, fa: Type2<F, L, A>) => boolean
export function elem<F extends URIS, A>(S: Setoid<A>, F: Foldable2v1<F>): (a: A, fa: Type<F, A>) => boolean
export function elem<F, A>(S: Setoid<A>, F: Foldable2v<F>): (a: A, fa: HKT<F, A>) => boolean
export function elem<F, A>(S: Setoid<A>, F: Foldable2v<F>): (a: A, fa: HKT<F, A>) => boolean {
  return (a, fa) => F.reduce<A, boolean>(fa, false, (b, x) => b || S.equals(x, a))
}

/**
 * Find the first element which satisfies a predicate function
 *
 *
 * @example
 * import { findFirst }  from  'fp-ts/lib/Foldable2v.ts'
 * import { Tree, tree }  from  'fp-ts/lib/Tree.ts'
 * import { some }  from  'fp-ts/lib/Option.ts'
 *
 * const t = new Tree(1, [new Tree(2, []), new Tree(3, []), new Tree(4, [])])
 * assert.deepStrictEqual(findFirst(tree)(t, a => a > 2), some(3))
 *
 * @since 1.10.0
 */
export function findFirst<F extends URIS3>(
  F: Foldable2v3<F>
): <U, L, A>(fa: Type3<F, U, L, A>, p: Predicate<A>) => Option<A>
export function findFirst<F extends URIS3, U, L>(
  F: Foldable2v3C<F, U, L>
): <A>(fa: Type3<F, U, L, A>, p: Predicate<A>) => Option<A>
export function findFirst<F extends URIS2>(F: Foldable2v2<F>): <L, A>(fa: Type2<F, L, A>, p: Predicate<A>) => Option<A>
export function findFirst<F extends URIS2, L>(
  F: Foldable2v2C<F, L>
): <A>(fa: Type2<F, L, A>, p: Predicate<A>) => Option<A>
export function findFirst<F extends URIS>(F: Foldable2v1<F>): <A>(fa: Type<F, A>, p: Predicate<A>) => Option<A>
export function findFirst<F>(F: Foldable2v<F>): <A>(fa: HKT<F, A>, p: Predicate<A>) => Option<A>
export function findFirst<F>(F: Foldable2v<F>): <A>(fa: HKT<F, A>, p: Predicate<A>) => Option<A> {
  return <A>(fa: HKT<F, A>, p: Predicate<A>) =>
    F.reduce<A, Option<A>>(fa, none, (b, a) => {
      if (b.isNone() && p(a)) {
        return some(a)
      } else {
        return b
      }
    })
}

/**
 * Find the smallest element of a structure, according to its `Ord` instance
 *
 * @example
 * import { min }  from  'fp-ts/lib/Foldable2v.ts'
 * import { some }  from  'fp-ts/lib/Option.ts'
 * import { ordNumber }  from  'fp-ts/lib/Ord.ts'
 * import { Tree, tree }  from  'fp-ts/lib/Tree.ts'
 *
 * const t = new Tree(1, [new Tree(2, []), new Tree(3, []), new Tree(4, [])])
 * assert.deepStrictEqual(min(ordNumber, tree)(t), some(1))
 *
 * @since 1.10.0
 */
export function min<F extends URIS3, A>(O: Ord<A>, F: Foldable2v3<F>): <U, L>(fa: Type3<F, U, L, A>) => Option<A>
export function min<F extends URIS3, A, U, L>(O: Ord<A>, F: Foldable2v3C<F, U, L>): (fa: Type3<F, U, L, A>) => Option<A>
export function min<F extends URIS2, A>(O: Ord<A>, F: Foldable2v2<F>): <L>(fa: Type2<F, L, A>) => Option<A>
export function min<F extends URIS2, A, L>(O: Ord<A>, F: Foldable2v2C<F, L>): (fa: Type2<F, L, A>) => Option<A>
export function min<F extends URIS, A>(O: Ord<A>, F: Foldable2v1<F>): (fa: Type<F, A>) => Option<A>
export function min<F, A>(O: Ord<A>, F: Foldable2v<F>): (fa: HKT<F, A>) => Option<A>
export function min<F, A>(O: Ord<A>, F: Foldable2v<F>): (fa: HKT<F, A>) => Option<A> {
  const minO = minOrd(O)
  return fa => F.reduce(fa, none, (b: Option<A>, a) => (b.isNone() ? some(a) : some(minO(b.value, a))))
}

/**
 * Find the largest element of a structure, according to its `Ord` instance
 *
 * @example
 * import { max }  from  'fp-ts/lib/Foldable2v.ts'
 * import { some }  from  'fp-ts/lib/Option.ts'
 * import { ordNumber }  from  'fp-ts/lib/Ord.ts'
 * import { Tree, tree }  from  'fp-ts/lib/Tree.ts'
 *
 * const t = new Tree(1, [new Tree(2, []), new Tree(3, []), new Tree(4, [])])
 * assert.deepStrictEqual(max(ordNumber, tree)(t), some(4))
 *
 * @since 1.10.0
 */
export function max<F extends URIS3, A>(O: Ord<A>, F: Foldable2v3<F>): <U, L>(fa: Type3<F, U, L, A>) => Option<A>
export function max<F extends URIS3, A, U, L>(O: Ord<A>, F: Foldable2v3C<F, U, L>): (fa: Type3<F, U, L, A>) => Option<A>
export function max<F extends URIS2, A>(O: Ord<A>, F: Foldable2v2<F>): <L>(fa: Type2<F, L, A>) => Option<A>
export function max<F extends URIS2, A, L>(O: Ord<A>, F: Foldable2v2C<F, L>): (fa: Type2<F, L, A>) => Option<A>
export function max<F extends URIS, A>(O: Ord<A>, F: Foldable2v1<F>): (fa: Type<F, A>) => Option<A>
export function max<F, A>(O: Ord<A>, F: Foldable2v<F>): (fa: HKT<F, A>) => Option<A>
export function max<F, A>(O: Ord<A>, F: Foldable2v<F>): (fa: HKT<F, A>) => Option<A> {
  const maxO = maxOrd(O)
  return fa => F.reduce(fa, none, (b: Option<A>, a) => (b.isNone() ? some(a) : some(maxO(b.value, a))))
}

/**
 * Transforms a foldable into an array
 *
 * @example
 * import { toArray }  from  'fp-ts/lib/Foldable2v.ts'
 * import { Tree, tree }  from  'fp-ts/lib/Tree.ts'
 *
 * const t = new Tree(1, [new Tree(2, []), new Tree(3, []), new Tree(4, [])])
 * assert.deepStrictEqual(toArray(tree)(t), [1, 2, 3, 4])
 *
 * @since 1.10.0
 */
export function toArray<F extends URIS3>(F: Foldable2v3<F>): <U, L, A>(fa: Type3<F, U, L, A>) => Array<A>
export function toArray<F extends URIS3, U, L>(F: Foldable2v3C<F, U, L>): <A>(fa: Type3<F, U, L, A>) => Array<A>
export function toArray<F extends URIS2>(F: Foldable2v2<F>): <L, A>(fa: Type2<F, L, A>) => Array<A>
export function toArray<F extends URIS2, L>(F: Foldable2v2C<F, L>): <A>(fa: Type2<F, L, A>) => Array<A>
export function toArray<F extends URIS>(F: Foldable2v1<F>): <A>(fa: Type<F, A>) => Array<A>
export function toArray<F>(F: Foldable2v<F>): <A>(fa: HKT<F, A>) => Array<A>
export function toArray<F>(F: Foldable2v<F>): <A>(fa: HKT<F, A>) => Array<A> {
  const foldMapF = foldMap(F, unsafeMonoidArray)
  return fa => foldMapF(fa, a => [a])
}

/**
 * Traverse a data structure, performing some effects encoded by an `Applicative` functor at each value, ignoring the
 * final result.
 *
 * @example
 * import { array }  from  'fp-ts/lib/Array.ts'
 * import { traverse_ }  from  'fp-ts/lib/Foldable2v.ts'
 * import { io, IO }  from  'fp-ts/lib/IO.ts'
 *
 * let log = ''
 * const append = (s: string) => new IO(() => (log += s))
 * traverse_(io, array)(['a', 'b', 'c'], append).run()
 * assert.strictEqual(log, 'abc')
 *
 * @since 1.10.0
 */
export function traverse_<M extends URIS3, F extends URIS>(
  M: Applicative3<M>,
  F: Foldable2v1<F>
): <U, L, A, B>(fa: Type<F, A>, f: (a: A) => Type3<M, U, L, B>) => Type3<M, U, L, void>
export function traverse_<M extends URIS3, F extends URIS, U, L>(
  M: Applicative3C<M, U, L>,
  F: Foldable2v1<F>
): <A, B>(fa: Type<F, A>, f: (a: A) => Type3<M, U, L, B>) => Type3<M, U, L, void>
export function traverse_<M extends URIS2, F extends URIS>(
  M: Applicative2<M>,
  F: Foldable2v1<F>
): <L, A, B>(fa: Type<F, A>, f: (a: A) => Type2<M, L, B>) => Type2<M, L, void>
export function traverse_<M extends URIS2, F extends URIS, L>(
  M: Applicative2C<M, L>,
  F: Foldable2v1<F>
): <A, B>(fa: Type<F, A>, f: (a: A) => Type2<M, L, B>) => Type2<M, L, void>
export function traverse_<M extends URIS, F extends URIS>(
  M: Applicative1<M>,
  F: Foldable2v1<F>
): <A, B>(fa: Type<F, A>, f: (a: A) => Type<M, B>) => Type<M, void>
export function traverse_<M, F>(
  M: Applicative<M>,
  F: Foldable2v<F>
): <A, B>(fa: HKT<F, A>, f: (a: A) => HKT<M, B>) => HKT<M, void>
export function traverse_<M, F>(
  M: Applicative<M>,
  F: Foldable2v<F>
): <A, B>(fa: HKT<F, A>, f: (a: A) => HKT<M, B>) => HKT<M, void> {
  const toArrayF = toArray(F)
  const applyFirstM = applyFirst(M)
  const initialValue = M.of(undefined)
  return (fa, f) => toArrayF(fa).reduce((mu, a) => applyFirstM(mu, f(a)), initialValue)
}

/**
 * Use `elem` instead
 * @since 1.10.0
 * @deprecated
 */
export function member<F extends URIS3, A>(
  S: Setoid<A>,
  F: Foldable2v3<F>
): <U, L>(a: A, fa: Type3<F, U, L, A>) => boolean
/** @deprecated */
export function member<F extends URIS3, A, U, L>(
  S: Setoid<A>,
  F: Foldable2v3C<F, U, L>
): (a: A, fa: Type3<F, U, L, A>) => boolean
/** @deprecated */
export function member<F extends URIS2, A>(S: Setoid<A>, F: Foldable2v2<F>): <L>(a: A, fa: Type2<F, L, A>) => boolean
/** @deprecated */
export function member<F extends URIS2, A, L>(
  S: Setoid<A>,
  F: Foldable2v2C<F, L>
): (a: A, fa: Type2<F, L, A>) => boolean
/** @deprecated */
export function member<F extends URIS, A>(S: Setoid<A>, F: Foldable2v1<F>): (a: A, fa: Type<F, A>) => boolean
/** @deprecated */
export function member<F, A>(S: Setoid<A>, F: Foldable2v<F>): (a: A, fa: HKT<F, A>) => boolean
export function member<F, A>(S: Setoid<A>, F: Foldable2v<F>): (a: A, fa: HKT<F, A>) => boolean {
  return elem(S, F)
}

import { Applicative }  from  './Applicative.ts'
import { Compactable2, Separated }  from  './Compactable.ts'
import { Either }  from  './Either.ts'
import { FilterableWithIndex2C }  from  './FilterableWithIndex.ts'
import { Foldable2v2C, Foldable2v3, Foldable2v2, Foldable2v1, Foldable2v }  from  './Foldable2v.ts'
import { FoldableWithIndex2C }  from  './FoldableWithIndex.ts'
import { Predicate, phantom }  from  './function.ts'
import { HKT, Type, Type2, Type3, URIS, URIS2, URIS3 }  from  './HKT.ts'
import { Monoid }  from  './Monoid.ts'
import { Option, none, some }  from  './Option.ts'
import { Ord }  from  './Ord.ts'
import { Setoid, fromEquals }  from  './Setoid.ts'
import { TraversableWithIndex2C }  from  './TraversableWithIndex.ts'
import { Unfoldable, Unfoldable1 }  from  './Unfoldable.ts'
import { Semigroup }  from  './Semigroup.ts'
import { Witherable2C }  from  './Witherable.ts'
import { FunctorWithIndex2C }  from  './FunctorWithIndex.ts'
import { Functor2 }  from  './Functor.ts'
import { Traversable2v2C }  from  './Traversable2v.ts'
import { Filterable2 }  from  './Filterable.ts'
import { Show }  from  './Show.ts'

declare module './HKT.ts'
  interface URI2HKT2<L, A> {
    Map: Map<L, A>
  }
}

export const URI = 'Map'

export type URI = typeof URI

/**
 * @since 1.17.0
 */
export const getShow = <K, A>(SK: Show<K>, SA: Show<A>): Show<Map<K, A>> => {
  return {
    show: m => {
      let elements = ''
      m.forEach((a, k) => {
        elements += `[${SK.show(k)}, ${SA.show(a)}], `
      })
      if (elements !== '') {
        elements = elements.substring(0, elements.length - 2)
      }
      return `new Map([${elements}])`
    }
  }
}

/**
 * Calculate the number of key/value pairs in a map
 *
 * @since 1.14.0
 */
export const size = <K, A>(d: Map<K, A>): number => d.size

/**
 * Test whether or not a map is empty
 *
 * @since 1.14.0
 */
export const isEmpty = <K, A>(d: Map<K, A>): boolean => d.size === 0

/**
 * Test whether or not a key exists in a map
 *
 * @since 1.14.0
 */
export const member = <K>(S: Setoid<K>): (<A>(k: K, m: Map<K, A>) => boolean) => {
  const lookupS = lookup(S)
  return (k, m) => lookupS(k, m).isSome()
}

/**
 * Test whether or not a value is a member of a map
 *
 * @since 1.14.0
 */
export const elem = <A>(S: Setoid<A>) => <K>(a: A, m: Map<K, A>): boolean => {
  const values = m.values()
  let e: IteratorResult<A>
  while (!(e = values.next()).done) {
    const v = e.value
    if (S.equals(a, v)) {
      return true
    }
  }
  return false
}

/**
 * Get a sorted array of the keys contained in a map
 *
 * @since 1.14.0
 */
export const keys = <K>(O: Ord<K>): (<A>(m: Map<K, A>) => Array<K>) => m => Array.from(m.keys()).sort(O.compare)

/**
 * Get a sorted array of the values contained in a map
 *
 * @since 1.14.0
 */
export const values = <A>(O: Ord<A>): (<K>(m: Map<K, A>) => Array<A>) => m => Array.from(m.values()).sort(O.compare)

/**
 * @since 1.14.0
 */
export const collect = <K>(O: Ord<K>): (<A, B>(m: Map<K, A>, f: (k: K, a: A) => B) => Array<B>) => {
  const keysO = keys(O)
  return <A, B>(m: Map<K, A>, f: (k: K, a: A) => B): Array<B> => {
    const out: Array<B> = []
    const ks = keysO(m)
    for (let key of ks) {
      out.push(f(key, m.get(key)!))
    }
    return out
  }
}

/**
 * Get a sorted of the key/value pairs contained in a map
 *
 * @since 1.14.0
 */
export const toArray = <K>(O: Ord<K>): (<A>(m: Map<K, A>) => Array<[K, A]>) => {
  const collectO = collect(O)
  return m => collectO(m, (k, a) => [k, a])
}

/**
 * Unfolds a map into a list of key/value pairs
 *
 * @since 1.14.0
 */
export function toUnfoldable<K, F extends URIS>(
  O: Ord<K>,
  unfoldable: Unfoldable1<F>
): <A>(d: Map<K, A>) => Type<F, [K, A]>
export function toUnfoldable<K, F>(O: Ord<K>, unfoldable: Unfoldable<F>): <A>(d: Map<K, A>) => HKT<F, [K, A]>
export function toUnfoldable<K, F>(O: Ord<K>, unfoldable: Unfoldable<F>): <A>(d: Map<K, A>) => HKT<F, [K, A]> {
  const toArrayO = toArray(O)
  return d => {
    const arr = toArrayO(d)
    const len = arr.length
    return unfoldable.unfoldr(0, b => (b < len ? some([arr[b], b + 1]) : none))
  }
}

/**
 * Insert or replace a key/value pair in a map
 *
 * @since 1.14.0
 */
export const insert = <K>(S: Setoid<K>): (<A>(k: K, a: A, m: Map<K, A>) => Map<K, A>) => {
  const lookupS = lookupWithKey(S)
  return (k, a, m) => {
    const found = lookupS(k, m)
    if (found.isNone()) {
      const r = new Map(m)
      r.set(k, a)
      return r
    } else if (found.value[1] !== a) {
      const r = new Map(m)
      r.set(found.value[0], a)
      return r
    }
    return m
  }
}

/**
 * Delete a key and value from a map
 *
 * @since 1.14.0
 */
export const remove = <K>(S: Setoid<K>): (<A>(k: K, m: Map<K, A>) => Map<K, A>) => {
  const lookupS = lookupWithKey(S)
  return (k, m) => {
    const found = lookupS(k, m)
    if (found.isSome()) {
      const r = new Map(m)
      r.delete(found.value[0])
      return r
    }
    return m
  }
}

/**
 * Delete a key and value from a map, returning the value as well as the subsequent map
 *
 * @since 1.14.0
 */
export const pop = <K>(S: Setoid<K>): (<A>(k: K, m: Map<K, A>) => Option<[A, Map<K, A>]>) => {
  const lookupS = lookup(S)
  const removeS = remove(S)
  return (k, m) => lookupS(k, m).map(a => [a, removeS(k, m)])
}

/**
 * Lookup the value for a key in a `Map`.
 * If the result is a `Some`, the existing key is also returned.
 *
 * @since 1.14.0
 */
export const lookupWithKey = <K>(S: Setoid<K>) => <A>(k: K, m: Map<K, A>): Option<[K, A]> => {
  const entries = m.entries()
  let e: IteratorResult<[K, A]>
  while (!(e = entries.next()).done) {
    const [ka, a] = e.value
    if (S.equals(ka, k)) {
      return some([ka, a])
    }
  }
  return none
}

/**
 * Lookup the value for a key in a `Map`.
 *
 * @since 1.14.0
 */
export const lookup = <K>(S: Setoid<K>): (<A>(k: K, m: Map<K, A>) => Option<A>) => {
  const lookupWithKeyS = lookupWithKey(S)
  return (k, m) => lookupWithKeyS(k, m).map(([_, a]) => a)
}

/**
 * Test whether or not one Map contains all of the keys and values contained in another Map
 *
 * @since 1.14.0
 */
export const isSubmap = <K, A>(SK: Setoid<K>, SA: Setoid<A>): ((d1: Map<K, A>, d2: Map<K, A>) => boolean) => {
  const lookupWithKeyS = lookupWithKey(SK)
  return (d1: Map<K, A>, d2: Map<K, A>): boolean => {
    const entries = d1.entries()
    let e: IteratorResult<[K, A]>
    while (!(e = entries.next()).done) {
      const [k, a] = e.value
      const d2OptA = lookupWithKeyS(k, d2)
      if (d2OptA.isNone() || !SK.equals(k, d2OptA.value[0]) || !SA.equals(a, d2OptA.value[1])) {
        return false
      }
    }
    return true
  }
}

/**
 * @since 1.14.0
 */
export const empty = new Map<never, never>()

/**
 * @since 1.14.0
 */
export const getSetoid = <K, A>(SK: Setoid<K>, SA: Setoid<A>): Setoid<Map<K, A>> => {
  const isSubmap_ = isSubmap(SK, SA)
  return fromEquals((x, y) => isSubmap_(x, y) && isSubmap_(y, x))
}

/**
 * Gets `Monoid` instance for Maps given `Semigroup` instance for their values
 *
 * @since 1.14.0
 */
export const getMonoid = <K, A>(SK: Setoid<K>, SA: Semigroup<A>): Monoid<Map<K, A>> => {
  const lookupWithKeyS = lookupWithKey(SK)
  return {
    concat: (mx, my) => {
      const r = new Map(mx)
      const entries = my.entries()
      let e: IteratorResult<[K, A]>
      while (!(e = entries.next()).done) {
        const [k, a] = e.value
        const mxOptA = lookupWithKeyS(k, mx)
        if (mxOptA.isSome()) {
          r.set(mxOptA.value[0], SA.concat(mxOptA.value[1], a))
        } else {
          r.set(k, a)
        }
      }
      return r
    },
    empty
  }
}

/**
 * @since 1.14.0
 */
const filter = <K, A>(fa: Map<K, A>, p: Predicate<A>): Map<K, A> => filterWithIndex(fa, (_, a) => p(a))

/**
 * @since 1.14.0
 */
const mapWithIndex = <K, A, B>(fa: Map<K, A>, f: (k: K, a: A) => B): Map<K, B> => {
  const m = new Map<K, B>()
  const entries = fa.entries()
  let e: IteratorResult<[K, A]>
  while (!(e = entries.next()).done) {
    const [key, a] = e.value
    m.set(key, f(key, a))
  }
  return m
}

/**
 * @since 1.14.0
 */
const _map = <K, A, B>(fa: Map<K, A>, f: (a: A) => B): Map<K, B> => mapWithIndex(fa, (_, a) => f(a))

/**
 * @since 1.14.0
 */
const reduce = <K>(O: Ord<K>): (<A, B>(fa: Map<K, A>, b: B, f: (b: B, a: A) => B) => B) => {
  const reduceWithIndexO = reduceWithIndex(O)
  return (fa, b, f) => reduceWithIndexO(fa, b, (_, b, a) => f(b, a))
}

/**
 * @since 1.14.0
 */
const foldMap = <K>(O: Ord<K>): (<M>(M: Monoid<M>) => <A>(fa: Map<K, A>, f: (a: A) => M) => M) => M => {
  const foldMapWithIndexOM = foldMapWithIndex(O)(M)
  return (fa, f) => foldMapWithIndexOM(fa, (_, a) => f(a))
}

/**
 * @since 1.14.0
 */
const foldr = <K>(O: Ord<K>): (<A, B>(fa: Map<K, A>, b: B, f: (a: A, b: B) => B) => B) => {
  const foldrWithIndexO = foldrWithIndex(O)
  return (fa, b, f) => foldrWithIndexO(fa, b, (_, a, b) => f(a, b))
}

/**
 * @since 1.14.0
 */
const reduceWithIndex = <K>(O: Ord<K>): (<A, B>(fa: Map<K, A>, b: B, f: (k: K, b: B, a: A) => B) => B) => {
  const keysO = keys(O)
  return <A, B>(fa: Map<K, A>, b: B, f: (k: K, b: B, a: A) => B): B => {
    let out: B = b
    const ks = keysO(fa)
    const len = ks.length
    for (let i = 0; i < len; i++) {
      const k = ks[i]
      out = f(k, out, fa.get(k)!)
    }
    return out
  }
}

/**
 * @since 1.14.0
 */
const foldMapWithIndex = <K>(O: Ord<K>): (<M>(M: Monoid<M>) => <A>(fa: Map<K, A>, f: (k: K, a: A) => M) => M) => {
  const keysO = keys(O)
  return <M>(M: Monoid<M>) => <A>(fa: Map<K, A>, f: (k: K, a: A) => M): M => {
    let out: M = M.empty
    const ks = keysO(fa)
    const len = ks.length
    for (let i = 0; i < len; i++) {
      const k = ks[i]
      out = M.concat(out, f(k, fa.get(k)!))
    }
    return out
  }
}

/**
 * @since 1.14.0
 */
const foldrWithIndex = <K>(O: Ord<K>): (<A, B>(fa: Map<K, A>, b: B, f: (k: K, a: A, b: B) => B) => B) => {
  const keysO = keys(O)
  return <A, B>(fa: Map<K, A>, b: B, f: (k: K, a: A, b: B) => B): B => {
    let out: B = b
    const ks = keysO(fa)
    const len = ks.length
    for (let i = len - 1; i >= 0; i--) {
      const k = ks[i]
      out = f(k, fa.get(k)!, out)
    }
    return out
  }
}

/**
 * Create a map with one key/value pair
 *
 * @since 1.14.0
 */
export const singleton = <K, A>(k: K, a: A): Map<K, A> => {
  return new Map<K, A>([[k, a]])
}

/**
 * @since 1.14.0
 */
const traverseWithIndex = <F>(
  F: Applicative<F>
): (<K, A, B>(ta: Map<K, A>, f: (k: K, a: A) => HKT<F, B>) => HKT<F, Map<K, B>>) => {
  return <K, A, B>(ta: Map<K, A>, f: (k: K, a: A) => HKT<F, B>) => {
    let fm: HKT<F, Map<K, B>> = F.of(empty)
    const entries = ta.entries()
    let e: IteratorResult<[K, A]>
    while (!(e = entries.next()).done) {
      const [key, a] = e.value
      fm = F.ap(F.map(fm, m => (b: B) => new Map(m).set(key, b)), f(key, a))
    }
    return fm
  }
}

/**
 * @since 1.14.0
 */
const traverse = <F>(F: Applicative<F>): (<K, A, B>(ta: Map<K, A>, f: (a: A) => HKT<F, B>) => HKT<F, Map<K, B>>) => {
  const traverseWithIndexF = traverseWithIndex(F)
  return (ta, f) => traverseWithIndexF(ta, (_, a) => f(a))
}

/**
 * @since 1.14.0
 */
const sequence = <F>(F: Applicative<F>): (<K, A>(ta: Map<K, HKT<F, A>>) => HKT<F, Map<K, A>>) => {
  const traverseWithIndexF = traverseWithIndex(F)
  return ta => traverseWithIndexF(ta, (_, a) => a)
}

/**
 * @since 1.14.0
 */
const compact = <K, A>(fa: Map<K, Option<A>>): Map<K, A> => {
  const m = new Map<K, A>()
  const entries = fa.entries()
  let e: IteratorResult<[K, Option<A>]>
  while (!(e = entries.next()).done) {
    const [k, oa] = e.value
    if (oa.isSome()) {
      m.set(k, oa.value)
    }
  }
  return m
}

/**
 * @since 1.14.0
 */
const partitionMap = <K, RL, RR, A>(fa: Map<K, A>, f: (a: A) => Either<RL, RR>): Separated<Map<K, RL>, Map<K, RR>> =>
  partitionMapWithIndex(fa, (_, a) => f(a))

/**
 * @since 1.14.0
 */
const partition = <K, A>(fa: Map<K, A>, p: Predicate<A>): Separated<Map<K, A>, Map<K, A>> =>
  partitionWithIndex(fa, (_, a) => p(a))

/**
 * @since 1.14.0
 */
const separate = <K, RL, RR>(fa: Map<K, Either<RL, RR>>): Separated<Map<K, RL>, Map<K, RR>> => {
  const left = new Map<K, RL>()
  const right = new Map<K, RR>()
  const entries = fa.entries()
  let e: IteratorResult<[K, Either<RL, RR>]>
  while (!(e = entries.next()).done) {
    const [k, ei] = e.value
    if (ei.isLeft()) {
      left.set(k, ei.value)
    } else {
      right.set(k, ei.value)
    }
  }
  return {
    left,
    right
  }
}

/**
 * @since 1.14.0
 */
const wither = <F>(
  F: Applicative<F>
): (<K, A, B>(wa: Map<K, A>, f: (a: A) => HKT<F, Option<B>>) => HKT<F, Map<K, B>>) => {
  const traverseF = traverse(F)
  return (wa, f) => F.map(traverseF(wa, f), compact)
}

/**
 * @since 1.14.0
 */
const wilt = <F>(
  F: Applicative<F>
): (<K, RL, RR, A>(
  wa: Map<K, A>,
  f: (a: A) => HKT<F, Either<RL, RR>>
) => HKT<F, Separated<Map<K, RL>, Map<K, RR>>>) => {
  const traverseF = traverse(F)
  return (wa, f) => F.map(traverseF(wa, f), separate)
}

/**
 * @since 1.14.0
 */
const filterMap = <K, A, B>(fa: Map<K, A>, f: (a: A) => Option<B>): Map<K, B> => {
  return filterMapWithIndex(fa, (_, a) => f(a))
}

/**
 * @since 1.14.0
 */
const partitionMapWithIndex = <K, RL, RR, A>(
  fa: Map<K, A>,
  f: (k: K, a: A) => Either<RL, RR>
): Separated<Map<K, RL>, Map<K, RR>> => {
  const left = new Map<K, RL>()
  const right = new Map<K, RR>()
  const entries = fa.entries()
  let e: IteratorResult<[K, A]>
  while (!(e = entries.next()).done) {
    const [k, a] = e.value
    const ei = f(k, a)
    if (ei.isLeft()) {
      left.set(k, ei.value)
    } else {
      right.set(k, ei.value)
    }
  }
  return {
    left,
    right
  }
}

/**
 * @since 1.14.0
 */
const partitionWithIndex = <K, A>(fa: Map<K, A>, p: (k: K, a: A) => boolean): Separated<Map<K, A>, Map<K, A>> => {
  const left = new Map<K, A>()
  const right = new Map<K, A>()
  const entries = fa.entries()
  let e: IteratorResult<[K, A]>
  while (!(e = entries.next()).done) {
    const [k, a] = e.value
    if (p(k, a)) {
      right.set(k, a)
    } else {
      left.set(k, a)
    }
  }
  return {
    left,
    right
  }
}

/**
 * @since 1.14.0
 */
const filterMapWithIndex = <K, A, B>(fa: Map<K, A>, f: (k: K, a: A) => Option<B>): Map<K, B> => {
  const m = new Map<K, B>()
  const entries = fa.entries()
  let e: IteratorResult<[K, A]>
  while (!(e = entries.next()).done) {
    const [k, a] = e.value
    const o = f(k, a)
    if (o.isSome()) {
      m.set(k, o.value)
    }
  }
  return m
}

/**
 * @since 1.14.0
 */
const filterWithIndex = <K, A>(fa: Map<K, A>, p: (k: K, a: A) => boolean): Map<K, A> => {
  const m = new Map<K, A>()
  const entries = fa.entries()
  let e: IteratorResult<[K, A]>
  while (!(e = entries.next()).done) {
    const [k, a] = e.value
    if (p(k, a)) {
      m.set(k, a)
    }
  }
  return m
}

/**
 * Create a map from a foldable collection of key/value pairs, using the
 * specified function to combine values for duplicate keys.
 *
 * @since 1.14.0
 */
export function fromFoldable<K, F extends URIS3>(
  S: Setoid<K>,
  F: Foldable2v3<F>
): <U, L, A>(ta: Type3<F, U, L, [K, A]>, onConflict: (existing: A, a: A) => A) => Map<K, A>
export function fromFoldable<K, F extends URIS2>(
  S: Setoid<K>,
  F: Foldable2v2<F>
): <L, A>(ta: Type2<F, L, [K, A]>, onConflict: (existing: A, a: A) => A) => Map<K, A>
export function fromFoldable<K, F extends URIS>(
  S: Setoid<K>,
  F: Foldable2v1<F>
): <A>(ta: Type<F, [K, A]>, onConflict: (existing: A, a: A) => A) => Map<K, A>
export function fromFoldable<K, F>(
  S: Setoid<K>,
  F: Foldable2v<F>
): <A>(ta: HKT<F, [K, A]>, onConflict: (existing: A, a: A) => A) => Map<K, A>
export function fromFoldable<K, F>(
  S: Setoid<K>,
  F: Foldable2v<F>
): <A>(ta: HKT<F, [K, A]>, onConflict: (existing: A, a: A) => A) => Map<K, A> {
  return <A>(ta: HKT<F, [K, A]>, onConflict: (existing: A, a: A) => A) => {
    const lookupWithKeyS = lookupWithKey(S)
    return F.reduce<[K, A], Map<K, A>>(ta, new Map<K, A>(), (b, [k, a]) => {
      const bOpt = lookupWithKeyS(k, b)
      if (bOpt.isSome()) {
        b.set(bOpt.value[0], onConflict(bOpt.value[1], a))
      } else {
        b.set(k, a)
      }
      return b
    })
  }
}

/**
 * @since 1.14.0
 */
const compactable: Compactable2<URI> = {
  URI,
  compact,
  separate
}

/**
 * @since 1.14.0
 */
const functor: Functor2<URI> = {
  URI,
  map: _map
}

/**
 * @since 1.14.0
 */
const getFunctorWithIndex = <K>(): FunctorWithIndex2C<URI, K, K> => {
  return {
    _L: phantom,
    ...functor,
    mapWithIndex: mapWithIndex
  }
}

/**
 * @since 1.14.0
 */
const getFoldable = <K>(O: Ord<K>): Foldable2v2C<URI, K> => {
  return {
    URI,
    _L: phantom,
    reduce: reduce(O),
    foldMap: foldMap(O),
    foldr: foldr(O)
  }
}

/**
 * @since 1.14.0
 */
const getFoldableWithIndex = <K>(O: Ord<K>): FoldableWithIndex2C<URI, K, K> => {
  return {
    ...getFoldable(O),
    reduceWithIndex: reduceWithIndex(O),
    foldMapWithIndex: foldMapWithIndex(O),
    foldrWithIndex: foldrWithIndex(O)
  }
}

/**
 * @since 1.14.0
 */
const filterable: Filterable2<URI> = {
  ...compactable,
  ...functor,
  filter,
  filterMap,
  partition,
  partitionMap
}

/**
 * @since 1.14.0
 */
export const getFilterableWithIndex = <K>(): FilterableWithIndex2C<URI, K, K> => {
  return {
    ...filterable,
    ...getFunctorWithIndex<K>(),
    partitionMapWithIndex,
    partitionWithIndex,
    filterMapWithIndex,
    filterWithIndex
  }
}

/**
 * @since 1.14.0
 */
const getTraversable = <K>(O: Ord<K>): Traversable2v2C<URI, K> => {
  return {
    _L: phantom,
    ...getFoldable(O),
    ...functor,
    traverse,
    sequence
  }
}

/**
 * @since 1.14.0
 */
export const getWitherable = <K>(O: Ord<K>): Witherable2C<URI, K> => {
  return {
    ...filterable,
    ...getTraversable(O),
    wilt,
    wither
  }
}

/**
 * @since 1.14.0
 */
export const getTraversableWithIndex = <K>(O: Ord<K>): TraversableWithIndex2C<URI, K, K> => {
  return {
    ...getFunctorWithIndex<K>(),
    ...getFoldableWithIndex(O),
    ...getTraversable(O),
    traverseWithIndex
  }
}

/**
 * @since 1.14.0
 */
export const map: Filterable2<URI> = {
  URI,
  ...compactable,
  ...functor,
  ...filterable
}

/**
 * @file Data structure which represents non-empty arrays
 *
 * Use `NonEmptyArray2v` module instead.
 *
 * @deprecated
 */
import { Applicative }  from  './Applicative.ts'
import {
  array,
  findFirst as arrayFindFirst,
  findIndex as arrayFindIndex,
  findLast as arrayFindLast,
  findLastIndex as arrayFindLastIndex,
  insertAt as arrayInsertAt,
  last,
  lookup,
  sort,
  updateAt as arrayUpdateAt
} from './Array.ts'
import { Comonad1 }  from  './Comonad.ts'
import { FoldableWithIndex1 }  from  './FoldableWithIndex.ts'
import { compose, Predicate, Refinement, toString }  from  './function.ts'
import { FunctorWithIndex1 }  from  './FunctorWithIndex.ts'
import { HKT }  from  './HKT.ts'
import { Monad1 }  from  './Monad.ts'
import { Monoid }  from  './Monoid.ts'
import { none, Option, some }  from  './Option.ts'
import { Ord }  from  './Ord.ts'
import { fold, getJoinSemigroup, getMeetSemigroup, Semigroup }  from  './Semigroup.ts'
import { fromEquals, getArraySetoid, Setoid }  from  './Setoid.ts'
import { TraversableWithIndex1 }  from  './TraversableWithIndex.ts'

declare module './HKT.ts'
  interface URI2HKT<A> {
    NonEmptyArray: NonEmptyArray<A>
  }
}

export const URI = 'NonEmptyArray'

export type URI = typeof URI

/**
 * @since 1.0.0
 */
export class NonEmptyArray<A> {
  readonly _A!: A
  readonly _URI!: URI
  constructor(readonly head: A, readonly tail: Array<A>) {}

  /**
   * Converts this `NonEmptyArray` to a plain `Array`
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * assert.deepStrictEqual(new NonEmptyArray(1, [2, 3]).toArray(), [1, 2, 3])
   */
  toArray(): Array<A> {
    return [this.head, ...this.tail]
  }

  /**
   * Converts this `NonEmptyArray` to a plain `Array` using the given map function
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * assert.deepStrictEqual(new NonEmptyArray('a', ['bb', 'ccc']).toArrayMap(s => s.length), [1, 2, 3])
   *
   * @since 1.14.0
   */
  toArrayMap<B>(f: (a: A) => B): Array<B> {
    return [f(this.head), ...this.tail.map(a => f(a))]
  }

  /**
   * Concatenates this `NonEmptyArray` and passed `Array`
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * assert.deepStrictEqual(new NonEmptyArray<number>(1, []).concatArray([2]), new NonEmptyArray(1, [2]))
   */
  concatArray(as: Array<A>): NonEmptyArray<A> {
    return new NonEmptyArray(this.head, [...this.tail, ...as])
  }

  /**
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * const double = (n: number): number => n * 2
   * assert.deepStrictEqual(new NonEmptyArray(1, [2]).map(double), new NonEmptyArray(2, [4]))
   */
  map<B>(f: (a: A) => B): NonEmptyArray<B> {
    return new NonEmptyArray(f(this.head), this.tail.map(f))
  }

  mapWithIndex<B>(f: (i: number, a: A) => B): NonEmptyArray<B> {
    return new NonEmptyArray(f(0, this.head), array.mapWithIndex(this.tail, (i, a) => f(i + 1, a)))
  }

  /**
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * const x = new NonEmptyArray(1, [2])
   * const double = (n: number): number => n * 2
   * assert.deepStrictEqual(x.ap(new NonEmptyArray(double, [double])).toArray(), [2, 4, 2, 4])
   */
  ap<B>(fab: NonEmptyArray<(a: A) => B>): NonEmptyArray<B> {
    return fab.chain(f => this.map(f)) // <= derived
  }

  /**
   * Flipped version of `ap`
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * const x = new NonEmptyArray(1, [2])
   * const double = (n: number) => n * 2
   * assert.deepStrictEqual(new NonEmptyArray(double, [double]).ap_(x).toArray(), [2, 4, 2, 4])
   */
  ap_<B, C>(this: NonEmptyArray<(b: B) => C>, fb: NonEmptyArray<B>): NonEmptyArray<C> {
    return fb.ap(this)
  }

  /**
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * const x = new NonEmptyArray(1, [2])
   * const f = (a: number) => new NonEmptyArray(a, [4])
   * assert.deepStrictEqual(x.chain(f).toArray(), [1, 4, 2, 4])
   */
  chain<B>(f: (a: A) => NonEmptyArray<B>): NonEmptyArray<B> {
    return f(this.head).concatArray(array.chain(this.tail, a => f(a).toArray()))
  }

  /**
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * const x = new NonEmptyArray(1, [2])
   * const y = new NonEmptyArray(3, [4])
   * assert.deepStrictEqual(x.concat(y).toArray(), [1, 2, 3, 4])
   */
  concat(y: NonEmptyArray<A>): NonEmptyArray<A> {
    return this.concatArray(y.toArray())
  }

  /**
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * const x = new NonEmptyArray('a', ['b'])
   * assert.strictEqual(x.reduce('', (b, a) => b + a), 'ab')
   */
  reduce<B>(b: B, f: (b: B, a: A) => B): B {
    return array.reduce(this.toArray(), b, f)
  }

  /**
   * @since 1.12.0
   */
  reduceWithIndex<B>(b: B, f: (i: number, b: B, a: A) => B): B {
    return array.reduceWithIndex(this.toArray(), b, f)
  }

  /**
   * @since 1.12.0
   */
  foldr<B>(b: B, f: (a: A, b: B) => B): B {
    return this.foldrWithIndex(b, (_, a, b) => f(a, b))
  }

  /**
   * @since 1.12.0
   */
  foldrWithIndex<B>(b: B, f: (i: number, a: A, b: B) => B): B {
    return f(0, this.head, this.tail.reduceRight((acc, a, i) => f(i + 1, a, acc), b))
  }

  /**
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   * import { fold, monoidSum }  from  'fp-ts/lib/Monoid.ts'
   *
   * const sum = (as: NonEmptyArray<number>) => fold(monoidSum)(as.toArray())
   * assert.deepStrictEqual(new NonEmptyArray(1, [2, 3, 4]).extend(sum), new NonEmptyArray(10, [9, 7, 4]))
   */
  extend<B>(f: (fa: NonEmptyArray<A>) => B): NonEmptyArray<B> {
    return unsafeFromArray(array.extend(this.toArray(), as => f(unsafeFromArray(as))))
  }

  /**
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * assert.strictEqual(new NonEmptyArray(1, [2, 3]).extract(), 1)
   */
  extract(): A {
    return this.head
  }

  /**
   * Same as `toString`
   */
  inspect(): string {
    return this.toString()
  }

  /**
   * Return stringified representation of this `NonEmptyArray`
   */
  toString(): string {
    return `new NonEmptyArray(${toString(this.head)}, ${toString(this.tail)})`
  }

  /**
   * Gets minimum of this `NonEmptyArray` using specified `Ord` instance
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   * import { ordNumber }  from  'fp-ts/lib/Ord.ts'
   *
   * assert.strictEqual(new NonEmptyArray(1, [2, 3]).min(ordNumber), 1)
   *
   * @since 1.3.0
   */
  min(ord: Ord<A>): A {
    return fold(getMeetSemigroup(ord))(this.head)(this.tail)
  }

  /**
   * Gets maximum of this `NonEmptyArray` using specified `Ord` instance
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   * import { ordNumber }  from  'fp-ts/lib/Ord.ts'
   *
   * assert.strictEqual(new NonEmptyArray(1, [2, 3]).max(ordNumber), 3)
   *
   * @since 1.3.0
   */
  max(ord: Ord<A>): A {
    return fold(getJoinSemigroup(ord))(this.head)(this.tail)
  }

  /**
   * Gets last element of this `NonEmptyArray`
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * assert.strictEqual(new NonEmptyArray(1, [2, 3]).last(), 3)
   * assert.strictEqual(new NonEmptyArray(1, []).last(), 1)
   *
   * @since 1.6.0
   */
  last(): A {
    return last(this.tail).getOrElse(this.head)
  }

  /**
   * Sorts this `NonEmptyArray` using specified `Ord` instance
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   * import { ordNumber }  from  'fp-ts/lib/Ord.ts'
   *
   * assert.deepStrictEqual(new NonEmptyArray(3, [2, 1]).sort(ordNumber), new NonEmptyArray(1, [2, 3]))
   *
   * @since 1.6.0
   */
  sort(ord: Ord<A>): NonEmptyArray<A> {
    return unsafeFromArray(sort(ord)(this.toArray()))
  }

  /**
   * Reverts this `NonEmptyArray`
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   *
   * assert.deepStrictEqual(new NonEmptyArray(1, [2, 3]).reverse(), new NonEmptyArray(3, [2, 1]))
   *
   * @since 1.6.0
   */
  reverse(): NonEmptyArray<A> {
    return unsafeFromArray(this.toArray().reverse())
  }

  /**
   * @since 1.10.0
   */
  length(): number {
    return 1 + this.tail.length
  }

  /**
   * This function provides a safe way to read a value at a particular index from an NonEmptyArray
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   * import { some, none }  from  'fp-ts/lib/Option.ts'
   *
   * assert.deepStrictEqual(new NonEmptyArray(1, [2, 3]).lookup(1), some(2))
   * assert.deepStrictEqual(new NonEmptyArray(1, [2, 3]).lookup(3), none)
   *
   * @since 1.14.0
   */

  lookup(i: number): Option<A> {
    return i === 0 ? some(this.head) : lookup(i - 1, this.tail)
  }

  /**
   * Use `lookup` instead
   * @since 1.11.0
   * @deprecated
   */
  index(i: number): Option<A> {
    return this.lookup(i)
  }

  /**
   * Find the first element which satisfies a predicate (or a refinement) function
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   * import { some }  from  'fp-ts/lib/Option.ts'
   *
   * assert.deepStrictEqual(new NonEmptyArray({ a: 1, b: 1 }, [{ a: 1, b: 2 }]).findFirst(x => x.a === 1), some({ a: 1, b: 1 }))
   *
   * @since 1.11.0
   */
  findFirst<B extends A>(refinement: Refinement<A, B>): Option<B>
  findFirst(predicate: Predicate<A>): Option<A>
  findFirst(predicate: Predicate<A>): Option<A> {
    return predicate(this.head) ? some(this.head) : arrayFindFirst(this.tail, predicate)
  }
  /**
   * Find the last element which satisfies a predicate function
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   * import { some }  from  'fp-ts/lib/Option.ts'
   *
   * assert.deepStrictEqual(new NonEmptyArray({ a: 1, b: 1 }, [{ a: 1, b: 2 }]).findLast(x => x.a === 1), some({ a: 1, b: 2 }))
   *
   * @since 1.11.0
   */
  findLast<B extends A>(predicate: Refinement<A, B>): Option<B>
  findLast(predicate: Predicate<A>): Option<A>
  findLast(predicate: Predicate<A>): Option<A> {
    const a = arrayFindLast(this.tail, predicate)
    return a.isSome() ? a : predicate(this.head) ? some(this.head) : none
  }

  /**
   * Find the first index for which a predicate holds
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   * import { some, none }  from  'fp-ts/lib/Option.ts'
   *
   * assert.deepStrictEqual(new NonEmptyArray(1, [2, 3]).findIndex(x => x === 2), some(1))
   * assert.deepStrictEqual(new NonEmptyArray<number>(1, []).findIndex(x => x === 2), none)
   *
   * @since 1.11.0
   */
  findIndex(predicate: Predicate<A>): Option<number> {
    if (predicate(this.head)) {
      return some(0)
    } else {
      const i = arrayFindIndex(this.tail, predicate)
      return i.isSome() ? some(i.value + 1) : none
    }
  }

  /**
   * Returns the index of the last element of the list which matches the predicate
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   * import { some, none }  from  'fp-ts/lib/Option.ts'
   *
   * interface X {
   *   a: number
   *   b: number
   * }
   * const xs: NonEmptyArray<X> = new NonEmptyArray({ a: 1, b: 0 }, [{ a: 1, b: 1 }])
   * assert.deepStrictEqual(xs.findLastIndex(x => x.a === 1), some(1))
   * assert.deepStrictEqual(xs.findLastIndex(x => x.a === 4), none)
   *
   * @since 1.11.0
   */
  findLastIndex(predicate: Predicate<A>): Option<number> {
    const i = arrayFindLastIndex(this.tail, predicate)
    return i.isSome() ? some(i.value + 1) : predicate(this.head) ? some(0) : none
  }

  /**
   * Insert an element at the specified index, creating a new NonEmptyArray, or returning `None` if the index is out of bounds
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   * import { some }  from  'fp-ts/lib/Option.ts'
   *
   * assert.deepStrictEqual(new NonEmptyArray(1, [2, 3, 4]).insertAt(2, 5), some(new NonEmptyArray(1, [2, 5, 3, 4])))
   *
   * @since 1.11.0
   */
  insertAt(i: number, a: A): Option<NonEmptyArray<A>> {
    if (i === 0) {
      return some(new NonEmptyArray(a, this.toArray()))
    } else {
      const t = arrayInsertAt(i - 1, a, this.tail)
      return t.isSome() ? some(new NonEmptyArray(this.head, t.value)) : none
    }
  }

  /**
   * Change the element at the specified index, creating a new NonEmptyArray, or returning `None` if the index is out of bounds
   *
   * @example
   * import { NonEmptyArray }  from  'fp-ts/lib/NonEmptyArray.ts'
   * import { some, none }  from  'fp-ts/lib/Option.ts'
   *
   * assert.deepStrictEqual(new NonEmptyArray(1, [2, 3]).updateAt(1, 1), some(new NonEmptyArray(1, [1, 3])))
   * assert.deepStrictEqual(new NonEmptyArray(1, []).updateAt(1, 1), none)
   *
   * @since 1.11.0
   */

  updateAt(i: number, a: A): Option<NonEmptyArray<A>> {
    if (i === 0) {
      return this.head === a ? some(this) : some(new NonEmptyArray(a, this.tail))
    } else {
      const t = arrayUpdateAt(i - 1, a, this.tail)
      return t.isSome() ? (t.value === this.tail ? some(this) : some(new NonEmptyArray(this.head, t.value))) : none
    }
  }

  /**
   * Filter an NonEmptyArray, keeping the elements which satisfy a predicate function, creating a new NonEmptyArray or returning `None` in case the resulting NonEmptyArray would have no remaining elements.
   *
   * @since 1.11.0
   */
  filter<B extends A>(predicate: Refinement<A, B>): Option<NonEmptyArray<B>>
  filter(predicate: Predicate<A>): Option<NonEmptyArray<A>>
  filter(predicate: Predicate<A>): Option<NonEmptyArray<A>> {
    return this.filterWithIndex((_, a) => predicate(a))
  }

  /**
   * @since 1.12.0
   */
  filterWithIndex(predicate: (i: number, a: A) => boolean): Option<NonEmptyArray<A>> {
    const t = array.filterWithIndex(this.tail, (i, a) => predicate(i + 1, a))
    return predicate(0, this.head) ? some(new NonEmptyArray(this.head, t)) : fromArray(t)
  }

  /**
   * @since 1.14.0
   */
  some(predicate: Predicate<A>): boolean {
    return predicate(this.head) || this.tail.some(a => predicate(a))
  }

  /**
   * @since 1.14.0
   */
  every(predicate: Predicate<A>): boolean {
    return predicate(this.head) && this.tail.every(a => predicate(a))
  }
}

const unsafeFromArray = <A>(as: Array<A>): NonEmptyArray<A> => {
  return new NonEmptyArray(as[0], as.slice(1))
}

/**
 * Builds a `NonEmptyArray` from an `Array` returning `none` if `as` is an empty array
 *
 * @since 1.0.0
 */
export const fromArray = <A>(as: Array<A>): Option<NonEmptyArray<A>> => {
  return as.length > 0 ? some(unsafeFromArray(as)) : none
}

const map = <A, B>(fa: NonEmptyArray<A>, f: (a: A) => B): NonEmptyArray<B> => {
  return fa.map(f)
}

const mapWithIndex = <A, B>(fa: NonEmptyArray<A>, f: (i: number, a: A) => B): NonEmptyArray<B> => {
  return fa.mapWithIndex(f)
}

const of = <A>(a: A): NonEmptyArray<A> => {
  return new NonEmptyArray(a, [])
}

const ap = <A, B>(fab: NonEmptyArray<(a: A) => B>, fa: NonEmptyArray<A>): NonEmptyArray<B> => {
  return fa.ap(fab)
}

const chain = <A, B>(fa: NonEmptyArray<A>, f: (a: A) => NonEmptyArray<B>): NonEmptyArray<B> => {
  return fa.chain(f)
}

const concat = <A>(fx: NonEmptyArray<A>, fy: NonEmptyArray<A>): NonEmptyArray<A> => {
  return fx.concat(fy)
}

/**
 * Builds a `Semigroup` instance for `NonEmptyArray`
 *
 * @since 1.0.0
 */
export const getSemigroup = <A = never>(): Semigroup<NonEmptyArray<A>> => {
  return { concat }
}

/**
 * @example
 * import { NonEmptyArray, getSetoid }  from  'fp-ts/lib/NonEmptyArray.ts'
 * import { setoidNumber }  from  'fp-ts/lib/Setoid.ts'
 *
 * const S = getSetoid(setoidNumber)
 * assert.strictEqual(S.equals(new NonEmptyArray(1, []), new NonEmptyArray(1, [])), true)
 * assert.strictEqual(S.equals(new NonEmptyArray(1, []), new NonEmptyArray(1, [2])), false)
 *
 * @since 1.14.0
 */
export const getSetoid = <A>(S: Setoid<A>): Setoid<NonEmptyArray<A>> => {
  const setoidTail = getArraySetoid(S)
  return fromEquals((x, y) => S.equals(x.head, y.head) && setoidTail.equals(x.tail, y.tail))
}

/**
 * Group equal, consecutive elements of an array into non empty arrays.
 *
 * @example
 * import { NonEmptyArray, group }  from  'fp-ts/lib/NonEmptyArray.ts'
 * import { ordNumber }  from  'fp-ts/lib/Ord.ts'
 *
 * assert.deepStrictEqual(group(ordNumber)([1, 2, 1, 1]), [
 *   new NonEmptyArray(1, []),
 *   new NonEmptyArray(2, []),
 *   new NonEmptyArray(1, [1])
 * ])
 *
 * @since 1.7.0
 */
export const group = <A>(S: Setoid<A>) => (as: Array<A>): Array<NonEmptyArray<A>> => {
  const r: Array<NonEmptyArray<A>> = []
  const len = as.length
  if (len === 0) {
    return r
  }
  let head: A = as[0]
  let tail: Array<A> = []
  for (let i = 1; i < len; i++) {
    const x = as[i]
    if (S.equals(x, head)) {
      tail.push(x)
    } else {
      r.push(new NonEmptyArray(head, tail))
      head = x
      tail = []
    }
  }
  r.push(new NonEmptyArray(head, tail))
  return r
}

/**
 * Sort and then group the elements of an array into non empty arrays.
 *
 * @example
 * import { NonEmptyArray, groupSort }  from  'fp-ts/lib/NonEmptyArray.ts'
 * import { ordNumber }  from  'fp-ts/lib/Ord.ts'
 *
 * assert.deepStrictEqual(groupSort(ordNumber)([1, 2, 1, 1]), [new NonEmptyArray(1, [1, 1]), new NonEmptyArray(2, [])])
 *
 * @since 1.7.0
 */
export const groupSort = <A>(O: Ord<A>): ((as: Array<A>) => Array<NonEmptyArray<A>>) => {
  return compose(
    group(O),
    sort(O)
  )
}

const reduce = <A, B>(fa: NonEmptyArray<A>, b: B, f: (b: B, a: A) => B): B => {
  return fa.reduce(b, f)
}

const foldMap = <M>(M: Monoid<M>) => <A>(fa: NonEmptyArray<A>, f: (a: A) => M): M => {
  return fa.tail.reduce((acc, a) => M.concat(acc, f(a)), f(fa.head))
}

const foldr = <A, B>(fa: NonEmptyArray<A>, b: B, f: (a: A, b: B) => B): B => {
  return fa.foldr(b, f)
}

const reduceWithIndex = <A, B>(fa: NonEmptyArray<A>, b: B, f: (i: number, b: B, a: A) => B): B => {
  return fa.reduceWithIndex(b, f)
}

const foldMapWithIndex = <M>(M: Monoid<M>) => <A>(fa: NonEmptyArray<A>, f: (i: number, a: A) => M): M => {
  return fa.tail.reduce((acc, a, i) => M.concat(acc, f(i + 1, a)), f(0, fa.head))
}

const foldrWithIndex = <A, B>(fa: NonEmptyArray<A>, b: B, f: (i: number, a: A, b: B) => B): B => {
  return fa.foldrWithIndex(b, f)
}

const extend = <A, B>(fa: NonEmptyArray<A>, f: (fa: NonEmptyArray<A>) => B): NonEmptyArray<B> => {
  return fa.extend(f)
}

const extract = <A>(fa: NonEmptyArray<A>): A => {
  return fa.extract()
}

function traverse<F>(
  F: Applicative<F>
): <A, B>(ta: NonEmptyArray<A>, f: (a: A) => HKT<F, B>) => HKT<F, NonEmptyArray<B>> {
  const traverseWithIndexF = traverseWithIndex(F)
  return (ta, f) => traverseWithIndexF(ta, (_, a) => f(a))
}

function sequence<F>(F: Applicative<F>): <A>(ta: NonEmptyArray<HKT<F, A>>) => HKT<F, NonEmptyArray<A>> {
  const sequenceF = array.sequence(F)
  return <A>(ta: NonEmptyArray<HKT<F, A>>) =>
    F.ap(F.map(ta.head, a => (as: Array<A>) => new NonEmptyArray(a, as)), sequenceF(ta.tail))
}

/**
 * Splits an array into sub-non-empty-arrays stored in an object, based on the result of calling a `string`-returning
 * function on each element, and grouping the results according to values returned
 *
 * @example
 * import { NonEmptyArray, groupBy }  from  'fp-ts/lib/NonEmptyArray.ts'
 *
 * assert.deepStrictEqual(groupBy(['foo', 'bar', 'foobar'], a => String(a.length)), {
 *   '3': new NonEmptyArray('foo', ['bar']),
 *   '6': new NonEmptyArray('foobar', [])
 * })
 *
 * @since 1.10.0
 */
export const groupBy = <A>(as: Array<A>, f: (a: A) => string): { [key: string]: NonEmptyArray<A> } => {
  const r: { [key: string]: NonEmptyArray<A> } = {}
  for (const a of as) {
    const k = f(a)
    if (r.hasOwnProperty(k)) {
      r[k].tail.push(a)
    } else {
      r[k] = new NonEmptyArray(a, [])
    }
  }
  return r
}

const traverseWithIndex = <F>(
  F: Applicative<F>
): (<A, B>(ta: NonEmptyArray<A>, f: (i: number, a: A) => HKT<F, B>) => HKT<F, NonEmptyArray<B>>) => {
  const traverseWithIndexF = array.traverseWithIndex(F)
  return <A, B>(ta: NonEmptyArray<A>, f: (i: number, a: A) => HKT<F, B>) => {
    const fb = f(0, ta.head)
    const fbs = traverseWithIndexF(ta.tail, (i, a) => f(i + 1, a))
    return F.ap(F.map(fb, b => (bs: Array<B>) => new NonEmptyArray(b, bs)), fbs)
  }
}

/**
 * @since 1.0.0
 */
export const nonEmptyArray: Monad1<URI> &
  Comonad1<URI> &
  TraversableWithIndex1<URI, number> &
  FunctorWithIndex1<URI, number> &
  FoldableWithIndex1<URI, number> = {
  URI,
  extend,
  extract,
  map,
  mapWithIndex,
  of,
  ap,
  chain,
  reduce,
  foldMap,
  foldr,
  traverse,
  sequence,
  reduceWithIndex,
  foldMapWithIndex,
  foldrWithIndex,
  traverseWithIndex
}

