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

declare module './HKT' {
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

declare module './HKT' {
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

declare module './HKT' {
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

