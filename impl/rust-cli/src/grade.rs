// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Resource grades: deterministic accounting for bounded work and bounded holdings.
//!
//! A shell operation can use a resource in two different ways, and the two
//! compose differently:
//!
//! - **Cost** is consumed and never given back: directory entries read,
//!   comparisons made. Doing one thing and then another costs the *sum*.
//! - **Occupancy** is held for a while and may be released: paths kept in
//!   memory, history entries retained. What matters is the *high-water mark*,
//!   the most that was held at one time.
//!
//! A [`Grade`] is a value of one of those two kinds. A [`Meter`] measures a
//! grade while the work runs and refuses a charge that would pass its limit,
//! so a limit is enforced where the resource is used and not after the fact.
//!
//! Both kinds are plain counts. They depend only on the input and on the state
//! of the file system, never on the clock or on the machine, so a test can
//! compute the expected grade independently and compare it for equality.
//!
//! # Laws
//!
//! For both kinds, [`Grade::then`] is associative with [`Grade::ZERO`] as its
//! identity, [`Grade::either`] is associative, commutative and idempotent, and
//! `then` distributes over `either`. Metering a sequence of charges gives
//! exactly the grade obtained by composing those charges with `then`. The tests
//! at the end of this file check these laws on random inputs; they are tests,
//! not proofs.
//!
//! # Relation to the estate's type theories
//!
//! The split follows the vocabulary of `tropical-types` (cost: sequence adds,
//! choice takes the maximum) and of occupancy grades (high-water marks) as
//! summarised in `docs/THEORY-FEED.adoc`. Nothing is imported from those
//! repositories and no theorem of theirs is relied on here.
//!
//! # Examples
//!
//! ```
//! use vsh::grade::{Cost, Grade, Meter, Occupancy};
//!
//! // Cost adds up.
//! assert_eq!(Cost::of(3).then(Cost::of(4)), Cost::of(7));
//!
//! // Occupancy keeps what is still held and remembers the peak.
//! let held = Occupancy::of(5).then(Occupancy::of(2));
//! assert_eq!((held.held(), held.peak()), (7, 7));
//! assert_eq!(held.released(6).peak(), 7);
//!
//! // A meter refuses the charge that would pass its limit.
//! let mut entries: Meter<Cost> = Meter::new("directory entries read", 2);
//! assert!(entries.charge(2).is_ok());
//! let refused = entries.charge(1).unwrap_err();
//! assert_eq!((refused.limit, refused.level), (2, 3));
//! assert_eq!(entries.level(), 2); // the refused charge was not recorded
//! ```

use std::fmt;

/// A summary of how much of one resource a piece of work used.
///
/// See the [module documentation](self) for the two kinds and their laws.
pub trait Grade: Copy + Eq + fmt::Debug {
    /// The grade of doing nothing.
    const ZERO: Self;

    /// The grade of using `amount` units in a single step.
    fn of(amount: u64) -> Self;

    /// Sequential composition: this work, and then `next`.
    ///
    /// `next` starts from whatever this work still holds.
    #[must_use]
    fn then(self, next: Self) -> Self;

    /// The worst case of two alternatives, of which only one happens.
    #[must_use]
    fn either(self, other: Self) -> Self;

    /// The single number a limit is compared against.
    fn level(self) -> u64;
}

/// A cumulative cost: a resource that is consumed and never given back.
///
/// Sequential composition adds; the worst case of two alternatives is the
/// larger. Addition saturates at `u64::MAX` instead of wrapping.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Cost(u64);

impl Cost {
    /// The total consumed.
    pub const fn total(self) -> u64 {
        self.0
    }
}

impl Grade for Cost {
    const ZERO: Self = Cost(0);

    fn of(amount: u64) -> Self {
        Cost(amount)
    }

    fn then(self, next: Self) -> Self {
        Cost(self.0.saturating_add(next.0))
    }

    fn either(self, other: Self) -> Self {
        Cost(self.0.max(other.0))
    }

    fn level(self) -> u64 {
        self.0
    }
}

impl fmt::Display for Cost {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An occupancy: how much of a resource is held now, and the most that was
/// ever held at one time.
///
/// Invariant: `peak >= held`. Every constructor and operation preserves it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Occupancy {
    held: u64,
    peak: u64,
}

impl Occupancy {
    /// How much is held at the end of the work.
    pub const fn held(self) -> u64 {
        self.held
    }

    /// The high-water mark: the most that was held at one time.
    pub const fn peak(self) -> u64 {
        self.peak
    }

    /// The same work after giving back `amount` units of what it holds.
    ///
    /// Releasing more than is held releases everything. The peak is unchanged:
    /// a release cannot undo a high-water mark.
    #[must_use]
    pub fn released(self, amount: u64) -> Self {
        Occupancy {
            held: self.held.saturating_sub(amount),
            peak: self.peak,
        }
    }

    /// The same work after giving back everything it holds.
    #[must_use]
    pub fn settled(self) -> Self {
        self.released(self.held)
    }
}

impl Grade for Occupancy {
    const ZERO: Self = Occupancy { held: 0, peak: 0 };

    fn of(amount: u64) -> Self {
        Occupancy {
            held: amount,
            peak: amount,
        }
    }

    /// `next` runs on top of what this work still holds, so its peak is
    /// measured from there.
    fn then(self, next: Self) -> Self {
        Occupancy {
            held: self.held.saturating_add(next.held),
            peak: self.peak.max(self.held.saturating_add(next.peak)),
        }
    }

    fn either(self, other: Self) -> Self {
        Occupancy {
            held: self.held.max(other.held),
            peak: self.peak.max(other.peak),
        }
    }

    fn level(self) -> u64 {
        self.peak
    }
}

impl fmt::Display for Occupancy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (peak {})", self.held, self.peak)
    }
}

/// A charge that a [`Meter`] refused because it would pass the limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Exceeded {
    /// What was being counted, for example `"directory entries read"`.
    pub axis: &'static str,
    /// The limit that was configured.
    pub limit: u64,
    /// The level the refused charge would have reached.
    pub level: u64,
}

impl fmt::Display for Exceeded {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} would reach {}, over the limit of {}",
            self.axis, self.level, self.limit
        )
    }
}

impl std::error::Error for Exceeded {}

/// Measures one grade against a limit while the work runs.
///
/// Invariant: `level() <= limit()`. A charge that would break it is refused
/// and leaves the meter unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Meter<G> {
    axis: &'static str,
    limit: u64,
    grade: G,
}

impl<G: Grade> Meter<G> {
    /// A meter at zero for the resource named `axis`, allowing at most `limit`.
    pub const fn new(axis: &'static str, limit: u64) -> Self {
        Meter {
            axis,
            limit,
            grade: G::ZERO,
        }
    }

    /// Record the use of `amount` more units, or refuse if that passes the limit.
    ///
    /// # Errors
    /// Returns [`Exceeded`] and records nothing when the charge would take the
    /// level over the limit.
    pub fn charge(&mut self, amount: u64) -> Result<(), Exceeded> {
        let next = self.grade.then(G::of(amount));
        if next.level() > self.limit {
            return Err(Exceeded {
                axis: self.axis,
                limit: self.limit,
                level: next.level(),
            });
        }
        self.grade = next;
        Ok(())
    }

    /// The grade measured so far.
    pub fn grade(&self) -> G {
        self.grade
    }

    /// The level measured so far; never more than [`Meter::limit`].
    pub fn level(&self) -> u64 {
        self.grade.level()
    }

    /// The configured limit.
    pub fn limit(&self) -> u64 {
        self.limit
    }

    /// What this meter counts.
    pub fn axis(&self) -> &'static str {
        self.axis
    }
}

impl Meter<Occupancy> {
    /// Record that `amount` units are no longer held.
    ///
    /// Only an occupancy can be released. There is deliberately no such method
    /// on `Meter<Cost>`: a cost that has been paid cannot be taken back.
    pub fn release(&mut self, amount: u64) {
        self.grade = self.grade.released(amount);
    }

    /// How much is held right now.
    pub fn held(&self) -> u64 {
        self.grade.held()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn cost_adds_in_sequence_and_takes_the_larger_alternative() {
        assert_eq!(Cost::of(3).then(Cost::of(4)), Cost::of(7));
        assert_eq!(Cost::of(3).either(Cost::of(4)), Cost::of(4));
        assert_eq!(Cost::ZERO.total(), 0);
    }

    #[test]
    fn cost_saturates_instead_of_wrapping() {
        assert_eq!(Cost::of(u64::MAX).then(Cost::of(1)), Cost::of(u64::MAX));
    }

    #[test]
    fn occupancy_remembers_the_peak_after_a_release() {
        let work = Occupancy::of(10).released(8).then(Occupancy::of(3));
        assert_eq!(work.held(), 5);
        assert_eq!(work.peak(), 10);
    }

    #[test]
    fn occupancy_of_two_settled_phases_is_the_larger_peak() {
        let first = Occupancy::of(10).settled();
        let second = Occupancy::of(4).settled();
        let both = first.then(second);
        assert_eq!((both.held(), both.peak()), (0, 10));
    }

    #[test]
    fn occupancy_of_two_retained_phases_adds() {
        let both = Occupancy::of(10).then(Occupancy::of(4));
        assert_eq!((both.held(), both.peak()), (14, 14));
    }

    #[test]
    fn meter_accepts_up_to_the_limit_and_refuses_the_next_unit() {
        let mut meter: Meter<Cost> = Meter::new("steps", 3);
        assert!(meter.charge(3).is_ok());
        assert_eq!(meter.level(), 3);

        let refused = meter.charge(1).unwrap_err();
        assert_eq!(
            refused,
            Exceeded {
                axis: "steps",
                limit: 3,
                level: 4
            }
        );
        assert_eq!(meter.level(), 3, "a refused charge must not be recorded");
        assert_eq!(
            refused.to_string(),
            "steps would reach 4, over the limit of 3"
        );
    }

    #[test]
    fn occupancy_meter_can_reuse_what_was_released() {
        let mut meter: Meter<Occupancy> = Meter::new("items held", 10);
        meter.charge(10).unwrap();
        assert!(meter.charge(1).is_err());

        meter.release(4);
        assert_eq!(meter.held(), 6);
        assert!(meter.charge(4).is_ok(), "released room can be used again");
        assert!(meter.charge(1).is_err());
        assert_eq!(meter.grade().peak(), 10);
    }

    #[test]
    fn a_meter_with_a_zero_limit_refuses_any_use() {
        let mut meter: Meter<Occupancy> = Meter::new("items held", 0);
        assert!(meter.charge(0).is_ok());
        assert!(meter.charge(1).is_err());
    }

    /// A well-formed occupancy: `peak >= held`.
    fn occupancy() -> impl Strategy<Value = Occupancy> {
        (any::<u32>(), any::<u32>()).prop_map(|(held, extra)| Occupancy {
            held: u64::from(held),
            peak: u64::from(held) + u64::from(extra),
        })
    }

    fn cost() -> impl Strategy<Value = Cost> {
        any::<u64>().prop_map(Cost::of)
    }

    /// The laws stated in the module documentation, for any grade.
    fn check_laws<G: Grade>(a: G, b: G, c: G) -> Result<(), TestCaseError> {
        // `then` is a monoid.
        prop_assert_eq!(a.then(b).then(c), a.then(b.then(c)));
        prop_assert_eq!(G::ZERO.then(a), a);
        prop_assert_eq!(a.then(G::ZERO), a);
        // `either` is a semilattice.
        prop_assert_eq!(a.either(b).either(c), a.either(b.either(c)));
        prop_assert_eq!(a.either(b), b.either(a));
        prop_assert_eq!(a.either(a), a);
        // `then` distributes over `either` on both sides.
        prop_assert_eq!(a.then(b.either(c)), a.then(b).either(a.then(c)));
        prop_assert_eq!(a.either(b).then(c), a.then(c).either(b.then(c)));
        // Doing more never lowers the level.
        prop_assert!(a.then(b).level() >= a.level());
        prop_assert!(a.either(b).level() >= a.level());
        Ok(())
    }

    proptest! {
        #[test]
        fn cost_obeys_the_grade_laws(a in cost(), b in cost(), c in cost()) {
            check_laws(a, b, c)?;
        }

        #[test]
        fn occupancy_obeys_the_grade_laws(a in occupancy(), b in occupancy(), c in occupancy()) {
            check_laws(a, b, c)?;
        }

        #[test]
        fn occupancy_operations_keep_peak_at_least_held(
            a in occupancy(),
            b in occupancy(),
            amount in any::<u64>(),
        ) {
            for grade in [a.then(b), a.either(b), a.released(amount), a.settled()] {
                prop_assert!(grade.peak() >= grade.held());
            }
            prop_assert_eq!(a.released(amount).peak(), a.peak());
            prop_assert_eq!(a.settled().held(), 0);
        }

        /// Metering charges one by one gives exactly the grade obtained by
        /// composing them, and never passes the limit.
        #[test]
        fn a_cost_meter_agrees_with_composition(
            charges in prop::collection::vec(0u64..1_000, 0..40),
            limit in 0u64..20_000,
        ) {
            let mut meter: Meter<Cost> = Meter::new("steps", limit);
            let mut composed = Cost::ZERO;
            for amount in charges {
                let wanted = composed.then(Cost::of(amount));
                match meter.charge(amount) {
                    Ok(()) => {
                        prop_assert!(wanted.level() <= limit);
                        composed = wanted;
                    }
                    Err(refused) => {
                        prop_assert!(wanted.level() > limit);
                        prop_assert_eq!(refused.level, wanted.level());
                        prop_assert_eq!(refused.limit, limit);
                    }
                }
                prop_assert_eq!(meter.grade(), composed);
                prop_assert!(meter.level() <= meter.limit());
            }
        }

        /// The same for an occupancy meter, with releases mixed in.
        #[test]
        fn an_occupancy_meter_agrees_with_composition(
            steps in prop::collection::vec((any::<bool>(), 0u64..1_000), 0..40),
            limit in 0u64..5_000,
        ) {
            let mut meter: Meter<Occupancy> = Meter::new("items held", limit);
            let mut composed = Occupancy::ZERO;
            for (is_release, amount) in steps {
                if is_release {
                    meter.release(amount);
                    composed = composed.released(amount);
                } else {
                    let wanted = composed.then(Occupancy::of(amount));
                    match meter.charge(amount) {
                        Ok(()) => {
                            prop_assert!(wanted.level() <= limit);
                            composed = wanted;
                        }
                        Err(refused) => {
                            prop_assert!(wanted.level() > limit);
                            prop_assert_eq!(refused.level, wanted.level());
                        }
                    }
                }
                prop_assert_eq!(meter.grade(), composed);
                prop_assert!(meter.level() <= meter.limit());
                prop_assert!(meter.held() <= meter.level());
            }
        }
    }
}
