/// @title i64
/// @notice Signed 64-bit integers in Move.
/// from: https://github.com/ThalaLabs/movemate/blob/main/aptos/sources/i64.move
module thala_signed_math::i64 {
    use std::error;

    /// @dev Maximum I64 value as a u64.
    const MAX_I64_AS_U64: u64 = (1 << 63) - 1;

    /// @dev u64 with the first bit set. An `I64` is negative if this bit is set.
    const U64_WITH_FIRST_BIT_SET: u64 = 1 << 63;

    /// When both `U256` equal.
    const EQUAL: u8 = 0;

    /// When `a` is less than `b`.
    const LESS_THAN: u8 = 1;

    /// When `b` is greater than `b`.
    const GREATER_THAN: u8 = 2;

    /// @dev When trying to convert from a u64 > MAX_I64_AS_U64 to an I64.
    const ECONVERSION_FROM_U64_OVERFLOW: u64 = 0;

    /// @dev When trying to convert from an negative I64 to a u64.
    const ECONVERSION_TO_U64_UNDERFLOW: u64 = 1;

    /// @notice Struct representing a signed 64-bit integer.
    struct I64 has copy, drop, store {
        bits: u64
    }

    /// @notice Casts a `u64` to an `I64`.
    public fun from_u64(x: u64): I64 {
        assert!(x <= MAX_I64_AS_U64, error::invalid_argument(ECONVERSION_FROM_U64_OVERFLOW));
        I64 { bits: x }
    }

    /// @notice Creates a new `I64` with value 0.
    public fun zero(): I64 {
        I64 { bits: 0 }
    }

    /// @notice Creates a new `I64` with value 1.
    public fun one(): I64 {
        I64 { bits: 1 }
    }

    /// @notice Casts an `I64` to a `u64`.
    public fun to_u64(x: &I64): u64 {
        assert!(x.bits < U64_WITH_FIRST_BIT_SET, error::invalid_argument(ECONVERSION_TO_U64_UNDERFLOW));
        x.bits
    }

    /// @notice Whether or not `x` is equal to 0.
    public fun is_zero(x: &I64): bool {
        x.bits == 0
    }

    /// @notice Whether or not `x` is negative.
    public fun is_neg(x: &I64): bool {
        x.bits > U64_WITH_FIRST_BIT_SET
    }

    /// @notice Flips the sign of `x`.
    public fun neg(x: &I64): I64 {
        if (x.bits == 0) return *x;
        I64 { bits: if (x.bits < U64_WITH_FIRST_BIT_SET) x.bits | (1 << 63) else x.bits - (1 << 63) }
    }

    /// @notice Flips the sign of `x`.
    public fun neg_from_u64(x: u64): I64 {
        let ret = from_u64(x);
        if (ret.bits > 0) *&mut ret.bits = ret.bits | (1 << 63);
        ret
    }

    /// @notice Absolute value of `x`.
    public fun abs(x: &I64): I64 {
        if (x.bits < U64_WITH_FIRST_BIT_SET) *x else I64 { bits: x.bits - (1 << 63) }
    }

    /// @notice Compare `a` and `b`.
    public fun compare(a: &I64, b: &I64): u8 {
        if (a.bits == b.bits) return EQUAL;
        if (a.bits < U64_WITH_FIRST_BIT_SET) {
            // A is positive
            if (b.bits < U64_WITH_FIRST_BIT_SET) {
                // B is positive
                return if (a.bits > b.bits) GREATER_THAN else LESS_THAN
            } else {
                // B is negative
                return GREATER_THAN
            }
        } else {
            // A is negative
            if (b.bits < U64_WITH_FIRST_BIT_SET) {
                // B is positive
                return LESS_THAN
            } else {
                // B is negative
                return if (a.bits > b.bits) LESS_THAN else GREATER_THAN
            }
        }
    }

    /// @notice Add `a + b`.
    public fun add(a: &I64, b: u64): I64 {
        if (a.bits >> 63 == 0) {
            // A is positive
            return I64 { bits: a.bits + b }
        } else {
            // A is negative
            if (a.bits - (1 << 63) <= b) return I64 { bits: b - (a.bits - (1 << 63)) }; // Return positive
            return I64 { bits: a.bits - b } // Return negative
        }
    }

    /// @notice Subtract `a - b`.
    public fun sub(a: &I64, b: u64): I64 {
        if (a.bits >> 63 == 0) {
            // A is positive
            if (a.bits >= b) return I64 { bits: a.bits - b }; // Return positive
            return I64 { bits: (1 << 63) | (b - a.bits) } // Return negative
        } else {
            // A is negative
            return I64 { bits: a.bits + b } // Return negative
        }
    }

    /// @notice Multiply `a * b`.
    public fun mul(a: &I64, b: u64): I64 {
        if (a.bits >> 63 == 0) {
            // A is positive
            return I64 { bits: a.bits * b } // Return positive
        } else {
            // A is negative
            return I64 { bits: (1 << 63) | (b * (a.bits - (1 << 63))) } // Return negative
        }
    }

    /// @notice Divide `a / b`.
    public fun div(a: &I64, b: u64): I64 {
        if (a.bits >> 63 == 0) {
            // A is positive
            return I64 { bits: a.bits / b } // Return positive
        } else {
            // A is negative
            return I64 { bits: (1 << 63) | ((a.bits - (1 << 63)) / b) } // Return negative
        }
    }

    /// @notice Add `a + b`.
    public fun add_i64(a: &I64, b: &I64): I64 {
        if (a.bits >> 63 == 0) {
            // A is positive
            if (b.bits >> 63 == 0) {
                // B is positive
                return I64 { bits: a.bits + b.bits }
            } else {
                // B is negative
                if (b.bits - (1 << 63) <= a.bits) return I64 { bits: a.bits - (b.bits - (1 << 63)) }; // Return positive
                return I64 { bits: b.bits - a.bits } // Return negative
            }
        } else {
            // A is negative
            if (b.bits >> 63 == 0) {
                // B is positive
                if (a.bits - (1 << 63) <= b.bits) return I64 { bits: b.bits - (a.bits - (1 << 63)) }; // Return positive
                return I64 { bits: a.bits - b.bits } // Return negative
            } else {
                // B is negative
                return I64 { bits: a.bits + (b.bits - (1 << 63)) }
            }
        }
    }

    /// @notice Subtract `a - b`.
    public fun sub_i64(a: &I64, b: &I64): I64 {
        if (a.bits >> 63 == 0) {
            // A is positive
            if (b.bits >> 63 == 0) {
                // B is positive
                if (a.bits >= b.bits) return I64 { bits: a.bits - b.bits }; // Return positive
                return I64 { bits: (1 << 63) | (b.bits - a.bits) } // Return negative
            } else {
                // B is negative
                return I64 { bits: a.bits + (b.bits - (1 << 63)) } // Return negative
            }
        } else {
            // A is negative
            if (b.bits >> 63 == 0) {
                // B is positive
                return I64 { bits: a.bits + b.bits } // Return negative
            } else {
                // B is negative
                if (b.bits >= a.bits) return I64 { bits: b.bits - a.bits }; // Return positive
                return I64 { bits: a.bits - (b.bits - (1 << 63)) } // Return negative
            }
        }
    }

    /// @notice Multiply `a * b`.
    public fun mul_i64(a: &I64, b: &I64): I64 {
        if (a.bits >> 63 == 0) {
            // A is positive
            if (b.bits >> 63 == 0) {
                // B is positive
                return I64 { bits: a.bits * b.bits } // Return positive
            } else {
                // B is negative
                return I64 { bits: (1 << 63) | (a.bits * (b.bits - (1 << 63))) } // Return negative
            }
        } else {
            // A is negative
            if (b.bits >> 63 == 0) {
                // B is positive
                return I64 { bits: (1 << 63) | (b.bits * (a.bits - (1 << 63))) } // Return negative
            } else {
                // B is negative
                return I64 { bits: (a.bits - (1 << 63)) * (b.bits - (1 << 63)) } // Return positive
            }
        }
    }

    /// @notice Divide `a / b`.
    public fun div_i64(a: &I64, b: &I64): I64 {
        if (a.bits >> 63 == 0) {
            // A is positive
            if (b.bits >> 63 == 0) {
                // B is positive
                return I64 { bits: a.bits / b.bits } // Return positive
            } else {
                // B is negative
                return I64 { bits: (1 << 63) | (a.bits / (b.bits - (1 << 63))) } // Return negative
            }
        } else {
            // A is negative
            if (b.bits >> 63 == 0) {
                // B is positive
                return I64 { bits: (1 << 63) | ((a.bits - (1 << 63)) / b.bits) } // Return negative
            } else {
                // B is negative
                return I64 { bits: (a.bits - (1 << 63)) / (b.bits - (1 << 63)) } // Return positive
            }
        }
    }

    #[view]
    public fun equal(): u8 {
        EQUAL
    }

    #[view]
    public fun less_than(): u8 {
        LESS_THAN
    }

    #[view]
    public fun greater_than(): u8 {
        GREATER_THAN
    }

    #[test]
    fun test_compare() {
        assert!(compare(&from_u64(123), &from_u64(123)) == EQUAL, 0);
        assert!(compare(&neg_from_u64(123), &neg_from_u64(123)) == EQUAL, 0);
        assert!(compare(&from_u64(234), &from_u64(123)) == GREATER_THAN, 0);
        assert!(compare(&from_u64(123), &from_u64(234)) == LESS_THAN, 0);
        assert!(compare(&neg_from_u64(234), &neg_from_u64(123)) == LESS_THAN, 0);
        assert!(compare(&neg_from_u64(123), &neg_from_u64(234)) == GREATER_THAN, 0);
        assert!(compare(&from_u64(123), &neg_from_u64(234)) == GREATER_THAN, 0);
        assert!(compare(&neg_from_u64(123), &from_u64(234)) == LESS_THAN, 0);
        assert!(compare(&from_u64(234), &neg_from_u64(123)) == GREATER_THAN, 0);
        assert!(compare(&neg_from_u64(234), &from_u64(123)) == LESS_THAN, 0);
    }

    #[test]
    fun test_add() {
        assert!(add(&from_u64(123), 234) == from_u64(357), 0);
        assert!(add(&neg_from_u64(123), 234) == from_u64(111), 0);

        assert!(add(&neg_from_u64(123), 123) == zero(), 0);
    }

    #[test]
    fun test_sub() {
        assert!(sub(&from_u64(123), 234) == neg_from_u64(111), 0);
        assert!(sub(&from_u64(234), 123) == from_u64(111), 0);
        assert!(sub(&neg_from_u64(123), 234) == neg_from_u64(357), 0);

        assert!(sub(&from_u64(123), 123) == zero(), 0);
    }

    #[test]
    fun test_mul() {
        assert!(mul(&from_u64(123), 234) == from_u64(28782), 0);
        assert!(mul(&neg_from_u64(123), 234) == neg_from_u64(28782), 0);
    }

    #[test]
    fun test_div() {
        assert!(div(&from_u64(28781), 123) == from_u64(233), 0);
        assert!(div(&neg_from_u64(28781), 123) == neg_from_u64(233), 0);
    }

    #[test]
    fun test_add_i64() {
        assert!(add_i64(&from_u64(123), &from_u64(234)) == from_u64(357), 0);
        assert!(add_i64(&from_u64(123), &neg_from_u64(234)) == neg_from_u64(111), 0);
        assert!(add_i64(&from_u64(234), &neg_from_u64(123)) == from_u64(111), 0);
        assert!(add_i64(&neg_from_u64(123), &from_u64(234)) == from_u64(111), 0);
        assert!(add_i64(&neg_from_u64(123), &neg_from_u64(234)) == neg_from_u64(357), 0);
        assert!(add_i64(&neg_from_u64(234), &neg_from_u64(123)) == neg_from_u64(357), 0);

        assert!(add_i64(&from_u64(123), &neg_from_u64(123)) == zero(), 0);
        assert!(add_i64(&neg_from_u64(123), &from_u64(123)) == zero(), 0);
    }

    #[test]
    fun test_sub_i64() {
        assert!(sub_i64(&from_u64(123), &from_u64(234)) == neg_from_u64(111), 0);
        assert!(sub_i64(&from_u64(234), &from_u64(123)) == from_u64(111), 0);
        assert!(sub_i64(&from_u64(123), &neg_from_u64(234)) == from_u64(357), 0);
        assert!(sub_i64(&neg_from_u64(123), &from_u64(234)) == neg_from_u64(357), 0);
        assert!(sub_i64(&neg_from_u64(123), &neg_from_u64(234)) == from_u64(111), 0);
        assert!(sub_i64(&neg_from_u64(234), &neg_from_u64(123)) == neg_from_u64(111), 0);

        assert!(sub_i64(&from_u64(123), &from_u64(123)) == zero(), 0);
        assert!(sub_i64(&neg_from_u64(123), &neg_from_u64(123)) == zero(), 0);
    }

    #[test]
    fun test_mul_i64() {
        assert!(mul_i64(&from_u64(123), &from_u64(234)) == from_u64(28782), 0);
        assert!(mul_i64(&from_u64(123), &neg_from_u64(234)) == neg_from_u64(28782), 0);
        assert!(mul_i64(&neg_from_u64(123), &from_u64(234)) == neg_from_u64(28782), 0);
        assert!(mul_i64(&neg_from_u64(123), &neg_from_u64(234)) == from_u64(28782), 0);
    }

    #[test]
    fun test_div_i64() {
        assert!(div_i64(&from_u64(28781), &from_u64(123)) == from_u64(233), 0);
        assert!(div_i64(&from_u64(28781), &neg_from_u64(123)) == neg_from_u64(233), 0);
        assert!(div_i64(&neg_from_u64(28781), &from_u64(123)) == neg_from_u64(233), 0);
        assert!(div_i64(&neg_from_u64(28781), &neg_from_u64(123)) == from_u64(233), 0);
    }

    /// Less than
    public fun lt(left: &I64, right: &I64): bool {
        compare(left, right) == LESS_THAN
    }

    /// Greater than
    public fun gt(left: &I64, right: &I64): bool {
        compare(left, right) == GREATER_THAN
    }

    /// Less or equal than
    public fun lte(left: &I64, right: &I64): bool {
        compare(left, right) != GREATER_THAN
    }

    /// Greater or equal than
    public fun gte(left: &I64, right: &I64): bool {
        compare(left, right) != LESS_THAN
    }

    /// Equal than
    public fun eq(left: &I64, right: &I64): bool {
        left.bits == right.bits
    }
}
