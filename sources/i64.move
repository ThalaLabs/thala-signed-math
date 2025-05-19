/// @title i64
/// @notice Signed 64-bit integers in Move.
/// from: https://github.com/ThalaLabs/movemate/blob/main/aptos/sources/i64.move
module thala_signed_math::i64 {
    use std::error;

    /// @dev Maximum I64 value as a u64.
    const MAX_I64_AS_U64: u64 = (1 << 63) - 1;

    /// @dev Maximum U64 value (2^64 - 1), used as the basis of overflow checks
    const MAX_U64: u64 = 18446744073709551615;

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

    /// @dev When trying to add a u64 to an I64 that would overflow.
    const SIGNED_MATH_ADD_OVERFLOW: u64 = 2;

    /// @dev When trying to subtract a u64 from an I64 that would underflow.
    const SIGNED_MATH_SUB_UNDERFLOW: u64 = 3;

    /// @dev When trying to multiply a u64 by an I64 that would overflow.
    const SIGNED_MATH_MUL_OVERFLOW: u64 = 4;

    /// @dev When trying to divide by zero.
    const SIGNED_MATH_DIVIDE_BY_ZERO: u64 = 5;


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

    /// @notice Normalize `x such that "-0" and "0" are both represented by "0".
    fun normalize(x: I64): I64 {
        if (x.bits == U64_WITH_FIRST_BIT_SET) I64 { bits: 0 } else x
    }

    /// @notice Flips the sign of `x`.
    public fun neg(x: &I64): I64 {
        if (x.bits == 0) return *x;
        normalize(I64 { bits: if (x.bits < U64_WITH_FIRST_BIT_SET) x.bits | (1 << 63) else x.bits - (1 << 63) })
    }

    /// @notice Flips the sign of `x`.
    public fun neg_from_u64(x: u64): I64 {
        let ret = from_u64(x);
        if (ret.bits > 0) *&mut ret.bits = ret.bits | (1 << 63);
        normalize(ret)
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
            assert!(a.bits <= MAX_I64_AS_U64 - b, SIGNED_MATH_ADD_OVERFLOW);
            return normalize(I64 { bits: a.bits + b })
        } else {
            // A is negative
            let a_abs = a.bits - (1 << 63);
            if (a_abs <= b) {
                // Result becomes positive
                let diff = b - a_abs;
                assert!(diff <= MAX_I64_AS_U64, SIGNED_MATH_ADD_OVERFLOW);
                return normalize(I64 { bits: diff });
            };
            return normalize(I64 { bits: a.bits - b }) // Return negative
        }
    }

    /// @notice Subtract `a - b`.
    public fun sub(a: &I64, b: u64): I64 {
        if (a.bits >> 63 == 0) {
            // A is positive
            if (a.bits >= b) return I64 { bits: a.bits - b }; // Return positive
            let diff = b - a.bits;
            assert!(diff <= MAX_I64_AS_U64, SIGNED_MATH_SUB_UNDERFLOW);
            return normalize(I64 { bits: (1 << 63) | diff })
        } else {
            // A is negative
            assert!(b <= MAX_U64 - a.bits, SIGNED_MATH_SUB_UNDERFLOW);
            return normalize(I64 { bits: a.bits + b }) // Return negative
        }
    }

    /// @notice Multiply `a * b`.
    public fun mul(a: &I64, b: u64): I64 {
        let is_neg = a.bits >> 63 == 1;
        let a_abs = if (is_neg) a.bits - (1 << 63) else a.bits;

        assert!(
            a_abs == 0 || b <= MAX_I64_AS_U64 / a_abs,
            SIGNED_MATH_MUL_OVERFLOW
        );

        if (!is_neg) {
            // A is positive
            return normalize(I64 { bits: a.bits * b }) // Return positive
        } else {
            // A is negative
            return normalize(I64 { bits: (1 << 63) | (b * a_abs) }) // Return negative
        }
    }

    /// @notice Divide `a / b`.
    public fun div(a: &I64, b: u64): I64 {
        assert!(b != 0, SIGNED_MATH_DIVIDE_BY_ZERO);
        if (a.bits >> 63 == 0) {
            // A is positive
            return normalize(I64 { bits: a.bits / b }) // Return positive
        } else {
            // A is negative
            return normalize(I64 { bits: (1 << 63) | ((a.bits - (1 << 63)) / b) }) // Return negative
        }
    }

    /// @notice Add `a + b`.
    public fun add_i64(a: &I64, b: &I64): I64 {
        if (a.bits >> 63 == 0) {
            // A is positive
            if (b.bits >> 63 == 0) {
                // B is positive
                assert!(a.bits <= MAX_I64_AS_U64 - b.bits, SIGNED_MATH_ADD_OVERFLOW);
                return normalize(I64 { bits: a.bits + b.bits })
            } else {
                // B is negative
                if (b.bits - (1 << 63) <= a.bits) return I64 { bits: a.bits - (b.bits - (1 << 63)) }; // Return positive
                return normalize(I64 { bits: b.bits - a.bits }) // Return negative
            }
        } else {
            // A is negative
            if (b.bits >> 63 == 0) {
                // B is positive
                if (a.bits - (1 << 63) <= b.bits) return I64 { bits: b.bits - (a.bits - (1 << 63)) }; // Return positive
                return normalize(I64 { bits: a.bits - b.bits }) // Return negative
            } else {
                // B is negative
                assert!(a.bits - (1 << 63) <= MAX_I64_AS_U64 - (b.bits - (1 << 63)), SIGNED_MATH_SUB_UNDERFLOW);
                return normalize(I64 { bits: a.bits + (b.bits - (1 << 63)) })
            }
        }
    }

    /// @notice Subtract `a - b`.
    public fun sub_i64(a: &I64, b: &I64): I64 {
        if (a.bits >> 63 == 0) {
            // A is positive
            if (b.bits >> 63 == 0) {
                // B is positive
                if (a.bits >= b.bits) return normalize(I64 { bits: a.bits - b.bits }); // Return positive
                return normalize(I64 { bits: (1 << 63) | (b.bits - a.bits) }) // Return negative
            } else {
                // B is negative
                assert!(a.bits <= MAX_I64_AS_U64 - (b.bits - (1 << 63)), SIGNED_MATH_ADD_OVERFLOW);
                return normalize(I64 { bits: a.bits + (b.bits - (1 << 63)) }) // Return negative
            }
        } else {
            // A is negative
            if (b.bits >> 63 == 0) {
                // B is positive
                assert!(b.bits <= MAX_I64_AS_U64 - (a.bits - (1 << 63)), SIGNED_MATH_SUB_UNDERFLOW);
                return normalize(I64 { bits: a.bits + b.bits }) // Return negative
            } else {
                // B is negative
                if (b.bits >= a.bits) return normalize(I64 { bits: b.bits - a.bits }); // Return positive
                return normalize(I64 { bits: a.bits - (b.bits - (1 << 63)) }) // Return negative
            }
        }
    }

    /// @notice Multiply `a * b`.
    public fun mul_i64(a: &I64, b: &I64): I64 {
        let a_neg = a.bits >> 63 == 1;
        let b_neg = b.bits >> 63 == 1;

        let a_abs = if (a_neg) a.bits - (1 << 63) else a.bits;
        let b_abs = if (b_neg) b.bits - (1 << 63) else b.bits;

        // Prevent overflow: a_abs * b_abs must fit in MAX_I64_AS_U64
        assert!(
            a_abs == 0 || b_abs <= MAX_I64_AS_U64 / a_abs,
            SIGNED_MATH_MUL_OVERFLOW
        );

        if (a.bits >> 63 == 0) {
            // A is positive
            if (b.bits >> 63 == 0) {
                // B is positive
                return normalize(I64 { bits: a.bits * b.bits }) // Return positive
            } else {
                // B is negative
                return normalize(I64 { bits: (1 << 63) | (a.bits * (b.bits - (1 << 63))) }) // Return negative
            }
        } else {
            // A is negative
            if (b.bits >> 63 == 0) {
                // B is positive
                return normalize(I64 { bits: (1 << 63) | (b.bits * (a.bits - (1 << 63))) }) // Return negative
            } else {
                // B is negative
                return normalize(I64 { bits: (a.bits - (1 << 63)) * (b.bits - (1 << 63)) }) // Return positive
            }
        }
    }

    /// @notice Divide `a / b`.
    public fun div_i64(a: &I64, b: &I64): I64 {
        assert!(compare(b, &from_u64(0)) != EQUAL, SIGNED_MATH_DIVIDE_BY_ZERO);

        if (a.bits >> 63 == 0) {
            // A is positive
            if (b.bits >> 63 == 0) {
                // B is positive
                return normalize(I64 { bits: a.bits / b.bits }) // Return positive
            } else {
                // B is negative
                return normalize(I64 { bits: (1 << 63) | (a.bits / (b.bits - (1 << 63))) }) // Return negative
            }
        } else {
            // A is negative
            if (b.bits >> 63 == 0) {
                // B is positive
                return normalize(I64 { bits: (1 << 63) | ((a.bits - (1 << 63)) / b.bits) }) // Return negative
            } else {
                // B is negative
                return normalize(I64 { bits: (a.bits - (1 << 63)) / (b.bits - (1 << 63)) }) // Return positive
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
        assert!(compare(&neg_from_u64(0), &zero()) == EQUAL, 0); // compare "normalized" values
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

        assert!(add(&zero(), 0) == zero(), 0);
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_ADD_OVERFLOW)]
    fun test_add_overflow_from_positive() {
        add(&from_u64(2), MAX_I64_AS_U64 - 1);
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_ADD_OVERFLOW)]
    fun test_add_overflow_from_negative() {
        add(&neg_from_u64(2), MAX_I64_AS_U64 + 3);
    }

    #[test]
    fun test_sub() {
        assert!(sub(&from_u64(123), 234) == neg_from_u64(111), 0);
        assert!(sub(&from_u64(234), 123) == from_u64(111), 0);
        assert!(sub(&neg_from_u64(123), 234) == neg_from_u64(357), 0);

        assert!(sub(&from_u64(123), 123) == zero(), 0);

        assert!(sub(&zero(), 0) == zero(), 0);
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_SUB_UNDERFLOW)]
    fun test_sub_underflow_from_positive() {
        sub(&from_u64(2), MAX_I64_AS_U64 + 3);
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_SUB_UNDERFLOW)]
    fun test_sub_underflow_from_negative() {
        sub(&neg_from_u64(2), MAX_I64_AS_U64 - 1);
    }

    #[test]
    fun test_mul() {
        assert!(mul(&from_u64(123), 234) == from_u64(28782), 0);
        assert!(mul(&neg_from_u64(123), 234) == neg_from_u64(28782), 0);

        assert!(mul(&zero(), 0) == zero(), 0);
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_MUL_OVERFLOW)]
    fun test_mul_overflow_from_positive() {
        mul(&from_u64(2), MAX_I64_AS_U64 - 1);
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_MUL_OVERFLOW)]
    fun test_mul_overflow_from_negative() {
        mul(&neg_from_u64(2), MAX_I64_AS_U64 - 1);
    }

    #[test]
    fun test_div() {
        assert!(div(&from_u64(28781), 123) == from_u64(233), 0);
        assert!(div(&neg_from_u64(28781), 123) == neg_from_u64(233), 0);

        assert!(div(&zero(), 1) == zero(), 0);
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_DIVIDE_BY_ZERO)]
    fun test_div_by_zero() {
        div(&from_u64(1), 0);
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

        assert!(add_i64(&neg_from_u64(0), &from_u64(0)) == zero(), 0);
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_ADD_OVERFLOW)]
    fun test_add_i64_overflow_from_positive() {
        add_i64(&from_u64(2), &from_u64(MAX_I64_AS_U64 - 1));
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_SUB_UNDERFLOW)]
    fun test_add_i64_underflow_from_negative() {
        add_i64(&neg_from_u64(2), &neg_from_u64(MAX_I64_AS_U64 - 1));
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

        assert!(sub_i64(&neg_from_u64(0), &from_u64(0)) == zero(), 0);
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_SUB_UNDERFLOW)]
    fun test_sub_i64_underflow_from_negative() {
        sub_i64(&neg_from_u64(2), &from_u64(MAX_I64_AS_U64 - 1));
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_ADD_OVERFLOW)]
    fun test_sub_i64_overflow_from_negative() {
        sub_i64(&from_u64(2), &neg_from_u64(MAX_I64_AS_U64 - 1));
    }

    #[test]
    fun test_mul_i64() {
        assert!(mul_i64(&from_u64(123), &from_u64(234)) == from_u64(28782), 0);
        assert!(mul_i64(&from_u64(123), &neg_from_u64(234)) == neg_from_u64(28782), 0);
        assert!(mul_i64(&neg_from_u64(123), &from_u64(234)) == neg_from_u64(28782), 0);
        assert!(mul_i64(&neg_from_u64(123), &neg_from_u64(234)) == from_u64(28782), 0);

        assert!(mul_i64(&neg_from_u64(0), &from_u64(0)) == zero(), 0);
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_MUL_OVERFLOW)]
    fun test_mul_i64_overflow_from_positive() {
        mul_i64(&from_u64(2), &from_u64(MAX_I64_AS_U64 - 1));
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_MUL_OVERFLOW)]
    fun test_mul_i64_overflow_from_negative() {
        mul_i64(&neg_from_u64(2), &neg_from_u64(MAX_I64_AS_U64 - 1));
    }

    #[test]
    fun test_div_i64() {
        assert!(div_i64(&from_u64(28781), &from_u64(123)) == from_u64(233), 0);
        assert!(div_i64(&from_u64(28781), &neg_from_u64(123)) == neg_from_u64(233), 0);
        assert!(div_i64(&neg_from_u64(28781), &from_u64(123)) == neg_from_u64(233), 0);
        assert!(div_i64(&neg_from_u64(28781), &neg_from_u64(123)) == from_u64(233), 0);

        assert!(div_i64(&neg_from_u64(0), &from_u64(1)) == zero(), 0);
    }

    #[test]
    #[expected_failure(abort_code = SIGNED_MATH_DIVIDE_BY_ZERO)]
    fun test_div_i64_by_zero() {
        div_i64(&from_u64(1), &from_u64(0));
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
