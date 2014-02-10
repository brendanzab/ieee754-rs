// Copyright 2013 The ieee754-rs Developers. For a full listing of the authors,
// refer to the AUTHORS file at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::cast;
use std::fmt;
use std::num;

use FloatNaN;
use BinaryInterchange;

#[deriving(Clone, Eq)]
pub struct SoftF32 {
    priv data: u32,
}

pub static MAX_BIASED_EXP: u32 = 0xFF;

pub static SIG_MASK: u32 = 0b10000000000000000000000000000000;
pub static EXP_MASK: u32 = 0b01111111100000000000000000000000;
pub static MAN_MASK: u32 = 0b00000000011111111111111111111111;

impl SoftF32 {
    pub fn new(bits: u32) -> SoftF32 {
        return SoftF32 { data: bits };
    }

    pub fn nan() -> SoftF32 {
        return SoftF32 { data: 0xFFC00000 };
    }

    pub fn pack(sign: bool, exp: u32, man: u32) -> SoftF32 {
        let s = if sign { 0 } else { SIG_MASK };

        return SoftF32::new(s + (exp << 23) + man);
    }

    pub fn round_and_pack(sign: bool, exponent: int, mantissa: u32) -> SoftF32 {
        let round_increment = 0x40;
        // TODO: Handle other modes than round-to-even;
        let mut exp = exponent;
        let mut man = mantissa;

        if exp >= 0xFD {
            if (exp > 0xFD) || ((exp == 0xFD) && ((man + round_increment).leading_zeros() == 0)) {
                // TODO: Raise overflow, inexact
                if (round_increment == 0) {
                    return SoftF32::pack(sign, MAX_BIASED_EXP - 1, MAN_MASK);
                } else {
                    return SoftF32::pack(sign, MAX_BIASED_EXP, 0);
                }
            }
        } else if exp < 0 {
            man = shift_right_jamming(man, (-exp) as u32);
            exp = 0;

            // TODO: Possibly raise underflow
        }

        let round_bits = man & 0x7F;

        // TODO: Possibly raise inexact

        man = (man + round_increment) >> 7;

        man = man & !((if (round_bits ^ 0x40) == 0 { 1 } else { 0 }) & 1);

        if man == 0 {
            return SoftF32::pack(sign, 0, 0);
        } else {
            return SoftF32::pack(sign, exp as u32, man);
        }
    }

    pub fn normalize_round_and_pack(sign: bool, exponent: int, mantissa: u32) -> SoftF32 {
        let shift_count = (mantissa.leading_zeros() - 1) as int;

        if (shift_count > 31) {
            return SoftF32::round_and_pack(sign, exponent - shift_count, 0);
        } else {
            return SoftF32::round_and_pack(sign, exponent - shift_count, mantissa << shift_count);
        }
    }

    pub fn from_f32(x: f32) -> SoftF32 {
        SoftF32::new(unsafe { cast::transmute(x) })
    }

    pub fn to_f32(self) -> f32 {
        unsafe { cast::transmute(self) }
    }

    pub fn class(&self) -> ::FloatClass {
        match (
            self.data & MAN_MASK,
            self.data & EXP_MASK,
        ) {
            (0, 0)        => ::FloatZero,
            (_, 0)        => ::FloatSubnormal,
            (0, EXP_MASK) => ::FloatInfinite,
            (_, EXP_MASK) => ::FloatNaN,
            _             => ::FloatNormal,
        }
    }
}

impl BinaryInterchange<u32> for SoftF32 {
    fn binary(&self) -> u32 {
        return self.data;
    }

    fn sign(&self) -> bool {
        return (self.binary() & SIG_MASK) == 0;
    }

    fn exponent(&self) -> u32 {
        return self.biased_exponent() - 127;
    }

    fn biased_exponent(&self) -> u32 {
        return (self.binary() & EXP_MASK) >> 23;
    }

    fn significand(&self) -> u32 {
        if (self.biased_exponent() == 0) {
            return self.significand_field();
        } else {
            return 0b0000000100000000000000000000000 | self.significand_field();
        }
    }

    fn significand_field(&self) -> u32 {
        return self.binary() & MAN_MASK;
    }
}

fn shift_right_jamming<T: num::ToPrimitive>(a: T, count: T) -> u32 {
    let v: u64 = a.to_u64().unwrap();
    let c: u64 = count.to_u64().unwrap();

    if (c > 63) {
        return if v == 0 { 0 } else { 1 };
    } else {
        return ((v >> c) as u32) | (if v.trailing_zeros() < c { 1 } else { 0 });
    }
}

fn propagate_nan(a: &SoftF32, b: &SoftF32) -> SoftF32 {
    let a_is_nan = a.class() == FloatNaN;

    // TODO: Check signalling

    return if (a_is_nan) { a.clone() } else { b.clone() };
}

fn normalize_subnormal(a_man: u32) -> (int, u32) {
    let sc = a_man.leading_zeros() - 8;

    return (1 - (sc as int), a_man << sc);
}

fn add_float(a: &SoftF32, b: &SoftF32, sign: bool) -> SoftF32 {
    let (a_exp, b_exp) = (a.biased_exponent(), b.biased_exponent());
    let (a_man, b_man) = (a.significand() << 6, b.significand() << 6);

    let exp_diff = (a_exp as int) - (b_exp as int);

    if a_exp == MAX_BIASED_EXP {
        if (a_man != 0) || ((b_exp == MAX_BIASED_EXP) && (b_man != 0)) {
            return propagate_nan(a, b);
        } else {
            return a.clone();
        }
    }

    let (z_exp, z_man) = if exp_diff == 0 {
        if a_exp == 0 {
            return SoftF32::pack(sign, 0, (a_man + b_man) >> 6);
        } else {
            (a_exp as int, a_man + b_man)
        }
    } else {
        (a_exp as int, a_man + shift_right_jamming(b_man, exp_diff as u32 - if b_exp == 0 { 1 } else { 0 }))
    };

    if (z_man << 1).leading_zeros() == 0 {
        return SoftF32::round_and_pack(sign, z_exp, z_man);
    } else {
        return SoftF32::round_and_pack(sign, z_exp - 1, z_man << 1);
    }
}

fn sub_float(a: &SoftF32, b: &SoftF32, sign: bool) -> SoftF32 {
    let (a_man, b_man) = (a.significand() << 7, b.significand() << 7);
    let (a_exp, b_exp) = (a.biased_exponent(), b.biased_exponent());

    let exp_diff = (a_exp as int) - (b_exp as int);

    // TODO: Raise flags?
    if a_exp == MAX_BIASED_EXP {
        return if (a_man != 0) || ((b_exp == MAX_BIASED_EXP) && b_man != 0) {
            propagate_nan(a, b)
        } else {
            a.clone()
        };
    }

    let (z_man, z_exp, z_sign) = if exp_diff > 0 {
        (a_man - shift_right_jamming(b_man, exp_diff as u32 - if b_exp == 0 { 1 } else { 0 }), a_exp, sign)
    } else {
        if a_man > b_man {
            (a_man - b_man, if a_exp == 0 { 1 } else { a_exp }, sign)
        } else {
            return SoftF32::pack(true, 0, 0);
        }
    };

    return SoftF32::normalize_round_and_pack(z_sign, z_exp as int - 1, z_man);
}

impl Neg<SoftF32> for SoftF32 {
    fn neg(&self) -> SoftF32 {
        return SoftF32::new(self.data ^ SIG_MASK)
    }
}

impl Add<SoftF32, SoftF32> for SoftF32 {
    fn add(&self, other: &SoftF32) -> SoftF32 {
        let a_abs = self.binary() & (EXP_MASK | MAN_MASK);
        let b_abs = other.binary() & (EXP_MASK | MAN_MASK);

        let swap = (a_abs < b_abs);

        let (a, b) = if swap { (other, self) } else { (self, other) };

        if (self.sign() == other.sign()) {
            return add_float(a, b, self.sign())
        } else {
            return sub_float(a, b, self.sign() ^ swap)
        }
    }
}

impl Sub<SoftF32, SoftF32> for SoftF32 {
    fn sub(&self, other: &SoftF32) -> SoftF32 {
        let a_abs = self.binary() & (EXP_MASK | MAN_MASK);
        let b_abs = other.binary() & (EXP_MASK | MAN_MASK);

        let swap = (a_abs < b_abs);

        let (a, b) = if swap { (other, self) } else { (self, other) };

        if (self.sign() == other.sign()) {
            return sub_float(a, b, self.sign() ^ swap);
        } else {
            return add_float(a, b, self.sign());
        }
    }
}

impl Mul<SoftF32, SoftF32> for SoftF32 {
    fn mul(&self, other: &SoftF32) -> SoftF32 {
        let (a_exp, b_exp) = (self.biased_exponent(), other.biased_exponent());
        let (a_man, b_man) = (self.significand(), other.significand());

        let z_sign = !(self.sign() ^ other.sign());

        if (a_exp == MAX_BIASED_EXP || b_exp == MAX_BIASED_EXP) {
            if ((a_exp == MAX_BIASED_EXP) && (a_man != 0)) || ((b_exp == MAX_BIASED_EXP) && (b_man != 0)) {
                return propagate_nan(self, other);
            } else if ((a_man == 0) && (a_exp == 0)) || ((b_man == 0) && (b_exp == 0)) {
                // TODO: Raise invalid flag
                return SoftF32::nan();
            } else {
                return SoftF32::pack(z_sign, MAX_BIASED_EXP, 0);
            }
        }

        let (a_exp, a_man) = if (a_exp == 0) {
            if a_man == 0 {
                return SoftF32::pack(z_sign, 0, 0);
            } else {
                normalize_subnormal(a_man)
            }
        } else {
            (a_exp as int, a_man)
        };

        let (b_exp, b_man) = if (b_exp == 0) {
            if b_man == 0 {
                return SoftF32::pack(z_sign, 0, 0);
            } else {
                normalize_subnormal(b_man)
            }
        } else {
            (b_exp as int, b_man)
        };

        let z_exp = a_exp + b_exp - 0x7F;
        let z_man = shift_right_jamming(((a_man << 7)as u64) * ((b_man << 8) as u64), 32);

        if (z_man << 1).leading_zeros() != 0 {
            return SoftF32::round_and_pack(z_sign, (z_exp - 1), z_man << 1);
        } else {
            return SoftF32::round_and_pack(z_sign, z_exp, z_man);
        }
    }
}

impl fmt::Default for SoftF32 {
    fn fmt(x: &SoftF32, f: &mut fmt::Formatter) {
        fmt::Default::fmt(&x.to_f32(), f)
    }
}

impl fmt::Float for SoftF32 {
    fn fmt(x: &SoftF32, f: &mut fmt::Formatter) {
        fmt::Float::fmt(&x.to_f32(), f)
    }
}

impl fmt::Binary for SoftF32 {
    fn fmt(x: &SoftF32, f: &mut fmt::Formatter) {
        fmt::Binary::fmt(&x.data, f)
    }
}

#[cfg(test)]
mod tests {
    use std;
    use {FloatZero, FloatSubnormal, FloatInfinite, FloatNaN, FloatNormal};

    use BinaryInterchange;
    use soft_f32::SoftF32;

    use std::rand::Rng;
    use std::rand::SeedableRng;

    macro_rules! test_add(($a:expr, $b:expr, $r:expr) => ({
        let (a, b, r) = (SoftF32::new($a), SoftF32::new($b), SoftF32::new($r));

        let sum = a + b;

        assert_eq!(sum.class(), r.class());

        if (r.class() != FloatNaN) {
            // println!("h: {:?} exp: {:?} sig: {:t}", r.sign(), r.biased_exponent(), r.significand_field());
            // println!("s: {:?} exp: {:?} sig: {:t}", sum.sign(), sum.biased_exponent(), sum.significand_field());

            assert_eq!(sum.sign(), r.sign());
            assert_eq!(sum.biased_exponent(), r.biased_exponent());
            assert_eq!(sum.significand_field(), r.significand_field());
            assert_eq!(sum.binary(), r.binary());
        }
    }))

    macro_rules! test_sub(($a:expr, $b:expr, $r:expr) => ({
        let (a, b, r) = (SoftF32::new($a), SoftF32::new($b), SoftF32::new($r));

        let sum = a - b;

        assert_eq!(sum.class(), r.class());

        if (r.class() != FloatNaN) {
            // println!("h: {:?} exp: {:?} sig: {:t}", r.sign(), r.biased_exponent(), r.significand_field());
            // println!("s: {:?} exp: {:?} sig: {:t}", sum.sign(), sum.biased_exponent(), sum.significand_field());

            assert_eq!(sum.sign(), r.sign());
            assert_eq!(sum.biased_exponent(), r.biased_exponent());
            assert_eq!(sum.significand_field(), r.significand_field());
            assert_eq!(sum.binary(), r.binary());
        }
    }))

    macro_rules! test_mul(($a:expr, $b:expr, $r:expr) => ({
        let (a, b, r) = (SoftF32::new($a), SoftF32::new($b), SoftF32::new($r));

        let sum = a * b;

        assert_eq!(sum.class(), r.class());

        if (r.class() != FloatNaN) {
            // println!("h: {:?} exp: {:?} sig: {:t}", r.sign(), r.biased_exponent(), r.significand_field());
            // println!("s: {:?} exp: {:?} sig: {:t}", sum.sign(), sum.biased_exponent(), sum.significand_field());

            assert_eq!(sum.sign(), r.sign());
            assert_eq!(sum.biased_exponent(), r.biased_exponent());
            assert_eq!(sum.significand_field(), r.significand_field());
            assert_eq!(sum.binary(), r.binary());
        }
    }))

    #[test]
    fn test_specific_add() {
        test_add!(   8388750u32,   25174430u32,   27271618u32);
        test_add!(  12749327u32,    5166936u32,   17346740u32);
        test_add!( 297867913u32,  574824446u32,  574824446u32);
        test_add!(  44180447u32, 2434822861u32, 2434822861u32);
        test_add!(  10160343u32, 4279686483u32, 4279686483u32);
        test_add!(3065323245u32,  914535169u32, 3049893808u32);
        test_add!( 430114522u32,  428316865u32,  437604302u32);
        test_add!(  13624552u32, 2153752233u32,    7355967u32);
    }

    #[test]
    fn test_specific_sub() {
        test_sub!( 126869781u32, 3102201224u32,  954717576u32);
        test_sub!( 126869781u32, 3102201224u32,  954717576u32);
    }

    #[test]
    fn test_specific_mul() {
        test_mul!(     18509u32,       6167u32,          0u32);
        test_mul!(2445515395u32, 2958138854u32,   44050890u32);
    }

    #[test]
    fn test_random_add() {
        let mut rng: std::rand::XorShiftRng = SeedableRng::from_seed([1, 2, 3, 4]);

        for _ in std::iter::range(0, 100000000) {
            let a = SoftF32::new(rng.next_u32());
            let b = SoftF32::new(rng.next_u32());

            let software = a + b;
            let hardware = SoftF32::from_f32(a.to_f32() + b.to_f32());

            if (hardware.class() != FloatNaN) {
                assert_eq!((a.binary(), b.binary(), software.binary()), (a.binary(), b.binary(), hardware.binary()));
            } else {
                assert_eq!(software.class(), hardware.class());
            }
        }
    }

    #[test]
    fn test_random_sub() {
        let mut rng: std::rand::XorShiftRng = SeedableRng::from_seed([5, 6, 7, 8]);

        for _ in std::iter::range(0, 100000000) {
            let a = SoftF32::new(rng.next_u32());
            let b = SoftF32::new(rng.next_u32());

            let software = a - b;
            let hardware = SoftF32::from_f32(a.to_f32() - b.to_f32());

            if (hardware.class() != FloatNaN) {
                assert_eq!((a.binary(), b.binary(), software.binary()), (a.binary(), b.binary(), hardware.binary()));
            } else {
                assert_eq!(software.class(), hardware.class());
            }
        }
    }

    #[test]
    fn test_random_mul() {
        let mut rng: std::rand::XorShiftRng = SeedableRng::from_seed([9, 10, 11, 12]);

        for _ in std::iter::range(0, 100000000) {
            let a = SoftF32::new(rng.next_u32());
            let b = SoftF32::new(rng.next_u32());

            let software = a * b;
            let hardware = SoftF32::from_f32(a.to_f32() * b.to_f32());

            if (hardware.class() != FloatNaN) {
                assert_eq!((a.binary(), b.binary(), software.binary()), (a.binary(), b.binary(), hardware.binary()));
            } else {
                assert_eq!(software.class(), hardware.class());
            }
        }
    }
}