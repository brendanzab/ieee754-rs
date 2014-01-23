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

#[deriving(Clone, Eq)]
pub struct F32 {
    priv data: u32,
}

pub fn F32(x: f32) -> F32 {
    F32::new(unsafe { cast::transmute(x) })
}

pub static SIG_MASK: u32 = 0b10000000000000000000000000000000;
pub static EXP_MASK: u32 = 0b01111111100000000000000000000000;
pub static MAN_MASK: u32 = 0b00000000011111111111111111111111;

impl F32 {
    pub fn new(bits: u32) -> F32 {
        F32 { data: bits }
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

    pub fn is_sign_minus(self) -> bool {
        (self.data & SIG_MASK) == SIG_MASK
    }

    pub fn abs(self) -> F32 {
        F32::new(self.data & !SIG_MASK)
    }

    pub fn copy_sign(self, sign_src: F32) -> F32 {
        F32::new(self.data | sign_src.data & SIG_MASK)
    }
}

impl Neg<F32> for F32 {
    fn neg(&self) -> F32 {
        F32::new(self.data ^ SIG_MASK)
    }
}

impl fmt::Default for F32 {
    fn fmt(x: &F32, f: &mut fmt::Formatter) {
        fmt::Default::fmt(&x.to_f32(), f)
    }
}

impl fmt::Float for F32 {
    fn fmt(x: &F32, f: &mut fmt::Formatter) {
        fmt::Float::fmt(&x.to_f32(), f)
    }
}

impl fmt::Binary for F32 {
    fn fmt(x: &F32, f: &mut fmt::Formatter) {
        fmt::Binary::fmt(&x.data, f)
    }
}
