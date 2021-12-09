//! Binary-file specific parsers and utilities.

use super::*;

use std::mem;
use std::convert::TryInto;

mod sealed {
    pub trait Sealed {}

    impl Sealed for u8 {}
    impl Sealed for u16 {}
    impl Sealed for u32 {}
    impl Sealed for u64 {}
    impl Sealed for u128 {}
    impl Sealed for usize {}

    impl Sealed for i8 {}
    impl Sealed for i16 {}
    impl Sealed for i32 {}
    impl Sealed for i64 {}
    impl Sealed for i128 {}
    impl Sealed for isize {}

    impl Sealed for f32 {}
    impl Sealed for f64 {}
}

macro_rules! impl_from_bytes {
    ($($ty:ty),*) => {
        $(
        impl FromBytes for $ty {
            fn from_bytes(bytes: &[u8], endian: Endian) -> Self {
                let bytes = bytes.try_into().unwrap();
                match endian {
                    Endian::Little => Self::from_le_bytes(bytes),
                    Endian::Big => Self::from_be_bytes(bytes),
                }
            }
        }
        )*
    }
}

/// A trait implemented by types that can be converted from bytes
pub trait FromBytes: sealed::Sealed + Sized {
    /// Convert a slice of bytes into this type, using the given endian
    fn from_bytes(bytes: &[u8], endian: Endian) -> Self;
}

impl_from_bytes! {
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, f32, f64
}

/// A trait implemented by integral types
pub trait Integral: sealed::Sealed + FromBytes + Copy {}

impl Integral for u8 {}
impl Integral for u16 {}
impl Integral for u32 {}
impl Integral for u64 {}
impl Integral for u128 {}
impl Integral for usize {}

impl Integral for i8 {}
impl Integral for i16 {}
impl Integral for i32 {}
impl Integral for i64 {}
impl Integral for i128 {}
impl Integral for isize {}

/// A trait implemented by floating-point types
///
/// Avoid implementing this trait yourself if you can: it's *very* likely to be expanded in future versions!
pub trait Float: sealed::Sealed + FromBytes + Copy {}

impl Float for f32 {}
impl Float for f64 {}

/// The endianness of a value, the 'direction' in which bytes are read to interpret the value
#[derive(Copy, Clone, Debug)]
pub enum Endian {
    /// Big endian reading order
    Big,
    /// Little endian reading order
    Little,
}

/// A parser that reads an integral type.
///
/// The output of this parser is `I`, the read integer
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
///
/// let be_u16 = binary::int::<u16, Simple<u8>>(Endian::Big);
/// let le_u16 = binary::int::<u16, Simple<u8>>(Endian::Little);
///
/// assert_eq!(be_u16.parse(b"\x01\x02"), Ok(258));
/// assert_eq!(be_u16.parse(b"\xFF\xFF"), Ok(u16::MAX));
///
/// assert_eq!(le_u16.parser(b"\x01\x02"), Ok(513));
/// assert_eq!(le_u16.parser(b"\xFF\xFF"), Ok(u16::MAX));
///
/// ```
pub fn int<I: Integral, E: Error<u8>>(endian: Endian) -> impl Parser<u8, I, Error = E> + Copy + Clone {
    any()
        .repeated()
        .exactly(mem::size_of::<I>())
        .map(move |bytes| I::from_bytes(&bytes, endian))
}

/// A parser that reads a floating-point type.
///
/// The output of this parser is `F`, the read float
///
/// # Examples
/// ```
/// # use chumsky::prelude::*;
///
/// let be_f32 = binary::float::<f32, Simple<u8>>(Endian::Big);
/// let le_u16 = binary::float::<f32, Simple<u8>>(Endian::Little);
///
/// assert_eq!(be_f32.parse((1.0).to_be_bytes()), Ok(1.));
/// assert_eq!(be_f32.parse((-1.0).to_be_bytes()), Ok(-1.));
///
/// assert_eq!(le_f32.parser((1.0).to_le_bytes()), Ok(1.));
/// assert_eq!(le_f32.parser((-1.0).to_le_bytes()), Ok(-1.));
/// ```
pub fn float<F: Float, E: Error<u8>>(endian: Endian) -> impl Parser<u8, F, Error = E> + Copy + Clone {
    any()
        .repeated()
        .exactly(mem::size_of::<F>())
        .map(move |bytes| F::from_bytes(&bytes, endian))
}
