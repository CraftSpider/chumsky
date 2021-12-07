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
}

/// A trait implemented by integral types
///
/// Avoid implementing this trait yourself if you can: it's *very* likely to be expanded in future versions!
pub trait Integral: sealed::Sealed + Sized + Copy {
    /// Convert a slice of bytes into this type, using the given endian
    fn from_bytes(bytes: &[u8], endian: Endian) -> Self;
}

impl Integral for u8 {
    fn from_bytes(bytes: &[u8], endian: Endian) -> u8 {
        let bytes = bytes.try_into().unwrap();
        match endian {
            Endian::Little => u8::from_le_bytes(bytes),
            Endian::Big => u8::from_be_bytes(bytes),
        }
    }
}

impl Integral for u16 {
    fn from_bytes(bytes: &[u8], endian: Endian) -> Self {
        let bytes = bytes.try_into().unwrap();
        match endian {
            Endian::Little => u16::from_le_bytes(bytes),
            Endian::Big => u16::from_be_bytes(bytes),
        }
    }
}

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
