use std::fmt::Debug;
use chumsky::{
    input::Input,
    extra::ParserExtra,
    Parser,
};
use chumsky::extension::v1::{Ext, ExtParser};

mod combinator;

use combinator::*;

pub trait DebugParser<'a, I, O, E>: Parser<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    fn debug_offset(self) -> Ext<DebugOffset<Self>>
    where
        Self: Sized,
        I::Offset: Debug,
    {
        Ext(DebugOffset {
            inner: self,
        })
    }
}
