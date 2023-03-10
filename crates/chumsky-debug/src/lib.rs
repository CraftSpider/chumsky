use std::fmt::Debug;
use std::io::Write;
use chumsky::{
    input::Input,
    extra::ParserExtra,
    Parser,
};
use chumsky::extension::v1::{Ext, ExtParser};

mod combinator;

use combinator::*;

pub enum Target<'a> {
    Out,
    Err,
    Write(&'a dyn Write),
}

pub trait DebugParser<'a, I, O, E>: Parser<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    fn debug_offset(self) -> Ext<DebugOffset<'a, Self>>
    where
        Self: Sized,
        I::Offset: Debug,
    {
        Ext(DebugOffset {
            parser: self,
        })
    }

    fn debug_out(self) -> Ext<DebugOut<Self>>
    where
        Self: Sized,
        O: Debug,
    {
        Ext(DebugOut {
            parser: self,
        })
    }

    fn debug_span(self) -> Ext<DebugSpan<Self>>
    where
        Self: Sized,
        I::Span: Debug,
    {
        Ext(DebugSpan {
            parser: self,
        })
    }
}
