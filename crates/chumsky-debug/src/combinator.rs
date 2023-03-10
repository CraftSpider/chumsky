use chumsky::input::InputRef;
use super::*;

pub struct DebugOffset<'a, A> {
    pub(crate) parser: A,
}

impl<'a, A, I, O, E> ExtParser<'a, I, O, E> for DebugOffset<'a, A>
where
    A: Parser<'a, I, O, E>,
    I: Input<'a>,
    I::Offset: Debug,
    E: ParserExtra<'a, I>,
{
    fn parse(&self, inp: &mut InputRef<'a, '_, I, E>) -> Result<O, E::Error> {
        println!("Starting Offset: {:?}", inp.offset());
        match inp.parse(&self.parser) {
            Ok(out) => {
                println!("Final Offset: {:?}", inp.offset());
                Ok(out)
            }
            Err(e) => {
                println!("Error Occurred");
                Err(e)
            }
        }
    }
}

pub struct DebugOut<A> {
    pub(crate) parser: A,
}

impl<'a, A, I, O, E> ExtParser<'a, I, O, E> for DebugOut<A>
where
    A: Parser<'a, I, O, E>,
    I: Input<'a>,
    O: Debug,
    E: ParserExtra<'a, I>,
{
    fn parse(&self, inp: &mut InputRef<'a, '_, I, E>) -> Result<O, E::Error> {
        match inp.parse(&self.parser) {
            Ok(out) => {
                println!("Parser Output: {:?}", out);
                Ok(out)
            }
            Err(e) => Err(e),
        }
    }
}

pub struct DebugSpan<A> {
    pub(crate) parser: A,
}

impl<'a, A, I, O, E> ExtParser<'a, I, O, E> for DebugSpan<A>
where
    A: Parser<'a, I, O, E>,
    I: Input<'a>,
    I::Span: Debug,
    E: ParserExtra<'a, I>,
{
    fn parse(&self, inp: &mut InputRef<'a, '_, I, E>) -> Result<O, E::Error> {
        let before = inp.offset();
        match inp.parse(&self.parser) {
            Ok(out) => {
                println!("Consumed Span: {:?}", inp.span_since(before));
                Ok(out)
            },
            Err(e) => Err(e),
        }
    }
}
