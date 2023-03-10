use chumsky::input::InputRef;
use super::*;

pub struct DebugOffset<A> {
    pub(crate) inner: A,
}

impl<'a, A, I, O, E> ExtParser<'a, I, O, E> for DebugOffset<A>
where
    A: Parser<'a, I, O, E>,
    I: Input<'a>,
    I::Offset: Debug,
    E: ParserExtra<'a, I>,
{
    fn parse(&self, inp: &mut InputRef<'a, '_, I, E>) -> Result<O, E::Error> {
        dbg!(inp.offset());
        match inp.parse(&self.inner) {
            Ok(out) => {
                dbg!(inp.offset());
                Ok(out)
            }
            Err(e) => {
                println!("Error Occurred");
                Err(e)
            }
        }
    }
}
