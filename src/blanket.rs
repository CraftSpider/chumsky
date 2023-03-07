use super::*;

impl<'a, 'b, T, I, E> Parser<'a, I, E> for &'b T
where
    T: Parser<'a, I, E>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type Output = T::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output>
    where
        Self: Sized,
    {
        (*self).go::<M>(inp)
    }

    go_extra!();
}

impl<'a, 'b, T, I, E> ConfigParser<'a, I, E> for &'b T
where
    T: ConfigParser<'a, I, E>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type Config = T::Config;

    fn go_cfg<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>, cfg: Self::Config) -> PResult<M, Self::Output>
    where
        Self: Sized,
    {
        (*self).go_cfg::<M>(inp, cfg)
    }

    go_cfg_extra!();
}
