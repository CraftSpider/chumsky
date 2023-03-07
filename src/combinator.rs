//! Combinators that allow combining and extending existing parsers.
//!
//! *“Ford... you're turning into a penguin. Stop it.”*
//!
//! Although it's *sometimes* useful to be able to name their type, most of these parsers are much easier to work with
//! when accessed through their respective methods on [`Parser`].

use super::*;
use core::mem::MaybeUninit;

/// The type of a lazy parser.
pub type Lazy<'a, A, I, E> =
    ThenIgnore<A, Repeated<Any<I, E>, I, E>, E>;

/// Alter the configuration of a struct using parse-time context
pub struct Configure<A, F> {
    pub(crate) parser: A,
    pub(crate) cfg: F,
}

impl<A: Copy, F: Copy> Copy for Configure<A, F> {}
impl<A: Clone, F: Clone> Clone for Configure<A, F> {
    fn clone(&self) -> Self {
        Configure {
            parser: self.parser.clone(),
            cfg: self.cfg.clone(),
        }
    }
}

impl<'a, I, E, A, F> Parser<'a, I, E> for Configure<A, F>
where
    A: ConfigParser<'a, I, E>,
    F: Fn(A::Config, &E::Context) -> A::Config,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output>
    where
        Self: Sized,
    {
        let cfg = (self.cfg)(A::Config::default(), inp.ctx());
        self.parser.go_cfg::<M>(inp, cfg)
    }

    go_extra!();
}

/// See [`ConfigIterParser::configure`]
pub struct IterConfigure<A, F> {
    pub(crate) parser: A,
    pub(crate) cfg: F,
}

impl<A: Copy, F: Copy> Copy for IterConfigure<A, F> {}
impl<A: Clone, F: Clone> Clone for IterConfigure<A, F> {
    fn clone(&self) -> Self {
        IterConfigure {
            parser: self.parser.clone(),
            cfg: self.cfg.clone(),
        }
    }
}

impl<'a, I, E, A, F> Parser<'a, I, E> for IterConfigure<A, F>
where
    A: ConfigIterParser<'a, I, E>,
    F: Fn(A::Config, &E::Context) -> A::Config,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type Output = ();

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let mut state = self.make_iter::<Check>(inp)?;
        loop {
            match self.next::<Check>(inp, &mut state) {
                Ok(Some(())) => {}
                Ok(None) => break Ok(M::bind(|| ())),
                Err(()) => break Err(()),
            }
        }
    }

    go_extra!();
}

impl<'a, I, E, A, F> IterParser<'a, I, E> for IterConfigure<A, F>
where
    A: ConfigIterParser<'a, I, E>,
    F: Fn(A::Config, &E::Context) -> A::Config,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type Item = A::Item;

    type IterState<M: Mode> = (A::IterState<M>, A::Config)
    where
        I: 'a;

    #[inline]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok((
            A::make_iter(&self.parser, inp)?,
            (self.cfg)(A::Config::default(), inp.ctx()),
        ))
    }

    #[inline]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, Self::Item> {
        self.parser.next_cfg(inp, &mut state.0, &state.1)
    }
}

/// See [`ConfigIterParser::try_configure`]
pub struct TryIterConfigure<A, F> {
    pub(crate) parser: A,
    pub(crate) cfg: F,
}

impl<A: Copy, F: Copy> Copy for TryIterConfigure<A, F> {}
impl<A: Clone, F: Clone> Clone for TryIterConfigure<A, F> {
    fn clone(&self) -> Self {
        TryIterConfigure {
            parser: self.parser.clone(),
            cfg: self.cfg.clone(),
        }
    }
}

impl<'a, I, E, A, F> Parser<'a, I, E> for TryIterConfigure<A, F>
where
    A: ConfigIterParser<'a, I, E>,
    F: Fn(A::Config, &E::Context, I::Span) -> Result<A::Config, E::Error>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type Output = ();

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let mut state = self.make_iter::<Check>(inp)?;
        loop {
            match self.next::<Check>(inp, &mut state) {
                Ok(Some(())) => {}
                Ok(None) => break Ok(M::bind(|| ())),
                Err(()) => break Err(()),
            }
        }
    }

    go_extra!();
}

impl<'a, I, E, A, F> IterParser<'a, I, E> for TryIterConfigure<A, F>
where
    A: ConfigIterParser<'a, I, E>,
    F: Fn(A::Config, &E::Context, I::Span) -> Result<A::Config, E::Error>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type Item = A::Item;

    type IterState<M: Mode> = (A::IterState<M>, A::Config)
    where
        I: 'a;

    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        let cfg = (self.cfg)(A::Config::default(), inp.ctx(), unsafe {
            inp.span_since(inp.offset)
        })
        .map_err(|e| inp.add_alt_err(inp.offset, e))?;

        Ok((A::make_iter(&self.parser, inp)?, cfg))
    }

    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, Self::Item> {
        self.parser.next_cfg(inp, &mut state.0, &state.1)
    }
}

/// See [`Parser::map_slice`].
pub struct MapSlice<'a, A, I, E, F, U>
where
    I: SliceInput<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(I::Slice) -> U,
{
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<(I::Slice, E)>,
}

impl<'a, A: Copy, I, E, F: Copy, U> Copy for MapSlice<'a, A, I, E, F, U>
where
    I: SliceInput<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(I::Slice) -> U,
{
}
impl<'a, A: Clone, I, E, F: Clone, U> Clone for MapSlice<'a, A, I, E, F, U>
where
    I: Input<'a> + SliceInput<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(I::Slice) -> U,
{
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, F, U> Parser<'a, I, E> for MapSlice<'a, A, I, E, F, U>
where
    I: SliceInput<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(I::Slice) -> U,
{
    type Output = U;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, U> {
        let before = inp.offset();
        self.parser.go::<Check>(inp)?;
        let after = inp.offset();

        Ok(M::bind(|| (self.mapper)(inp.slice(before..after))))
    }

    go_extra!();
}

/// See [`Parser::slice`]
pub struct Slice<A> {
    pub(crate) parser: A,
}

impl<A: Copy> Copy for Slice<A> {}
impl<A: Clone> Clone for Slice<A> {
    fn clone(&self) -> Self {
        Slice {
            parser: self.parser.clone(),
        }
    }
}

impl<'a, A, I, E> Parser<'a, I, E> for Slice<A>
where
    A: Parser<'a, I, E>,
    I: SliceInput<'a>,
    E: ParserExtra<'a, I>,
{
    type Output = I::Slice;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, I::Slice>
    where
        Self: Sized,
    {
        let before = inp.offset();
        self.parser.go::<Check>(inp)?;
        let after = inp.offset();

        Ok(M::bind(|| inp.slice(before..after)))
    }

    go_extra!();
}

/// See [`Parser::filter`].
pub struct Filter<A, F> {
    pub(crate) parser: A,
    pub(crate) filter: F,
}

impl<A: Copy, F: Copy> Copy for Filter<A, F> {}
impl<A: Clone, F: Clone> Clone for Filter<A, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            filter: self.filter.clone(),
        }
    }
}

impl<'a, A, I, E, F> Parser<'a, I, E> for Filter<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(&A::Output) -> bool,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let before = inp.offset();
        self.parser.go::<Emit>(inp).and_then(|out| {
            if (self.filter)(&out) {
                Ok(M::bind(|| out))
            } else {
                // SAFETY: Using offsets derived from input
                let err_span = unsafe { inp.span_since(before) };
                inp.add_alt(inp.offset(), None, None, err_span);
                Err(())
            }
        })
    }

    go_extra!();
}

/// See [`Parser::map`].
pub struct Map<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<A: Copy, F: Copy> Copy for Map<A, F> {}
impl<A: Clone, F: Clone> Clone for Map<A, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
        }
    }
}

impl<'a, I, O, E, A, F> Parser<'a, I, E> for Map<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(A::Output) -> O,
{
    type Output = O;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let out = self.parser.go::<M>(inp)?;
        Ok(M::map(out, &self.mapper))
    }

    go_extra!();
}

impl<'a, I, O, E, A, F> IterParser<'a, I, E> for Map<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: IterParser<'a, I, E>,
    F: Fn(A::Item) -> O,
{
    type Item = O;

    type IterState<M: Mode> = A::IterState<M>
    where
        I: 'a;

    #[inline]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        self.parser.make_iter(inp)
    }

    #[inline]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, Self::Item> {
        match self.parser.next::<M>(inp, state) {
            Ok(Some(o)) => Ok(Some(M::map(o, |o| (self.mapper)(o)))),
            Ok(None) => Ok(None),
            Err(()) => Err(()),
        }
    }
}

/// See [`Parser::map_with_span`].
pub struct MapWithSpan<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<A: Copy, F: Copy> Copy for MapWithSpan<A, F> {}
impl<A: Clone, F: Clone> Clone for MapWithSpan<A, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
        }
    }
}

impl<'a, I, O, E, A, F> Parser<'a, I, E> for MapWithSpan<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(A::Output, I::Span) -> O,
{
    type Output = O;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let before = inp.offset();
        let out = self.parser.go::<M>(inp)?;
        Ok(M::map(out, |out| {
            // SAFETY: Using offsets derived from input
            let span = unsafe { inp.span_since(before) };
            (self.mapper)(out, span)
        }))
    }

    go_extra!();
}

/// See [`Parser::map_with_state`].
pub struct MapWithState<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<A: Copy, F: Copy> Copy for MapWithState<A, F> {}
impl<A: Clone, F: Clone> Clone for MapWithState<A, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
        }
    }
}

impl<'a, I, O, E, A, F> Parser<'a, I, E> for MapWithState<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(A::Output, I::Span, &mut E::State) -> O,
{
    type Output = O;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let before = inp.offset();
        let out = self.parser.go::<Emit>(inp)?;
        Ok(M::bind(|| {
            // SAFETY: Using offsets derived from input
            let span = unsafe { inp.span_since(before) };
            let state = inp.state();
            (self.mapper)(out, span, state)
        }))
    }

    go_extra!();
}

/// See [`Parser::try_map`].
pub struct TryMap<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<A: Copy, F: Copy> Copy for TryMap<A, F> {}
impl<A: Clone, F: Clone> Clone for TryMap<A, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
        }
    }
}

impl<'a, I, O, E, A, F> Parser<'a, I, E> for TryMap<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(A::Output, I::Span) -> Result<O, E::Error>,
{
    type Output = O;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let before = inp.offset();
        let out = self.parser.go::<Emit>(inp)?;
        // SAFETY: Using offsets derived from input
        let span = unsafe { inp.span_since(before) };
        match (self.mapper)(out, span) {
            Ok(out) => Ok(M::bind(|| out)),
            Err(err) => {
                inp.add_alt_err(inp.offset(), err);
                Err(())
            }
        }
    }

    go_extra!();
}

/// See [`Parser::try_map_with_state`].
pub struct TryMapWithState<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<A: Copy, F: Copy> Copy for TryMapWithState<A, F> {}
impl<A: Clone, F: Clone> Clone for TryMapWithState<A, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
        }
    }
}

impl<'a, I, O, E, A, F> Parser<'a, I, E> for TryMapWithState<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(A::Output, I::Span, &mut E::State) -> Result<O, E::Error>,
{
    type Output = O;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let before = inp.offset();
        let out = self.parser.go::<Emit>(inp)?;
        // SAFETY: Using offsets derived from input
        let span = unsafe { inp.span_since(before) };
        match (self.mapper)(out, span, inp.state()) {
            Ok(out) => Ok(M::bind(|| out)),
            Err(err) => {
                inp.add_alt_err(inp.offset(), err);
                Err(())
            }
        }
    }

    go_extra!();
}

/// See [`Parser::to`].
pub struct To<A, O> {
    pub(crate) parser: A,
    pub(crate) to: O,
}

impl<A: Copy, O: Copy> Copy for To<A, O> {}
impl<A: Clone, O: Clone> Clone for To<A, O> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            to: self.to.clone(),
        }
    }
}

impl<'a, I, O, E, A> Parser<'a, I, E> for To<A, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    O: Clone,
{
    type Output = O;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let () = self.parser.go::<Check>(inp)?;
        Ok(M::bind(|| self.to.clone()))
    }

    go_extra!();
}

/// See [`Parser::ignored`].
pub struct Ignored<A> {
    pub(crate) parser: A,
}

impl<A: Copy> Copy for Ignored<A> {}
impl<A: Clone> Clone for Ignored<A> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
        }
    }
}

impl<'a, I, E, A> Parser<'a, I, E> for Ignored<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
{
    type Output = ();

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let () = self.parser.go::<Check>(inp)?;
        Ok(M::bind(|| ()))
    }

    go_extra!();
}

/// See [`Parser::unwrapped`].
pub struct Unwrapped<A, O> {
    pub(crate) parser: A,
    pub(crate) location: Location<'static>,
    pub(crate) phantom: PhantomData<O>,
}

impl<A: Copy, O> Copy for Unwrapped<A, O> {}
impl<A: Clone, O> Clone for Unwrapped<A, O> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            location: self.location,
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, O, U> Parser<'a, I, E> for Unwrapped<A, Result<O, U>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E, Output = Result<O, U>>,
    U: fmt::Debug,
{
    type Output = O;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let out = self.parser.go::<M>(inp)?;
        Ok(M::map(out, |out| match out {
            Ok(out) => out,
            Err(err) => panic!(
                "called `Result::unwrap` on a `Err(_)` value at {}: {:?}",
                self.location, err
            ),
        }))
    }

    go_extra!();
}

impl<'a, I, E, A, O> Parser<'a, I, E> for Unwrapped<A, Option<O>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E, Output = Option<O>>,
{
    type Output = O;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let out = self.parser.go::<M>(inp)?;
        Ok(M::map(out, |out| match out {
            Some(out) => out,
            None => panic!(
                "called `Option::unwrap` on a `None` value at {}",
                self.location
            ),
        }))
    }

    go_extra!();
}

/// See [`Parser::memoised`].
#[cfg(feature = "memoization")]
#[derive(Copy, Clone)]
pub struct Memoised<A> {
    pub(crate) parser: A,
}

#[cfg(feature = "memoization")]
impl<'a, I, E, A> Parser<'a, I, E> for Memoised<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    E::Error: Clone,
    A: Parser<'a, I, E>,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        // TODO: Don't use address, since this might not be constant?
        let key = (inp.offset(), &self.parser as *const _ as *const () as usize);

        match inp.memos.entry(key) {
            hashbrown::hash_map::Entry::Occupied(o) => {
                if let Some(err) = o.get() {
                    let err = err.clone();
                    inp.add_alt_err(err.pos, err.err);
                } else {
                    // SAFETY: Using offsets derived from input
                    let err_span = unsafe { inp.span_since(key.0) };
                    inp.add_alt(key.0, None, None, err_span);
                }
                return Err(());
            }
            hashbrown::hash_map::Entry::Vacant(v) => {
                v.insert(None);
            }
        }

        let res = self.parser.go::<M>(inp);

        if res.is_err() {
            inp.memos.insert(
                key,
                Some(inp.errors.alt.clone().expect("failure but no alt?!")),
            );
        } else {
            inp.memos.remove(&key);
        }

        res
    }

    go_extra!();
}

/// See [`Parser::then`].
pub struct Then<A, B, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<E>,
}

impl<A: Copy, B: Copy, E> Copy for Then<A, B, E> {}
impl<A: Clone, B: Clone, E> Clone for Then<A, B, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B> Parser<'a, I, E> for Then<A, B, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E>,
{
    type Output = (A::Output, B::Output);

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let a = self.parser_a.go::<M>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::combine(a, b, |a: A::Output, b: B::Output| (a, b)))
    }

    go_extra!();
}

/// See [`Parser::ignore_then`].
pub struct IgnoreThen<A, B, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<E>,
}

impl<A: Copy, B: Copy, E> Copy for IgnoreThen<A, B, E> {}
impl<A: Clone, B: Clone, E> Clone for IgnoreThen<A, B, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B> Parser<'a, I, E> for IgnoreThen<A, B, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E>,
{
    type Output = B::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let _a = self.parser_a.go::<Check>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::map(b, |b: B::Output| b))
    }

    go_extra!();
}

/// See [`Parser::then_ignore`].
pub struct ThenIgnore<A, B, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<E>,
}

impl<A: Copy, B: Copy, E> Copy for ThenIgnore<A, B, E> {}
impl<A: Clone, B: Clone, E> Clone for ThenIgnore<A, B, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B> Parser<'a, I, E> for ThenIgnore<A, B, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E>,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let a = self.parser_a.go::<M>(inp)?;
        let _b = self.parser_b.go::<Check>(inp)?;
        Ok(M::map(a, |a: A::Output| a))
    }

    go_extra!();
}

/// See [`Parser::nested_in`].
pub struct NestedIn<A, B, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<E>,
}

impl<A: Copy, B: Copy, E> Copy for NestedIn<A, B, E> {}
impl<A: Clone, B: Clone, E> Clone for NestedIn<A, B, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B> Parser<'a, I, E> for NestedIn<A, B, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E, Output = I>,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let inp2 = self.parser_b.go::<Emit>(inp)?;

        let alt = inp.errors.alt.take();

        #[cfg(feature = "memoization")]
        let mut memos = HashMap::default();
        let res = inp.with_input(
            &inp2,
            |inp| self.then_ignore(end()).parser_a.go::<M>(inp),
            #[cfg(feature = "memoization")]
            &mut memos,
        );

        // TODO: Translate secondary error offsets too
        let new_alt = inp.errors.alt.take();
        inp.errors.alt = alt;
        if let Some(new_alt) = new_alt {
            inp.add_alt_err(inp.offset(), new_alt.err);
        }

        res
    }

    go_extra!();
}

/// See [`Parser::then_with_ctx`].
pub struct ThenWithCtx<A, B, I: ?Sized, E> {
    pub(crate) parser: A,
    pub(crate) then: B,
    pub(crate) phantom: PhantomData<(E, I)>,
}

impl<A: Copy, B: Copy, I: ?Sized, E> Copy for ThenWithCtx<A, B, I, E> {}
impl<A: Clone, B: Clone, I: ?Sized, E> Clone for ThenWithCtx<A, B, I, E> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            then: self.then.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B> Parser<'a, I, E>
    for ThenWithCtx<A, B, I, extra::Full<E::Error, E::State, A::Output>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, extra::Full<E::Error, E::State, A::Output>>,
    A::Output: 'a,
{
    type Output = B::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let p1 = self.parser.go::<Emit>(inp)?;
        inp.with_ctx(&p1, |inp| self.then.go::<M>(inp))
    }

    go_extra!();
}

impl<'a, I, E, A, B> IterParser<'a, I, E>
    for ThenWithCtx<A, B, I, extra::Full<E::Error, E::State, A::Output>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: IterParser<'a, I, extra::Full<E::Error, E::State, A::Output>>,
    A::Output: 'a,
{
    type Item = B::Item;

    type IterState<M: Mode> = (A::Output, B::IterState<M>)
    where
        I: 'a;

    #[inline]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        let out = self.parser.go::<Emit>(inp)?;
        let then = inp.with_ctx(&out, |inp| self.then.make_iter::<M>(inp))?;
        Ok((out, then))
    }

    #[inline]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, Self::Item> {
        let (ctx, inner_state) = state;

        inp.with_ctx(ctx, |inp| self.then.next(inp, inner_state))
    }
}

/// See [`Parser::with_ctx`].
pub struct WithCtx<A, Ctx> {
    pub(crate) parser: A,
    pub(crate) ctx: Ctx,
}

impl<A: Copy, Ctx: Copy> Copy for WithCtx<A, Ctx> {}
impl<A: Clone, Ctx: Clone> Clone for WithCtx<A, Ctx> {
    fn clone(&self) -> Self {
        WithCtx {
            parser: self.parser.clone(),
            ctx: self.ctx.clone(),
        }
    }
}

impl<'a, I, E, A, Ctx> Parser<'a, I, E> for WithCtx<A, Ctx>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, extra::Full<E::Error, E::State, Ctx>>,
    Ctx: 'a,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        inp.with_ctx(&self.ctx, |inp| self.parser.go::<M>(inp))
    }

    go_extra!();
}

/// See [`Parser::delimited_by`].
pub struct DelimitedBy<A, B, C> {
    pub(crate) parser: A,
    pub(crate) start: B,
    pub(crate) end: C,
}

impl<A: Copy, B: Copy, C: Copy> Copy for DelimitedBy<A, B, C> {}
impl<A: Clone, B: Clone, C: Clone> Clone for DelimitedBy<A, B, C> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            start: self.start.clone(),
            end: self.end.clone(),
        }
    }
}

impl<'a, I, E, A, B, C> Parser<'a, I, E> for DelimitedBy<A, B, C>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E>,
    C: Parser<'a, I, E>,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let _ = self.start.go::<Check>(inp)?;
        let a = self.parser.go::<M>(inp)?;
        let _ = self.end.go::<Check>(inp)?;
        Ok(a)
    }

    go_extra!();
}

/// See [`Parser::padded_by`].
pub struct PaddedBy<A, B> {
    pub(crate) parser: A,
    pub(crate) padding: B,
}

impl<A: Copy, B: Copy> Copy for PaddedBy<A, B> {}
impl<A: Clone, B: Clone> Clone for PaddedBy<A, B> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            padding: self.padding.clone(),
        }
    }
}

impl<'a, I, E, A, B> Parser<'a, I, E> for PaddedBy<A, B>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E>,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let _ = self.padding.go::<Check>(inp)?;
        let a = self.parser.go::<M>(inp)?;
        let _ = self.padding.go::<Check>(inp)?;
        Ok(a)
    }

    go_extra!();
}

/// See [`Parser::or`].
#[derive(Copy, Clone)]
pub struct Or<A, B> {
    pub(crate) choice: crate::primitive::Choice<(A, B)>,
}

impl<'a, I, E, A, B> Parser<'a, I, E> for Or<A, B>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E, Output = A::Output>,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        self.choice.go::<M>(inp)
    }

    go_extra!();
}

/// Configuration for [`Parser::repeated`], used in [`ConfigParser::configure`].
#[derive(Default)]
pub struct RepeatedCfg {
    at_least: Option<usize>,
    at_most: Option<usize>,
}

impl RepeatedCfg {
    /// Set the minimum number of repetitions accepted
    pub fn at_least(mut self, n: usize) -> Self {
        self.at_least = Some(n);
        self
    }

    /// Set the maximum number of repetitions accepted
    pub fn at_most(mut self, n: usize) -> Self {
        self.at_most = Some(n);
        self
    }

    /// Set an exact number of repetitions to accept
    pub fn exactly(mut self, n: usize) -> Self {
        self.at_least = Some(n);
        self.at_most = Some(n);
        self
    }
}

/// See [`Parser::repeated`].
pub struct Repeated<A, I: ?Sized, E> {
    pub(crate) parser: A,
    pub(crate) at_least: usize,
    // Slightly evil: Should be `Option<usize>`, but we encode `!0` as 'no cap' because it's so large
    pub(crate) at_most: u64,
    pub(crate) phantom: PhantomData<(E, I)>,
}

impl<A: Copy, I: ?Sized, E> Copy for Repeated<A, I, E> {}
impl<A: Clone, I: ?Sized, E> Clone for Repeated<A, I, E> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            at_least: self.at_least,
            at_most: self.at_most,
            phantom: PhantomData,
        }
    }
}

impl<'a, A, I, E> Repeated<A, I, E>
where
    A: Parser<'a, I, E>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    /// Require that the pattern appear at least a minimum number of times.
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, ..self }
    }

    /// Require that the pattern appear at most a maximum number of times.
    pub fn at_most(self, at_most: usize) -> Self {
        Self {
            at_most: at_most as u64,
            ..self
        }
    }

    /// Require that the pattern appear exactly the given number of times. If the value provided
    /// is constant, consider instead using [`Parser::repeated_exactly`]
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let ring = just::<_, _, extra::Err<Simple<char>>>('O');
    ///
    /// let for_the_elves = ring
    ///     .repeated()
    ///     .exactly(3)
    ///     .collect::<Vec<_>>();
    ///
    /// let for_the_dwarves = ring
    ///     .repeated()
    ///     .exactly(6)
    ///     .collect::<Vec<_>>();
    ///
    /// let for_the_humans = ring
    ///     .repeated()
    ///     .exactly(9)
    ///     .collect::<Vec<_>>();
    ///
    /// let for_sauron = ring
    ///     .repeated()
    ///     .exactly(1)
    ///     .collect::<Vec<_>>();
    ///
    /// let rings = for_the_elves
    ///     .then(for_the_dwarves)
    ///     .then(for_the_humans)
    ///     .then(for_sauron);
    ///
    /// assert!(rings.parse("OOOOOOOOOOOOOOOOOO").has_errors()); // Too few rings!
    /// assert!(rings.parse("OOOOOOOOOOOOOOOOOOOO").has_errors()); // Too many rings!
    /// // The perfect number of rings
    /// assert_eq!(
    ///     rings.parse("OOOOOOOOOOOOOOOOOOO").into_result(),
    ///     Ok(((((vec!['O'; 3]), vec!['O'; 6]), vec!['O'; 9]), vec!['O'; 1])),
    /// );
    /// ````
    pub fn exactly(self, exactly: usize) -> Self {
        Self {
            at_least: exactly,
            at_most: exactly as u64,
            ..self
        }
    }
}

impl<'a, I, E, A> Parser<'a, I, E> for Repeated<A, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
{
    type Output = ();

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let mut state = self.make_iter::<Check>(inp)?;
        loop {
            match self.next::<Check>(inp, &mut state) {
                Ok(Some(())) => {}
                Ok(None) => break Ok(M::bind(|| ())),
                Err(()) => break Err(()),
            }
        }
    }

    go_extra!();
}

impl<'a, A, I, E> IterParser<'a, I, E> for Repeated<A, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
{
    type Item = A::Output;

    type IterState<M: Mode> = usize;

    fn make_iter<M: Mode>(
        &self,
        _inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok(0)
    }

    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        count: &mut Self::IterState<M>,
    ) -> IPResult<M, Self::Item> {
        if *count as u64 >= self.at_most {
            return Ok(None);
        }

        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(item) => {
                *count += 1;
                Ok(Some(item))
            }
            Err(()) => {
                inp.rewind(before);
                if *count >= self.at_least {
                    Ok(None)
                } else {
                    Err(())
                }
            }
        }
    }
}

impl<'a, A, I, E> ConfigIterParser<'a, I, E> for Repeated<A, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
{
    type Config = RepeatedCfg;

    fn next_cfg<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        count: &mut Self::IterState<M>,
        cfg: &Self::Config,
    ) -> IPResult<M, Self::Item> {
        let at_most = cfg.at_most.map(|x| x as u64).unwrap_or(self.at_most);
        let at_least = cfg.at_least.unwrap_or(self.at_least);

        if *count as u64 >= at_most {
            return Ok(None);
        }

        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(item) => {
                *count += 1;
                Ok(Some(item))
            }
            Err(()) => {
                inp.rewind(before);
                if *count >= at_least {
                    Ok(None)
                } else {
                    Err(())
                }
            }
        }
    }
}

/// See [`Parser::separated_by`].
pub struct SeparatedBy<A, B, I: ?Sized, E> {
    pub(crate) parser: A,
    pub(crate) separator: B,
    pub(crate) at_least: usize,
    // Slightly evil: Should be `Option<usize>`, but we encode `!0` as 'no cap' because it's so large
    pub(crate) at_most: u64,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
    pub(crate) phantom: PhantomData<(E, I)>,
}

impl<A: Copy, B: Copy, I: ?Sized, E> Copy for SeparatedBy<A, B, I, E> {}
impl<A: Clone, B: Clone, I: ?Sized, E> Clone for SeparatedBy<A, B, I, E> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            separator: self.separator.clone(),
            at_least: self.at_least,
            at_most: self.at_most,
            allow_leading: self.allow_leading,
            allow_trailing: self.allow_trailing,
            phantom: PhantomData,
        }
    }
}

impl<'a, A, B, I, E> SeparatedBy<A, B, I, E>
where
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    /// Require that the pattern appear at least a minimum number of times.
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let numbers = just::<_, _, extra::Err<Simple<char>>>('-')
    ///     .separated_by(just('.'))
    ///     .at_least(2)
    ///     .collect::<Vec<_>>();
    ///
    /// assert!(numbers.parse("").has_errors());
    /// assert!(numbers.parse("-").has_errors());
    /// assert_eq!(numbers.parse("-.-").into_result(), Ok(vec!['-', '-']));
    /// ````
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, ..self }
    }

    /// Require that the pattern appear at most a maximum number of times.
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let row_4 = text::int::<_, _, extra::Err<Simple<char>>>(10)
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .at_most(4)
    ///     .collect::<Vec<_>>();
    ///
    /// let matrix_4x4 = row_4
    ///     .separated_by(just(','))
    ///     .at_most(4)
    ///     .collect::<Vec<_>>();
    ///
    /// assert_eq!(
    ///     matrix_4x4.parse("0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15").into_result(),
    ///     Ok(vec![
    ///         vec!["0", "1", "2", "3"],
    ///         vec!["4", "5", "6", "7"],
    ///         vec!["8", "9", "10", "11"],
    ///         vec!["12", "13", "14", "15"],
    ///     ]),
    /// );
    /// ````
    pub fn at_most(self, at_most: usize) -> Self {
        Self {
            at_most: at_most as u64,
            ..self
        }
    }

    /// Require that the pattern appear exactly the given number of times. If the value provided is
    /// constant, consider instead using [`Parser::separated_by_exactly`].
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let coordinate_3d = text::int::<_, _, extra::Err<Simple<char>>>(10)
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .exactly(3)
    ///     .collect::<Vec<_>>();
    ///
    /// // Not enough elements
    /// assert!(coordinate_3d.parse("4, 3").has_errors());
    /// // Too many elements
    /// assert!(coordinate_3d.parse("7, 2, 13, 4").has_errors());
    /// // Just the right number of elements
    /// assert_eq!(coordinate_3d.parse("5, 0, 12").into_result(), Ok(vec!["5", "0", "12"]));
    /// ````
    pub fn exactly(self, exactly: usize) -> Self {
        Self {
            at_least: exactly,
            at_most: exactly as u64,
            ..self
        }
    }

    /// Allow a leading separator to appear before the first item.
    ///
    /// Note that even if no items are parsed, a leading separator *is* permitted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let r#enum = text::keyword::<_, _, _, extra::Err<Simple<char>>>("enum")
    ///     .padded()
    ///     .ignore_then(text::ident()
    ///         .padded()
    ///         .separated_by(just('|'))
    ///         .allow_leading()
    ///         .collect::<Vec<_>>());
    ///
    /// assert_eq!(r#enum.parse("enum True | False").into_result(), Ok(vec!["True", "False"]));
    /// assert_eq!(r#enum.parse("
    ///     enum
    ///     | True
    ///     | False
    /// ").into_result(), Ok(vec!["True", "False"]));
    /// ```
    pub fn allow_leading(self) -> Self {
        Self {
            allow_leading: true,
            ..self
        }
    }

    /// Allow a trailing separator to appear after the last item.
    ///
    /// Note that if no items are parsed, no leading separator is permitted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let numbers = text::int::<_, _, extra::Err<Simple<char>>>(10)
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .allow_trailing()
    ///     .collect::<Vec<_>>()
    ///     .delimited_by(just('('), just(')'));
    ///
    /// assert_eq!(numbers.parse("(1, 2)").into_result(), Ok(vec!["1", "2"]));
    /// assert_eq!(numbers.parse("(1, 2,)").into_result(), Ok(vec!["1", "2"]));
    /// ```
    pub fn allow_trailing(self) -> Self {
        Self {
            allow_trailing: true,
            ..self
        }
    }
}

impl<'a, I, E, A, B> IterParser<'a, I, E> for SeparatedBy<A, B, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E>,
{
    type Item = A::Output;

    type IterState<M: Mode> = usize
    where
        I: 'a;

    fn make_iter<M: Mode>(
        &self,
        _inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok(0)
    }

    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, Self::Item> {
        if *state as u64 >= self.at_most {
            return Ok(None);
        }

        let before_separator = inp.save();
        if *state == 0 && self.allow_leading {
            if let Err(_) = self.separator.go::<Check>(inp) {
                inp.rewind(before_separator);
            }
        } else if *state > 0 {
            match self.separator.go::<Check>(inp) {
                Ok(()) => {
                    // Do nothing
                }
                Err(()) if *state < self.at_least => {
                    inp.rewind(before_separator);
                    return Err(());
                }
                Err(()) => {
                    inp.rewind(before_separator);
                    return Ok(None);
                }
            }
        }

        let before_item = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(item) => {
                *state += 1;
                Ok(Some(item))
            }
            Err(()) if *state < self.at_least => {
                // We have errored before we have reached the count,
                // and therefore should return this error, as we are
                // still expecting items
                inp.rewind(before_separator);
                Err(())
            }
            Err(()) => {
                // We are not expecting any more items, so it is okay
                // for it to fail.

                // though if we don't allow trailing, we shouldn't have
                // consumed the separator, so we need to rewind it.
                if self.allow_trailing {
                    inp.rewind(before_item);
                } else {
                    inp.rewind(before_separator);
                }
                Ok(None)
            }
        }
    }
}

impl<'a, I, E, A, B> Parser<'a, I, E> for SeparatedBy<A, B, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E>,
{
    type Output = ();

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let mut state = self.make_iter::<Check>(inp)?;
        loop {
            match self.next::<Check>(inp, &mut state) {
                Ok(Some(())) => {}
                Ok(None) => break Ok(M::bind(|| ())),
                Err(()) => break Err(()),
            }
        }
    }

    go_extra!();
}

/// See [`IterParser::collect`].
pub struct Collect<A, C> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<C>,
}

impl<A: Copy, C> Copy for Collect<A, C> {}
impl<A: Clone, C> Clone for Collect<A, C> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, C> Parser<'a, I, E> for Collect<A, C>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: IterParser<'a, I, E>,
    C: Container<A::Item>,
{
    type Output = C;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, C> {
        let mut output = M::bind::<C, _>(|| C::default());
        let mut iter_state = self.parser.make_iter::<M>(inp)?;
        loop {
            match self.parser.next::<M>(inp, &mut iter_state) {
                Ok(Some(out)) => {
                    output = M::combine(output, out, |mut output: C, item| {
                        output.push(item);
                        output
                    });
                }
                Ok(None) => break Ok(output),
                Err(()) => break Err(()),
            }
        }
    }

    go_extra!();
}

/// See [`Parser::or_not`].
#[derive(Copy, Clone)]
pub struct OrNot<A> {
    pub(crate) parser: A,
}

// TODO: Maybe implement `IterParser` too?
impl<'a, I, E, A> Parser<'a, I, E> for OrNot<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
{
    type Output = Option<A::Output>;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let before = inp.save();
        Ok(match self.parser.go::<M>(inp) {
            Ok(out) => M::map::<A::Output, _, _>(out, Some),
            Err(()) => {
                inp.rewind(before);
                M::bind::<Self::Output, _>(|| None)
            }
        })
    }

    go_extra!();
}

/// See [`Parser::not`].
pub struct Not<A> {
    pub(crate) parser: A,
}

impl<A: Copy> Copy for Not<A> {}
impl<A: Clone> Clone for Not<A> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
        }
    }
}

impl<'a, I, E, A> Parser<'a, I, E> for Not<A>
where
    I: ValueInput<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
{
    type Output = ();

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let before = inp.save();

        let alt = inp.errors.alt.take();

        let result = self.parser.go::<Check>(inp);
        // SAFETY: Using offsets derived from input
        let result_span = unsafe { inp.span_since(before.offset) };
        inp.rewind(before);

        inp.errors.alt = alt;

        match result {
            Ok(()) => {
                let (at, found) = inp.next();
                inp.add_alt(at, None, found.map(|f| f.into()), result_span);
                Err(())
            }
            Err(()) => Ok(M::bind(|| ())),
        }
    }

    go_extra!();
}

/// See [`Parser::and_is`].
pub struct AndIs<A, B> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
}

impl<A: Copy, B: Copy> Copy for AndIs<A, B> {}
impl<A: Clone, B: Clone> Clone for AndIs<A, B> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
        }
    }
}

impl<'a, I, E, A, B> Parser<'a, I, E> for AndIs<A, B>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E>,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let before = inp.save();
        match self.parser_a.go::<M>(inp) {
            Ok(out) => {
                // A succeeded -- go back to the beginning and try B
                let after = inp.save();
                inp.rewind(before);

                match self.parser_b.go::<Check>(inp) {
                    Ok(()) => {
                        // B succeeded -- go to the end of A and return its output
                        inp.rewind(after);
                        Ok(out)
                    }
                    Err(()) => {
                        // B failed -- go back to the beginning and fail
                        inp.rewind(before);
                        Err(())
                    }
                }
            }
            Err(()) => {
                // A failed -- go back to the beginning and fail
                inp.rewind(before);
                Err(())
            }
        }
    }

    go_extra!();
}

/// See [`Parser::repeated_exactly`].
pub struct RepeatedExactly<A, C, const N: usize> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<C>,
}

impl<A: Copy, C, const N: usize> Copy for RepeatedExactly<A, C, N> {}
impl<A: Clone, C, const N: usize> Clone for RepeatedExactly<A, C, N> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: PhantomData,
        }
    }
}

impl<A, C, const N: usize> RepeatedExactly<A, C, N> {
    /// Set the type of [`ContainerExactly`] to collect into.
    pub fn collect<'a, I, E, D>(self) -> RepeatedExactly<A, D, N>
    where
        A: Parser<'a, I, E>,
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        D: ContainerExactly<A::Output, N>,
    {
        RepeatedExactly {
            parser: self.parser,
            phantom: PhantomData,
        }
    }
}

// TODO: Work out how this can properly integrate into `IterParser`
impl<'a, I, E, A, C, const N: usize> Parser<'a, I, E> for RepeatedExactly<A, C, N>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    C: ContainerExactly<A::Output, N>,
{
    type Output = C;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, C> {
        let mut i = 0;
        let mut output = M::bind(|| C::uninit());
        loop {
            let before = inp.save();
            match self.parser.go::<M>(inp) {
                Ok(out) => {
                    output = M::map(output, |mut output| {
                        M::map(out, |out| {
                            C::write(&mut output, i, out);
                        });
                        output
                    });
                    i += 1;
                    if i == N {
                        // SAFETY: All entries with an index < i are filled
                        break Ok(M::map(output, |output| unsafe { C::take(output) }));
                    }
                }
                Err(()) => {
                    inp.rewind(before);
                    // SAFETY: All entries with an index < i are filled
                    unsafe {
                        M::map(output, |mut output| C::drop_before(&mut output, i));
                    }
                    break Err(());
                }
            }
        }
    }

    go_extra!();
}

/// See [`Parser::separated_by_exactly`].
pub struct SeparatedByExactly<A, B, C, const N: usize> {
    pub(crate) parser: A,
    pub(crate) separator: B,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
    pub(crate) phantom: PhantomData<C>,
}

impl<A: Copy, B: Copy, C, const N: usize> Copy for SeparatedByExactly<A, B, C, N> {}
impl<A: Clone, B: Clone, C, const N: usize> Clone for SeparatedByExactly<A, B, C, N> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            separator: self.separator.clone(),
            allow_leading: self.allow_leading,
            allow_trailing: self.allow_trailing,
            phantom: PhantomData,
        }
    }
}

impl<A, B, C, const N: usize> SeparatedByExactly<A, B, C, N> {
    /// Allow a leading separator to appear before the first item.
    ///
    /// Note that even if no items are parsed, a leading separator *is* permitted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let r#enum = text::keyword::<_, _, _, extra::Err<Simple<char>>>("enum")
    ///     .padded()
    ///     .ignore_then(text::ident()
    ///         .padded()
    ///         .separated_by(just('|'))
    ///         .allow_leading()
    ///         .collect::<Vec<_>>());
    ///
    /// assert_eq!(r#enum.parse("enum True | False").into_result(), Ok(vec!["True", "False"]));
    /// assert_eq!(r#enum.parse("
    ///     enum
    ///     | True
    ///     | False
    /// ").into_result(), Ok(vec!["True", "False"]));
    /// ```
    pub fn allow_leading(self) -> Self {
        Self {
            allow_leading: true,
            ..self
        }
    }

    /// Allow a trailing separator to appear after the last item.
    ///
    /// Note that if no items are parsed, no trailing separator is permitted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let numbers = text::int::<_, _, extra::Err<Simple<char>>>(10)
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .allow_trailing()
    ///     .collect::<Vec<_>>()
    ///     .delimited_by(just('('), just(')'));
    ///
    /// assert_eq!(numbers.parse("(1, 2)").into_result(), Ok(vec!["1", "2"]));
    /// assert_eq!(numbers.parse("(1, 2,)").into_result(), Ok(vec!["1", "2"]));
    /// ```
    pub fn allow_trailing(self) -> Self {
        Self {
            allow_trailing: true,
            ..self
        }
    }

    /// Set the type of [`ContainerExactly`] to collect into.
    pub fn collect<'a, I, E, D>(self) -> SeparatedByExactly<A, B, D, N>
    where
        A: Parser<'a, I, E>,
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        D: ContainerExactly<A::Output, N>,
    {
        SeparatedByExactly {
            parser: self.parser,
            separator: self.separator,
            allow_leading: self.allow_leading,
            allow_trailing: self.allow_trailing,
            phantom: PhantomData,
        }
    }
}

// FIXME: why parser output is not C ?
impl<'a, I, E, A, B, C, const N: usize> Parser<'a, I, E>
    for SeparatedByExactly<A, B, C, N>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    B: Parser<'a, I, E>,
    C: ContainerExactly<A::Output, N>,
{
    type Output = [A::Output; N];

    // FIXME: why parse result output is not C ?
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        if self.allow_leading {
            let before_separator = inp.save();
            if let Err(()) = self.separator.go::<Check>(inp) {
                inp.rewind(before_separator);
            }
        }

        let mut i = 0;
        let mut output = <MaybeUninit<_> as MaybeUninitExt<_>>::uninit_array();
        loop {
            let before = inp.save();
            match self.parser.go::<M>(inp) {
                Ok(out) => {
                    output[i].write(out);
                    i += 1;
                    if i == N {
                        if self.allow_trailing {
                            let before_separator = inp.save();
                            if self.separator.go::<Check>(inp).is_err() {
                                inp.rewind(before_separator);
                            }
                        }

                        // SAFETY: All entries with an index < i are filled
                        break Ok(M::array::<A::Output, N>(unsafe {
                            MaybeUninitExt::array_assume_init(output)
                        }));
                    } else {
                        let before_separator = inp.save();
                        if self.separator.go::<Check>(inp).is_err() {
                            inp.rewind(before_separator);
                            // SAFETY: All entries with an index < i are filled
                            output[..i]
                                .iter_mut()
                                .for_each(|o| unsafe { o.assume_init_drop() });
                            break Err(());
                        }
                    }
                }
                Err(()) => {
                    inp.rewind(before);
                    // SAFETY: All entries with an index < i are filled
                    output[..i]
                        .iter_mut()
                        .for_each(|o| unsafe { o.assume_init_drop() });
                    break Err(());
                }
            }
        }
    }

    go_extra!();
}

/// See [`IterParser::foldr`].
pub struct Foldr<F, A, B, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) folder: F,
    pub(crate) phantom: PhantomData<E>,
}

impl<F: Copy, A: Copy, B: Copy, E> Copy for Foldr<F, A, B, E> {}
impl<F: Clone, A: Clone, B: Clone, E> Clone for Foldr<F, A, B, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            folder: self.folder.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, F, A, B, E> Parser<'a, I, E> for Foldr<F, A, B, E>
where
    I: Input<'a>,
    A: IterParser<'a, I, E>,
    B: Parser<'a, I, E>,
    E: ParserExtra<'a, I>,
    F: Fn(A::Item, B::Output) -> B::Output,
{
    type Output = B::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output>
    where
        Self: Sized,
    {
        let mut a_out = M::bind(|| Vec::new());
        let mut iter_state = self.parser_a.make_iter::<M>(inp)?;
        loop {
            match self.parser_a.next::<M>(inp, &mut iter_state) {
                Ok(Some(out)) => {
                    a_out = M::combine(a_out, out, |mut a_out, item| {
                        a_out.push(item);
                        a_out
                    });
                }
                Ok(None) => break,
                Err(()) => return Err(()),
            }
        }

        let b_out = self.parser_b.go::<M>(inp)?;

        Ok(M::combine(a_out, b_out, |a_out, b_out| {
            a_out.into_iter().rfold(b_out, |b, a| (self.folder)(a, b))
        }))
    }

    go_extra!();
}

/// See [`Parser::foldl`].
pub struct Foldl<F, A, B, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) folder: F,
    pub(crate) phantom: PhantomData<E>,
}

impl<F: Copy, A: Copy, B: Copy, E> Copy for Foldl<F, A, B, E> {}
impl<F: Clone, A: Clone, B: Clone, E> Clone for Foldl<F, A, B, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            folder: self.folder.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, F, A, B, E> Parser<'a, I, E> for Foldl<F, A, B, E>
where
    I: Input<'a>,
    A: Parser<'a, I, E>,
    B: IterParser<'a, I, E>,
    E: ParserExtra<'a, I>,
    F: Fn(A::Output, B::Item) -> A::Output,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output>
    where
        Self: Sized,
    {
        let mut out = self.parser_a.go::<M>(inp)?;
        let mut iter_state = self.parser_b.make_iter::<M>(inp)?;
        loop {
            match self.parser_b.next::<M>(inp, &mut iter_state) {
                Ok(Some(b_out)) => {
                    out = M::combine(out, b_out, |out, b_out| (self.folder)(out, b_out));
                }
                Ok(None) => break Ok(out),
                Err(()) => break Err(()),
            }
        }
    }

    go_extra!();
}

/// See [`Parser::rewind`].
#[must_use]
#[derive(Copy, Clone)]
pub struct Rewind<A> {
    pub(crate) parser: A,
}

impl<'a, I, E, A> Parser<'a, I, E> for Rewind<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output> {
        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(out) => {
                inp.rewind(before);
                Ok(out)
            }
            Err(()) => Err(()),
        }
    }

    go_extra!();
}

/// See [`Parser::map_err`].
#[derive(Copy, Clone)]
pub struct MapErr<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, E, A, F> Parser<'a, I, E> for MapErr<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(E::Error) -> E::Error,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output>
    where
        Self: Sized,
    {
        let res = self.parser.go::<M>(inp);

        if res.is_err() {
            let mut e = inp.errors.alt.take().expect("error but no alt?");
            e.err = (self.mapper)(e.err);
            inp.errors.alt = Some(e);
        }

        res
    }

    go_extra!();
}

/// See [`Parser::map_err_with_span`].
#[derive(Copy, Clone)]
pub struct MapErrWithSpan<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, E, A, F> Parser<'a, I, E> for MapErrWithSpan<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(E::Error, I::Span) -> E::Error,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output>
    where
        Self: Sized,
    {
        let start = inp.offset();
        let res = self.parser.go::<M>(inp);

        if res.is_err() {
            let mut e = inp.errors.alt.take().expect("error but no alt?");
            // SAFETY: Using offsets derived from input
            let span = unsafe { inp.span_since(start) };
            e.err = (self.mapper)(e.err, span);
        }

        res
    }

    go_extra!();
}

/// See [`Parser::map_err_with_state`].
#[derive(Copy, Clone)]
pub struct MapErrWithState<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, E, A, F> Parser<'a, I, E> for MapErrWithState<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(E::Error, I::Span, &mut E::State) -> E::Error,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output>
    where
        Self: Sized,
    {
        let start = inp.offset();
        let res = self.parser.go::<M>(inp);

        if res.is_err() {
            let mut e = inp.errors.alt.take().expect("error but no alt?");
            // SAFETY: Using offsets derived from input
            let span = unsafe { inp.span_since(start) };
            e.err = (self.mapper)(e.err, span, inp.state());
        }

        res
    }

    go_extra!();
}

/// See [`Parser::validate`]
pub struct Validate<A, F> {
    pub(crate) parser: A,
    pub(crate) validator: F,
}

impl<A: Copy, F: Copy> Copy for Validate<A, F> {}
impl<A: Clone, F: Clone> Clone for Validate<A, F> {
    fn clone(&self) -> Self {
        Validate {
            parser: self.parser.clone(),
            validator: self.validator.clone(),
        }
    }
}

impl<'a, I, U, E, A, F> Parser<'a, I, E> for Validate<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(A::Output, I::Span, &mut Emitter<E::Error>) -> U,
{
    type Output = U;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, U>
    where
        Self: Sized,
    {
        let before = inp.offset();
        self.parser.go::<Emit>(inp).map(|out| {
            // SAFETY: Using offsets derived from input
            let span = unsafe { inp.span_since(before) };
            let mut emitter = Emitter::new();
            let out = (self.validator)(out, span, &mut emitter);
            for err in emitter.errors() {
                inp.emit(err);
            }
            M::bind(|| out)
        })
    }

    go_extra!();
}

/// See [`Parser::or_else`].
#[derive(Copy, Clone)]
pub struct OrElse<A, F> {
    pub(crate) parser: A,
    pub(crate) or_else: F,
}

impl<'a, I, E, A, F> Parser<'a, I, E> for OrElse<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, E>,
    F: Fn(E::Error) -> Result<A::Output, E::Error>,
{
    type Output = A::Output;

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Self::Output>
    where
        Self: Sized,
    {
        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(out) => Ok(out),
            Err(()) => {
                let err = inp.errors.alt.take().expect("error but no alt?");
                match (self.or_else)(err.err) {
                    Ok(out) => {
                        inp.rewind(before);
                        Ok(M::bind(|| out))
                    }
                    Err(new_err) => {
                        inp.errors.alt = Some(Located {
                            pos: err.pos,
                            err: new_err,
                        });
                        Err(())
                    }
                }
            }
        }
    }

    go_extra!();
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn separated_by_at_least() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .at_least(3)
            .collect();

        assert_eq!(parser.parse("-,-,-").into_result(), Ok(vec!['-', '-', '-']));
    }

    #[test]
    fn separated_by_at_least_without_leading() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .at_least(3)
            .collect::<Vec<_>>();

        // Is empty means no errors
        assert!(parser.parse(",-,-,-").has_errors());
    }

    #[test]
    fn separated_by_at_least_without_trailing() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .at_least(3)
            .collect::<Vec<_>>();

        // Is empty means no errors
        assert!(parser.parse("-,-,-,").has_errors());
    }

    #[test]
    fn separated_by_at_least_with_leading() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .allow_leading()
            .at_least(3)
            .collect();

        assert_eq!(
            parser.parse(",-,-,-").into_result(),
            Ok(vec!['-', '-', '-'])
        );
        assert!(parser.parse(",-,-").has_errors());
    }

    #[test]
    fn separated_by_at_least_with_trailing() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .allow_trailing()
            .at_least(3)
            .collect();

        assert_eq!(
            parser.parse("-,-,-,").into_result(),
            Ok(vec!['-', '-', '-'])
        );
        assert!(parser.parse("-,-,").has_errors());
    }

    #[test]
    fn separated_by_leaves_last_separator() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .collect::<Vec<_>>()
            .then(just(','));
        assert_eq!(
            parser.parse("-,-,-,").into_result(),
            Ok((vec!['-', '-', '-'], ',')),
        )
    }
}
