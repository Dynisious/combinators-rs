//! A library of combinator functions with named types.
//! 
//! Author --- DMorgan  
//! Last Moddified --- 2021-03-31

#![no_std]
#![deny(missing_docs,)]
#![feature(
  fn_traits, unboxed_closures, const_ptr_read, const_maybe_uninit_as_ptr,
  const_refs_to_cell, const_fn_fn_ptr_basics, try_trait, coerce_unsized,
  const_fn, min_type_alias_impl_trait, impl_trait_in_bindings,
)]

use core::{
  fmt,
  ops::{Try, CoerceUnsized,},
  marker::PhantomData,
  cmp::Ordering,
};

/// A function which returns the input.
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(Identity(42), 42);
/// ```
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Debug,)]
pub struct Identity;

impl Identity {
  /// Returns the input.
  #[inline]
  pub const fn identity<A,>(a: A,) -> A { a }
}

impl<A,> From<Identity> for fn(A,) -> A {
  #[inline]
  fn from(_: Identity,) -> Self { Identity::identity }
}

impl<A,> FnOnce<(A,)> for Identity {
  type Output = A;

  #[inline]
  extern "rust-call" fn call_once(self, (a,): (A,),) -> Self::Output { a }
}

impl<A,> FnMut<(A,)> for Identity {
  #[inline]
  extern "rust-call" fn call_mut(&mut self, (a,): (A,),) -> Self::Output { a }
}

impl<A,> Fn<(A,)> for Identity {
  #[inline]
  extern "rust-call" fn call(&self, (a,): (A,),) -> Self::Output { a }
}

/// A function which wraps the argument in a [`Replace`](self::Replace).
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(Replace::INIT(42)("dropped"), 42);
/// ```
pub type Keep<A,> = impl Fn(A,) -> Replace<A,> + Clone + Copy;

/// A function which ignores the inputs and returns the inner value.
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(Replace(42)("dropped"), 42);
/// ```
#[repr(transparent,)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Debug,)]
pub struct Replace<A,>(pub A,);

impl<A,> Replace<A,> {
  /// The `Replace` constructor.
  pub const INIT: Keep<A,> = Replace;

  /// Constructs a new `Replace` from `a`.
  #[inline]
  pub const fn new(a: A,) -> Self { Replace(a,) }
  /// Returns the inner value.
  #[inline]
  pub const fn into_inner(self,) -> A {
    use core::{ptr, mem::MaybeUninit,};

    unsafe { ptr::read(MaybeUninit::new(self,).as_ptr() as *const Self as *const A,) }
  }
  /// Maps the inner value.
  #[inline]
  pub fn map<B, F,>(self, map: F,) -> Replace<B,>
    where F: FnOnce(A,) -> B, { Replace::new(map(self.0,),) }
}

impl<A, Args,> FnOnce<Args> for Replace<A,> {
  type Output = A;

  #[inline]
  extern "rust-call" fn call_once(self, _: Args,) -> Self::Output { self.0 }
}

impl<A, Args,> FnMut<Args> for Replace<A,>
  where A: Clone, {
  #[inline]
  extern "rust-call" fn call_mut(&mut self, _: Args,) -> Self::Output { self.0.clone() }
}

impl<A, Args,> Fn<Args> for Replace<A,>
  where A: Clone, {
  #[inline]
  extern "rust-call" fn call(&self, _: Args,) -> Self::Output { self.0.clone() }
}

/// A function which uses the output of one function as the input to a second function.
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(Compose::new(Replace, Replace)(42)("dropped1")("dropped2"), 42);
/// ```
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Debug,)]
pub struct Compose<F, G,> {
  /// The second function to apply.
  pub f: F,
  /// The first function to apply.
  pub g: G,
}

impl<F, G,> Compose<F, G,> {
  /// Constructs a new `Compose` from `f` and `g`.
  #[inline]
  pub const fn new(f: F, g: G,) -> Self { Compose { f, g, } }
  /// Maps the `f` type.
  #[inline]
  pub fn mapf<H, I,>(self, map: I,) -> Compose<H, G,>
    where I: FnOnce(F,) -> H { Compose::new(map(self.f,), self.g,) }
  /// Maps the `g` type.
  #[inline]
  pub fn mapg<H, I,>(self, map: I,) -> Compose<F, H,>
    where I: FnOnce(G,) -> H { Compose::new(self.f, map(self.g,),) }
}

impl<F, G, A, B, C,> FnOnce<(A,)> for Compose<F, G,>
  where F: FnOnce(B,) -> C,
    G: FnOnce(A,) -> B, {
  type Output = C;

  #[inline]
  extern "rust-call" fn call_once(self, (a,): (A,),) -> Self::Output { (self.f)((self.g)(a,),) }
}

impl<F, G, A, B, C,> FnMut<(A,)> for Compose<F, G,>
  where F: FnMut(B,) -> C,
    G: FnMut(A,) -> B, {
  #[inline]
  extern "rust-call" fn call_mut(&mut self, (a,): (A,),) -> Self::Output { (self.f)((self.g)(a,),) }
}

impl<F, G, A, B, C,> Fn<(A,)> for Compose<F, G,>
  where F: Fn(B,) -> C,
    G: Fn(A,) -> B, {
  #[inline]
  extern "rust-call" fn call(&self, (a,): (A,),) -> Self::Output { (self.f)((self.g)(a,),) }
}

/// A function which wraps the argument in a [`TryMap`](self::TryMap).
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(TryMap::INIT(|x| x * 2)(Some(21)), Ok(42));
/// ```
pub type MapOk<F,> = impl Fn(F,) -> TryMap<F,> + Clone + Copy;

/// A function which maps the [`Ok`](core::ops::Try::Ok) variant of a
/// [`Try`](core::ops::Try) value.
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(TryMap(|x| x * 2)(Some(21)), Ok(42));
/// ```
#[repr(transparent,)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Debug,)]
pub struct TryMap<F,>(pub F,)
  where F: ?Sized,;

impl<F,> TryMap<F,> {
  /// The `TryMap` constructor.
  pub const INIT: MapOk<F,> = TryMap;

  /// Constructs a new `TryMap` from `f`.
  #[inline]
  pub const fn new(f: F,) -> Self { TryMap(f,) }
  /// Returns the inner value.
  #[inline]
  pub const fn into_inner(self,) -> F {
    use core::{ptr, mem::MaybeUninit,};

    unsafe { ptr::read(MaybeUninit::new(self,).as_ptr() as *const Self as *const F,) }
  }
  /// Maps the inner value.
  #[inline]
  pub fn map<H, G,>(self, map: G,) -> TryMap<H,>
    where G: FnOnce(F,) -> H, { TryMap::new(map(self.0,),) }
}

impl<F, T, A,> FnOnce<(T,)> for TryMap<F,>
  where F: FnOnce(T::Ok,) -> A,
    T: Try, {
  type Output = Result<A, T::Error>;

  #[inline]
  extern "rust-call" fn call_once(self, (t,): (T,),) -> Self::Output { t.into_result().map(self.0,) }
}

impl<F, T, A,> FnMut<(T,)> for TryMap<F,>
  where F: FnMut(T::Ok,) -> A,
    T: Try, {
  #[inline]
  extern "rust-call" fn call_mut(&mut self, (t,): (T,),) -> Self::Output { t.into_result().map(&mut self.0,) }
}

impl<F, T, A,> Fn<(T,)> for TryMap<F,>
  where F: Fn(T::Ok,) -> A,
    T: Try, {
  #[inline]
  extern "rust-call" fn call(&self, (t,): (T,),) -> Self::Output { t.into_result().map(&self.0,) }
}

impl<A, B,> CoerceUnsized<TryMap<B,>> for TryMap<A,>
  where A: CoerceUnsized<B,> + ?Sized,
    B: ?Sized, {}

/// A function which wraps the argument in a [`TryMapErr`](self::TryMapErr).
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(TryMapErr::INIT(|x| x * 2)(Err(21)), Err(42) as Result<(), i32>);
/// ```
pub type MapErr<F,> = impl Fn(F,) -> TryMapErr<F,> + Clone + Copy;

/// A function which maps the [`Error`](core::ops::Try::Error) variant of a
/// [`Try`](core::ops::Try) value.
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(TryMapErr(|x| x * 2)(Err(21)), Err(42) as Result<(), i32>);
/// ```
#[repr(transparent,)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Debug,)]
pub struct TryMapErr<F,>(pub F,)
  where F: ?Sized,;

impl<F,> TryMapErr<F,> {
  /// The `TryMapErr` constructor.
  pub const INIT: MapErr<F,> = TryMapErr;

  /// Constructs a new `TryMapErr` from `f`.
  #[inline]
  pub const fn new(f: F,) -> Self { TryMapErr(f,) }
  /// Returns the inner value.
  #[inline]
  pub const fn into_inner(self,) -> F {
    use core::{ptr, mem::MaybeUninit,};

    unsafe { ptr::read(MaybeUninit::new(self,).as_ptr() as *const Self as *const F,) }
  }
  /// Maps the inner value.
  #[inline]
  pub fn map<H, G,>(self, map: G,) -> TryMapErr<H,>
    where G: FnOnce(F,) -> H, { TryMapErr::new(map(self.0,),) }
}

impl<F, T, A,> FnOnce<(T,)> for TryMapErr<F,>
  where F: FnOnce(T::Error,) -> A,
    T: Try, {
  type Output = Result<T::Ok, A>;

  #[inline]
  extern "rust-call" fn call_once(self, (t,): (T,),) -> Self::Output { t.into_result().map_err(self.0,) }
}

impl<F, T, A,> FnMut<(T,)> for TryMapErr<F,>
  where F: FnMut(T::Error,) -> A,
    T: Try, {
  #[inline]
  extern "rust-call" fn call_mut(&mut self, (t,): (T,),) -> Self::Output { t.into_result().map_err(&mut self.0,) }
}

impl<F, T, A,> Fn<(T,)> for TryMapErr<F,>
  where F: Fn(T::Error,) -> A,
    T: Try, {
  #[inline]
  extern "rust-call" fn call(&self, (t,): (T,),) -> Self::Output { t.into_result().map_err(&self.0,) }
}

impl<A, B,> CoerceUnsized<TryMapErr<B,>> for TryMapErr<A,>
  where A: CoerceUnsized<B,> + ?Sized,
    B: ?Sized, {}

/// A function which wraps the argument in a [`TryAndThen`](self::TryAndThen).
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(TryAndThen::INIT(|x| Some(x * 2))(Some(21)), Some(42));
/// ```
pub type AndThen<F,> = impl Fn(F,) -> TryAndThen<F,> + Clone + Copy;

/// A function which either maps the [`Ok`](core::ops::Try::Ok) variant of a
/// [`Try`](core::ops::Try) value or returns the error.
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(TryAndThen(|x| Some(x * 2))(Some(21)), Some(42));
/// ```
#[repr(transparent,)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Debug,)]
pub struct TryAndThen<F,>(pub F,)
  where F: ?Sized,;

impl<F,> TryAndThen<F,> {
  /// The `TryAndThen` constructor.
  pub const INIT: AndThen<F,> = TryAndThen;

  /// Constructs a new `TryAndThen` from `f`.
  #[inline]
  pub const fn new(f: F,) -> Self { TryAndThen(f,) }
  /// Returns the inner value.
  #[inline]
  pub const fn into_inner(self,) -> F {
    use core::{ptr, mem::MaybeUninit,};

    unsafe { ptr::read(MaybeUninit::new(self,).as_ptr() as *const Self as *const F,) }
  }
  /// Maps the inner value.
  #[inline]
  pub fn map<H, G,>(self, map: G,) -> TryAndThen<H,>
    where G: FnOnce(F,) -> H, { TryAndThen::new(map(self.0,),) }
}

impl<F, T, A,> FnOnce<(T,)> for TryAndThen<F,>
  where F: FnOnce(T::Ok,) -> A,
    T: Try,
    A: Try,
    A::Error: From<T::Error>, {
  type Output = A;

  extern "rust-call" fn call_once(self, (t,): (T,),) -> Self::Output { (self.0)(t?,) }
}

impl<F, T, A,> FnMut<(T,)> for TryAndThen<F,>
  where F: FnMut(T::Ok,) -> A,
    T: Try,
    A: Try,
    A::Error: From<T::Error>, {
  extern "rust-call" fn call_mut(&mut self, (t,): (T,),) -> Self::Output { (&mut self.0)(t?,) }
}

impl<F, T, A,> Fn<(T,)> for TryAndThen<F,>
  where F: Fn(T::Ok,) -> A,
    T: Try,
    A: Try,
    A::Error: From<T::Error>, {
  extern "rust-call" fn call(&self, (t,): (T,),) -> Self::Output { (&self.0)(t?,) }
}

impl<A, B,> CoerceUnsized<TryAndThen<B,>> for TryAndThen<A,>
  where A: CoerceUnsized<B,> + ?Sized,
    B: ?Sized, {}

/// A function which wraps the argument in a [`TryOrElse`](self::TryOrElse).
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(TryOrElse::INIT(|_| Some(42))(None as Option<i32>), Some(42));
/// ```
pub type OrElse<F,> = impl Fn(F,) -> TryOrElse<F,> + Clone + Copy;

/// A function which either maps the [`Error`](core::ops::Try::Error) variant of a
/// [`Try`](core::ops::Try) value or returns the success.
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(TryOrElse(|_| Some(42))(None as Option<i32>), Some(42));
/// ```
#[repr(transparent,)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Debug,)]
pub struct TryOrElse<F,>(pub F,)
  where F: ?Sized,;

impl<F,> TryOrElse<F,> {
  /// The `TryOrElse` constructor.
  pub const INIT: OrElse<F,> = TryOrElse;

  /// Constructs a new `TryOrElse` from `f`.
  #[inline]
  pub const fn new(f: F,) -> Self { TryOrElse(f,) }
  /// Returns the inner value.
  #[inline]
  pub const fn into_inner(self,) -> F {
    use core::{ptr, mem::MaybeUninit,};

    unsafe { ptr::read(MaybeUninit::new(self,).as_ptr() as *const Self as *const F,) }
  }
  /// Maps the inner value.
  #[inline]
  pub fn map<H, G,>(self, map: G,) -> TryOrElse<H,>
    where G: FnOnce(F,) -> H, { TryOrElse::new(map(self.0,),) }
}

impl<F, T, A,> FnOnce<(T,)> for TryOrElse<F,>
  where F: FnOnce(T::Error,) -> A,
    T: Try,
    A: Try,
    A::Ok: From<T::Ok>, {
  type Output = A;

  extern "rust-call" fn call_once(self, (t,): (T,),) -> Self::Output {
    match t.into_result() {
      Ok(v) => A::from_ok(v.into(),),
      Err(e) => (self.0)(e,),
    }
  }
}

impl<F, T, A,> FnMut<(T,)> for TryOrElse<F,>
  where F: FnMut(T::Error,) -> A,
    T: Try,
    A: Try,
    A::Ok: From<T::Ok>, {
  extern "rust-call" fn call_mut(&mut self, (t,): (T,),) -> Self::Output {
    match t.into_result() {
      Ok(v) => A::from_ok(v.into(),),
      Err(e) => (self.0)(e,),
    }
  }
}

impl<F, T, A,> Fn<(T,)> for TryOrElse<F,>
  where F: Fn(T::Error,) -> A,
    T: Try,
    A: Try,
    A::Ok: From<T::Ok>, {
  extern "rust-call" fn call(&self, (t,): (T,),) -> Self::Output {
    match t.into_result() {
      Ok(v) => A::from_ok(v.into(),),
      Err(e) => (self.0)(e,),
    }
  }
}

impl<A, B,> CoerceUnsized<TryOrElse<B,>> for TryOrElse<A,>
  where A: CoerceUnsized<B,> + ?Sized,
    B: ?Sized, {}

/// A function which maps from a `Result` into a [`Try`](core::ops::Try) type.
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(FromTry::<Option<i32>>::INIT(Ok(42)), Some(42));
/// ```
pub struct FromTry<T,>(PhantomData<T>,);

impl<T,> FromTry<T,> {
  /// The singleton value.
  pub const INIT: Self = FromTry(PhantomData,);

  /// Maps from a `Result` into a [`Try`](core::ops::Try) type.
  #[inline]
  pub fn from_try(r: Result<T::Ok, T::Error>,) -> T
    where T: Try, { r.map_or_else(T::from_error, T::from_ok,) }
}

impl<T,> PartialEq for FromTry<T,> {
  #[inline]
  fn eq(&self, _: &Self,) -> bool { true }
}

impl<T,> Eq for FromTry<T,> {}

impl<T,> PartialOrd for FromTry<T,> {
  #[inline]
  fn partial_cmp(&self, _: &Self,) -> Option<Ordering> { Some(Ordering::Equal) }
}

impl<T,> Ord for FromTry<T,> {
  #[inline]
  fn cmp(&self, _: &Self,) -> Ordering { Ordering::Equal }
}

impl<T,> Default for FromTry<T,> {
  #[inline]
  fn default() -> Self { Self::INIT }
}

impl<T,> fmt::Debug for FromTry<T,> {
  #[inline]
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result { write!(fmt, stringify!(FromTry<T,>,),) }
}

impl<T,> FnOnce<(Result<T::Ok, T::Error>,)> for FromTry<T,>
  where T: Try, {
  type Output = T;

  #[inline]
  extern "rust-call" fn call_once(self, (r,): (Result<T::Ok, T::Error>,),) -> Self::Output { Self::from_try(r,) }
}

impl<T,> FnMut<(Result<T::Ok, T::Error>,)> for FromTry<T,>
  where T: Try, {
  #[inline]
  extern "rust-call" fn call_mut(&mut self, (r,): (Result<T::Ok, T::Error>,),) -> Self::Output { Self::from_try(r,) }
}

impl<T,> Fn<(Result<T::Ok, T::Error>,)> for FromTry<T,>
  where T: Try, {
  #[inline]
  extern "rust-call" fn call(&self, (r,): (Result<T::Ok, T::Error>,),) -> Self::Output { Self::from_try(r,) }
}

/// A function which pairs its internal value with the input.
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(Join(42)("dropped"), (42, "dropped"));
/// ```
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Debug,)]
pub struct Join<A,>(pub A,);

impl<A,> Join<A,> {
  /// Constructs a new `Join` from `a`.
  #[inline]
  pub const fn new(a: A,) -> Self { Join(a,) }
}

impl<A, B,> FnOnce<(B,)> for Join<A,> {
  type Output = (A, B,);

  #[inline]
  extern "rust-call" fn call_once(self, (b,): (B,),) -> Self::Output { (self.0, b,) }
}

impl<A, B,> FnMut<(B,)> for Join<A,>
  where A: Clone, {
  #[inline]
  extern "rust-call" fn call_mut(&mut self, (b,): (B,),) -> Self::Output { (self.0.clone(), b,) }
}

impl<A, B,> Fn<(B,)> for Join<A,>
  where A: Clone, {
  #[inline]
  extern "rust-call" fn call(&self, (b,): (B,),) -> Self::Output { (self.0.clone(), b,) }
}

/// A function which wraps two inputs in a tuple or one input in a [`Join`](self::Join).
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(Pair(42)("dropped"), (42, "dropped"));
/// assert_eq!(Pair(42, "dropped"), (42, "dropped"));
/// ```
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Debug,)]
pub struct Pair;

impl Pair {
  /// Wraps the input in a `Join`.
  #[inline]
  pub const fn pair<A,>(a: A,) -> Join<A,> { Join(a,) }
}

impl<A,> FnOnce<(A,)> for Pair {
  type Output = Join<A,>;

  #[inline]
  extern "rust-call" fn call_once(self, (a,): (A,),) -> Self::Output { Join(a,) }
}

impl<A,> FnMut<(A,)> for Pair {
  #[inline]
  extern "rust-call" fn call_mut(&mut self, (a,): (A,),) -> Self::Output { Join(a,) }
}

impl<A,> Fn<(A,)> for Pair {
  #[inline]
  extern "rust-call" fn call(&self, (a,): (A,),) -> Self::Output { Join(a,) }
}

impl<A, B,> FnOnce<(A, B,)> for Pair {
  type Output = (A, B,);

  #[inline]
  extern "rust-call" fn call_once(self, t: (A, B,),) -> Self::Output { t }
}

impl<A, B,> FnMut<(A, B,)> for Pair {
  #[inline]
  extern "rust-call" fn call_mut(&mut self, t: (A, B,),) -> Self::Output { t }
}

impl<A, B,> Fn<(A, B,)> for Pair {
  #[inline]
  extern "rust-call" fn call(&self, t: (A, B,),) -> Self::Output { t }
}

/// A function which wraps its inputs in a tuple.
/// 
/// ```
/// use combinators_rs::*;
/// 
/// assert_eq!(Tuple(1), (1,));
/// assert_eq!(Tuple(1, 2), (1, 2));
/// assert_eq!(Tuple(1, 2, 3), (1, 2, 3));
/// ```
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Debug,)]
pub struct Tuple;

impl<Args,> FnOnce<Args> for Tuple {
  type Output = Args;

  #[inline]
  extern "rust-call" fn call_once(self, args: Args,) -> Self::Output { args }
}

impl<Args,> FnMut<Args> for Tuple {
  #[inline]
  extern "rust-call" fn call_mut(&mut self, args: Args,) -> Self::Output { args }
}

impl<Args,> Fn<Args> for Tuple {
  #[inline]
  extern "rust-call" fn call(&self, args: Args,) -> Self::Output { args }
}

fn _assert_coerce_unsized(a: TryMap<&i32,>, b: TryMapErr<&i32,>, c: TryAndThen<&i32,>,) {
  let _: TryMap<&dyn Send,> = a;
  let _: TryMapErr<&dyn Send,> = b;
  let _: TryAndThen<&dyn Send,> = c;
}
