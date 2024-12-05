#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub mod _module {
  pub struct _default {}

  impl _default {
    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
      ::dafny_runtime::allocate_object::<Self>()
    }
    pub fn add(x: &::dafny_runtime::DafnyInt, y: &::dafny_runtime::DafnyInt) -> super::_module::memcalcret<::dafny_runtime::DafnyInt> {
      x.clone() + y.clone()
    }
    pub fn apply<_t: ::dafny_runtime::DafnyType + ::std::default::Default + ::std::default::Default>(f: &::std::rc::Rc<dyn ::std::ops::Fn(&_t, &_t) -> super::_module::memcalcret<_t>>, x: &_t, y: &_t) -> _t {
      let mut z = ::dafny_runtime::MaybePlacebo::<_t>::new();
      z = ::dafny_runtime::MaybePlacebo::from(f(x, y));
      return z.read();
    }
    pub fn main(x: &::dafny_runtime::DafnyInt, y: &::dafny_runtime::DafnyInt) -> () {
      let mut v = ::dafny_runtime::MaybePlacebo::<::dafny_runtime::DafnyInt>::new();
      let mut _out0 = ::dafny_runtime::MaybePlacebo::<::dafny_runtime::DafnyInt>::new();
      _out0 = ::dafny_runtime::MaybePlacebo::from(super::_module::_default::apply::<::dafny_runtime::DafnyInt>(&(::std::rc::Rc::new(super::_module::_default::add) as ::std::rc::Rc<dyn ::std::ops::Fn(&_, &_) -> _>), x, y));
      v = ::dafny_runtime::MaybePlacebo::from(_out0.read());
      print!("{}", ::dafny_runtime::DafnyPrintWrapper(&v.read()));
      return ();
    }
  }

  impl ::dafny_runtime::UpcastObject<dyn ::std::any::Any>
    for super::_module::_default {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
  }

  pub type memcalcret<t: ::dafny_runtime::DafnyType + ::std::default::Default> = t;
}