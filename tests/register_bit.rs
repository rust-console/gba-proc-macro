#![feature(const_int_wrapping)]

use gba_proc_macro::*;

#[derive(Debug, Default, Clone, Copy)]
#[repr(transparent)]
pub struct Demo(u16);

impl Demo {
  register_bit!(FIRST_BIT, u16, 0b1, first);
}

#[test]
fn test_first_bit() {
  assert_eq!(Demo::FIRST_BIT, 1u16);

  let foo = Demo::default();
  assert_eq!(foo.first(), false);

  let foo_with_first = foo.with_first(true);
  assert_eq!(foo_with_first.first(), true);
}
