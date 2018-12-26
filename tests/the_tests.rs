#![feature(const_int_wrapping)]

use gba_proc_macro::*;

#[derive(Debug, Default, Clone, Copy)]
#[repr(transparent)]
pub struct BoolBitsDemo(u16);

impl BoolBitsDemo {
  bool_bits!(
    u16,
    [
      (3, cgb_mode),
      (4, page1_enabled),
      (5, hblank_interval_free),
      (6, object_memory_1d),
      (7, force_blank),
      (8, display_bg0),
      (9, display_bg1)
    ]
  );
}

#[test]
fn test_bool_bits() {
  // test our bit constant
  assert_eq!(BoolBitsDemo::CGB_MODE, 1 << 3);

  let foo = BoolBitsDemo::default();
  assert_eq!(foo.cgb_mode(), false);

  // test writing and reading
  let foo_with_cgb = foo.with_cgb_mode(true);
  assert_eq!(foo_with_cgb.cgb_mode(), true);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum SizeEnum {
  Small,
  Medium,
  Large,
}

#[derive(Debug, Default, Clone, Copy)]
#[repr(transparent)]
pub struct MultiBitsDemo(u16);

impl MultiBitsDemo {
  multi_bits!(
    u16,
    [
      (0, 2, priority),
      (2, 2, cbb),
      (8, 5, sbb),
      (14, 2, the_size, SizeEnum, Small, Medium, Large)
    ]
  );
}

#[test]
fn test_multi_bits() {
  // check mask creation
  assert_eq!(MultiBitsDemo::CBB_MASK, 0b11 << 2);

  let foo = MultiBitsDemo::default();
  assert_eq!(foo.cbb(), 0);

  // check writing and reading
  let foo_with_cbb = foo.with_cbb(3);
  assert_eq!(foo_with_cbb.cbb(), 3);

  // check overflows are masked properly
  let foo_with_cbb2 = foo.with_cbb(5);
  assert_eq!(foo_with_cbb2.cbb(), 1);

  // check enum write and read
  let foo_with_size = foo.with_the_size(SizeEnum::Medium);
  assert_eq!(foo_with_size.the_size(), SizeEnum::Medium);
}
