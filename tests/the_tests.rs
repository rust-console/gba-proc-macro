#![feature(const_int_wrapping)]

use gba_proc_macro::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum DisplayMode {
  Mode0 = 0,
  Mode1 = 1,
  Mode2 = 2,
}

#[derive(Debug, Default, Clone, Copy)]
#[repr(transparent)]
pub struct PhantomFieldsDemo(u32);

impl PhantomFieldsDemo {
  phantom_fields! {
    self.0: u32,
    /// enum_example docs
    enum_example: 0-2=DisplayMode<Mode0, Mode1, Mode2>,
    bool_example: 3,
    int_example: 6-7,
    enum_example2: 10-12=DisplayMode<Mode0, Mode1, Mode2>,
  }
}

#[test]
fn enum_example_test() {
  assert_eq!(PhantomFieldsDemo::ENUM_EXAMPLE_MASK, 0b111);
  for &dm in [DisplayMode::Mode0, DisplayMode::Mode1, DisplayMode::Mode2].iter() {
    assert_eq!(PhantomFieldsDemo(dm as u32).enum_example(), dm);
    assert_eq!(PhantomFieldsDemo(0).with_enum_example(dm).enum_example(), dm);
  }
}

#[test]
fn bool_example_test() {
  assert_eq!(PhantomFieldsDemo::BOOL_EXAMPLE_BIT, 1 << 3);
  assert!(!PhantomFieldsDemo(0).bool_example());
  assert!(PhantomFieldsDemo(PhantomFieldsDemo::BOOL_EXAMPLE_BIT).bool_example());
  assert!(PhantomFieldsDemo(0).with_bool_example(true).bool_example());
}

#[test]
fn int_example_test() {
  assert_eq!(PhantomFieldsDemo::INT_EXAMPLE_MASK, 0b11 << 6);
  assert_eq!(PhantomFieldsDemo(0).int_example(), 0);
  assert_eq!(PhantomFieldsDemo(PhantomFieldsDemo::INT_EXAMPLE_MASK).int_example(), 0b11);
  for i in 0..=0b11 {
    assert_eq!(PhantomFieldsDemo(0).with_int_example(i).int_example(), i);
  }
}

#[test]
fn enum_example2_test() {
  assert_eq!(PhantomFieldsDemo::ENUM_EXAMPLE2_MASK, 0b111 << 10);
  for &dm in [DisplayMode::Mode0, DisplayMode::Mode1, DisplayMode::Mode2].iter() {
    assert_eq!(PhantomFieldsDemo((dm as u32) << 10).enum_example2(), dm);
    assert_eq!(PhantomFieldsDemo(0).with_enum_example2(dm).enum_example2(), dm);
  }
}
