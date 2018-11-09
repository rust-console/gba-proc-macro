use gba_proc_macro::register_bit;

#[derive(Debug, Default, Clone, Copy)]
#[repr(transparent)]
pub struct Demo(u16);

impl Demo {
  register_bit!(FIRST_BIT, u16, 0b1, first, read_write);
}

#[test]
fn test_first_bit() {
  assert_eq!(Demo::FIRST_BIT, 1u16);

  let mut foo = Demo::default();
  assert_eq!(foo.first(), false);

  foo.set_first(true);
  assert_eq!(foo.first(), true);
}
