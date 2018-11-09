use gba_proc_macro::register_bit;

#[derive(Debug, Default)]
pub struct Demo(u16);

impl Demo {
  #[register_bit(read, write)]
  const FIRST: u16 = 0b1;
}

#[test]
fn test_first_bit() {
  let mut foo = Demo::default();
  assert!(foo.first(), false);
  foo.set_first(true);
  assert!(foo.first(), true);
}
