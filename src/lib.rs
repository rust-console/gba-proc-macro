extern crate proc_macro;

use self::proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::{parse_macro_input, Expr, Ident, Token, Type};

struct RegisterBit {
  const_name: Ident,
  const_value: Expr,
  const_type: Type,
  get_set_name: Ident,
  modes: Ident,
}

impl Parse for RegisterBit {
  fn parse(input: ParseStream) -> Result<Self> {
    let const_name: Ident = input.parse()?;
    input.parse::<Token![,]>()?;
    let const_type: Type = input.parse()?;
    input.parse::<Token![,]>()?;
    let const_value: Expr = input.parse()?;
    input.parse::<Token![,]>()?;
    let get_set_name: Ident = input.parse()?;
    input.parse::<Token![,]>()?;
    let modes: Ident = input.parse()?;
    Ok(RegisterBit {
      const_name,
      const_value,
      const_type,
      get_set_name,
      modes,
    })
  }
}

#[proc_macro]
pub fn register_bit(input: TokenStream) -> TokenStream {
  let RegisterBit {
    const_name,
    const_value,
    const_type,
    get_set_name,
    modes,
  } = parse_macro_input!(input as RegisterBit);

  let (read, write) = match modes.to_string().as_ref() {
    "read" => (true, false),
    "write" => (false, true),
    "read_write" => (true, true),
    _ => panic!(r#"Final arg must be one of "read", "write", or "read_write"."#),
  };

  let read_fn = if read {
    let read_name = get_set_name.clone();

    quote! {
      pub fn #read_name(&self) -> bool {
        (self.0 & Self::#const_name) != 0
      }
    }
  } else {
    quote!{}
  };

  let write_fn = if write {
    let write_name = Ident::new(&format!("set_{}", get_set_name), Span::call_site());

    quote! {
      pub fn #write_name(&mut self, bit: bool) {
        if bit {
          self.0 |= Self::#const_name;
        } else {
          self.0 &= !Self::#const_name;
        }
      }
    }
  } else {
    quote!{}
  };

  TokenStream::from(quote! {
    pub const #const_name: #const_type = #const_value;

    #read_fn

    #write_fn
  })
}
