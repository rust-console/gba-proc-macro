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
    Ok(RegisterBit {
      const_name,
      const_value,
      const_type,
      get_set_name,
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
  } = parse_macro_input!(input as RegisterBit);

  let read_fn = {
    let read_name = get_set_name.clone();

    quote! {
      pub fn #read_name(&self) -> bool {
        (self.0 & Self::#const_name) != 0
      }
    }
  };

  let write_fn = {
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
  };

  TokenStream::from(quote! {
    pub const #const_name: #const_type = #const_value;

    #read_fn

    #write_fn
  })
}

//////////

struct NewtypeDeclaration {
  newtype_name: Type,
  base_type: Type,
}

impl Parse for NewtypeDeclaration {
  fn parse(input: ParseStream) -> Result<Self> {
    let newtype_name: Type = input.parse()?;
    input.parse::<Token![,]>()?;
    let base_type: Type = input.parse()?;
    Ok(NewtypeDeclaration { newtype_name, base_type })
  }
}

#[proc_macro]
pub fn newtype(input: TokenStream) -> TokenStream {
  let NewtypeDeclaration { newtype_name, base_type } = parse_macro_input!(input as NewtypeDeclaration);

  TokenStream::from(quote! {
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
    #[repr(transparent)]
    pub struct #newtype_name(#base_type);
    impl From<#newtype_name> for #base_type {
      fn from(x: #newtype_name) -> #base_type {
        x.0
      }
    }
  })
}
