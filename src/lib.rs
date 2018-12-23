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
      pub const fn #read_name(&self) -> bool {
        (self.0 & Self::#const_name) != 0
      }
    }
  };

  let write_fn = {
    let write_name = Ident::new(&format!("with_{}", get_set_name), Span::call_site());

    // https://graphics.stanford.edu/~seander/bithacks.html#ConditionalSetOrClearBitsWithoutBranching
    quote! {
      pub const fn #write_name(self, bit: bool) -> Self {
        Self(self.0 ^ (((#const_type::wrapping_sub(0, bit as #const_type) ^ self.0) & #const_value)))
      }
    }
  };

  TokenStream::from(quote! {
    pub const #const_name: #const_type = #const_value;

    #read_fn

    #write_fn
  })
}

//

/*

// this is a macro_rules macro for now.

struct NewtypeDeclaration {
  newtype_name: Type,
  base_type: Type,
  doc_comments: LitStr,
}

impl Parse for NewtypeDeclaration {
  fn parse(input: ParseStream) -> Result<Self> {
    let newtype_name: Type = input.parse()?;
    input.parse::<Token![,]>()?;
    let base_type: Type = input.parse()?;
    let doc_comments: LitStr = if input.is_empty() {
      LitStr::new("", Span::call_site())
    } else {
      input.parse::<Token![,]>()?;
      input.parse()?
    };
    Ok(NewtypeDeclaration {
      newtype_name,
      base_type,
      doc_comments,
    })
  }
}

#[proc_macro]
pub fn newtype(input: TokenStream) -> TokenStream {
  let NewtypeDeclaration {
    newtype_name,
    base_type,
    doc_comments,
  } = parse_macro_input!(input as NewtypeDeclaration);

  TokenStream::from(quote! {
    #[doc = #doc_comments]
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
*/
