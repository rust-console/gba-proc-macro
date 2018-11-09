extern crate proc_macro;

use self::proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use std::collections::HashSet;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{parse_macro_input, Ident, ItemConst, Token};

struct Args {
  read: bool,
  write: bool,
}

impl Parse for Args {
  fn parse(input: ParseStream) -> Result<Self> {
    let vars: HashSet<_> = Punctuated::<Ident, Token![,]>::parse_terminated(input)?.into_iter().collect();
    let read = vars.get(&Ident::new("read", Span::call_site())).map(|_| true).unwrap_or(false);
    let write = vars.get(&Ident::new("write", Span::call_site())).map(|_| true).unwrap_or(false);
    Ok(Args { read, write })
  }
}

#[proc_macro_attribute]
pub fn register_bit(args: TokenStream, input: TokenStream) -> TokenStream {
  let item = parse_macro_input!(input as ItemConst);
  let args = parse_macro_input!(args as Args);

  let item_name = &item.ident;

  let read_fn = if args.read {
    let name = item_name.to_string().to_lowercase();
    let name = Ident::new(&name, Span::call_site());

    quote! {
      pub fn #name(&self) -> bool {
        (self.0 & Self::#item_name) != 0
      }
    }
  } else {
    quote!{}
  };

  let write_fn = if args.write {
    let name = item_name.to_string().to_lowercase();
    let name = Ident::new(&format!("set_{}", name), Span::call_site());

    quote! {
      pub fn #name(&mut self, bit: bool) {
        if bit {
          self.0 |= Self::#item_name;
        } else {
          self.0 &= !Self::#item_name;
        }
      }
    }
  } else {
    quote!{}
  };

  TokenStream::from(quote! {
    #item

    #read_fn

    #write_fn
  })
}
