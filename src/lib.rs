// Note(Lokathor): this extern crate is necessary even in 2018 for whatever
// reason that I'm sure is stupid.
extern crate proc_macro;
extern crate rand;

use core::str::FromStr;
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use rand::{Rng, SeedableRng};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};
use syn::{
  parse::{self, Parse, ParseStream, Result},
  parse_macro_input,
  spanned::Spanned,
  Attribute, Error, Ident, ItemFn, LitInt, ReturnType, Token, Type, TypePath, Visibility,
};

static CALL_COUNT: AtomicUsize = AtomicUsize::new(0);

// Phantom Fields

enum PhantomEntry {
  Enum {
    attributes: Vec<Attribute>,
    name: String,
    start: u64,
    end: u64,
    enum_type: Ident,
    variant_list: Vec<String>,
  },
  Integer {
    attributes: Vec<Attribute>,
    name: String,
    start: u64,
    end: u64,
  },
  Bool {
    attributes: Vec<Attribute>,
    name: String,
    bit: u64,
  },
}

struct PhantomFields {
  self_member_type: Type,
  entries: Vec<PhantomEntry>,
}

impl Parse for PhantomFields {
  fn parse(input: ParseStream) -> Result<Self> {
    let _ = input.parse::<Token![self]>()?;
    let _ = input.parse::<Token![.]>()?;
    let lit = input.parse::<LitInt>()?;
    if lit.value() != 0 {
      return Err(Error::new(lit.span(), "Currently only self.0 is supported"));
    }
    let _ = input.parse::<Token![:]>()?;
    let self_member_type: Type = {
      let tp = input.parse::<TypePath>()?;
      let tp_end_string = match tp.path.segments.last().expect("no type given") {
        syn::punctuated::Pair::Punctuated(path_segment, _colon2) => path_segment.ident.to_string(),
        syn::punctuated::Pair::End(path_segment) => path_segment.ident.to_string(),
      };
      match tp_end_string.as_ref() {
        "u8" | "i8" | "u16" | "i16" | "u32" | "i32" | "usize" | "isize" | "u64" | "i64" => Type::Path(tp),
        _ => {
          return Err(Error::new(tp.span(), format!("Unsupported target type: {:?}", tp_end_string)));
        }
      }
    };
    let _ = input.parse::<Token![,]>()?;
    //
    let mut entries: Vec<PhantomEntry> = vec![];
    'entry_loop: loop {
      if input.is_empty() {
        break;
      }
      let attributes = input.call(Attribute::parse_outer)?;
      let name = input.parse::<Ident>()?.to_string();
      let _ = input.parse::<Token![:]>()?;
      let start = input.parse::<LitInt>()?.value();
      let lookahead = input.lookahead1();
      if lookahead.peek(Token![,]) {
        // bool entry
        entries.push(PhantomEntry::Bool {
          attributes,
          name,
          bit: start,
        });
        let _ = input.parse::<Token![,]>()?;
        continue 'entry_loop;
      } else if lookahead.peek(Token![-]) {
        // spanning entry
        let _ = input.parse::<Token![-]>()?;
        let end = input.parse::<LitInt>()?.value();
        let lookahead = input.lookahead1();
        if lookahead.peek(Token![=]) {
          // enum span
          let _ = input.parse::<Token![=]>()?;
          let enum_type = input.parse::<Ident>()?;
          let mut variant_list = vec![];
          let _ = input.parse::<Token![<]>()?;
          'variant_gather_loop: loop {
            variant_list.push(input.parse::<Ident>()?.to_string());
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![>]) {
              // end of list
              let _ = input.parse::<Token![>]>()?;
              break 'variant_gather_loop;
            } else if lookahead.peek(Token![,]) {
              // more to gather
              let _ = input.parse::<Token![,]>()?;
              continue 'variant_gather_loop;
            } else {
              return Err(lookahead.error());
            }
          }
          entries.push(PhantomEntry::Enum {
            attributes,
            name,
            start,
            end,
            enum_type,
            variant_list,
          });
          let _ = input.parse::<Token![,]>()?;
          continue 'entry_loop;
        } else if lookahead.peek(Token![,]) {
          // int span
          entries.push(PhantomEntry::Integer {
            attributes,
            name,
            start,
            end,
          });
          let _ = input.parse::<Token![,]>()?;
          continue 'entry_loop;
        } else {
          return Err(lookahead.error());
        }
      } else {
        return Err(lookahead.error());
      }
    }
    Ok(PhantomFields { self_member_type, entries })
  }
}

#[proc_macro]
pub fn phantom_fields(input: TokenStream) -> TokenStream {
  let PhantomFields { self_member_type, entries } = parse_macro_input!(input as PhantomFields);

  let mut out_text = String::new();

  for entry in entries.into_iter() {
    match entry {
      PhantomEntry::Enum {
        attributes,
        name,
        start,
        end,
        enum_type,
        variant_list,
      } => {
        for attribute in attributes.into_iter() {
          out_text.push_str(&format!("{}\n", TokenStream::from(quote! { #attribute })));
        }
        let mask_name = Ident::new(&format!("{}_MASK", name.to_uppercase()), Span::call_site());
        let read_name = Ident::new(&name.clone(), Span::call_site());
        let with_name = Ident::new(&format!("with_{}", name), Span::call_site());
        let width = (end - start) + 1;
        out_text.push_str(&format!(
          "{}\n",
          TokenStream::from(quote! {
            #[allow(clippy::identity_op)]
            pub const #mask_name: #self_member_type = ((1<<(#width))-1) << #start;

            #[allow(missing_docs)]
            pub fn #read_name(self) -> #enum_type
          })
        ));
        out_text.push('{');
        out_text.push_str(&format!(
          "{}\n",
          TokenStream::from(quote! {
            match (self.0 & Self::#mask_name) >> #start
          })
        ));
        out_text.push('{');
        let enum_type_string = enum_type.to_string();
        for (i, variant) in variant_list.iter().enumerate() {
          out_text.push_str(&format!("{} => {}::{},\n", i, enum_type_string, variant));
        }
        if variant_list.len() == (1 << (width - 1)) {
          out_text.push_str("_ => core::hint::unreachable_unchecked(),");
        } else {
          out_text.push_str("_ => unreachable!(),");
        }
        out_text.push_str("} }\n");
        out_text.push_str(&format!(
          "{}\n",
          TokenStream::from(quote! {
            #[allow(missing_docs)]
            pub const fn #with_name(self, #read_name: #enum_type) -> Self {
              Self((self.0 & !Self::#mask_name) | (((#read_name as #self_member_type) << #start) & Self::#mask_name))
            }
          })
        ));
      }
      PhantomEntry::Integer {
        attributes,
        name,
        start,
        end,
      } => {
        for attribute in attributes.into_iter() {
          out_text.push_str(&format!("{}\n", TokenStream::from(quote! { #attribute })));
        }
        let mask_name = Ident::new(&format!("{}_MASK", name.to_uppercase()), Span::call_site());
        let read_name = Ident::new(&name.clone(), Span::call_site());
        let with_name = Ident::new(&format!("with_{}", name), Span::call_site());
        let width = (end - start) + 1;
        out_text.push_str(&format!(
          "{}\n",
          TokenStream::from(quote! {
            #[allow(clippy::identity_op)]
            pub const #mask_name: #self_member_type = ((1<<(#width))-1) << #start;

            #[allow(missing_docs)]
            pub const fn #read_name(self) -> #self_member_type {
              (self.0 & Self::#mask_name) >> #start
            }

            #[allow(missing_docs)]
            pub const fn #with_name(self, #read_name: #self_member_type) -> Self {
              Self((self.0 & !Self::#mask_name) | ((#read_name << #start) & Self::#mask_name))
            }
          })
        ));
      }
      PhantomEntry::Bool { attributes, name, bit } => {
        for attribute in attributes.into_iter() {
          out_text.push_str(&format!("{}\n", TokenStream::from(quote! { #attribute })));
        }
        let const_name = Ident::new(&format!("{}_BIT", name.to_uppercase()), Span::call_site());
        let read_name = Ident::new(&name.clone(), Span::call_site());
        let with_name = Ident::new(&format!("with_{}", name), Span::call_site());
        out_text.push_str(&format!(
          "{}\n",
          TokenStream::from(quote! {
            #[allow(clippy::identity_op)]
            pub const #const_name: #self_member_type = 1 << #bit;

            #[allow(missing_docs)]
            pub const fn #read_name(self) -> bool {
              (self.0 & Self::#const_name) != 0
            }

            // https://graphics.stanford.edu/~seander/bithacks.html#ConditionalSetOrClearBitsWithoutBranching
            #[allow(missing_docs)]
            pub const fn #with_name(self, bit: bool) -> Self {
              Self(self.0 ^ (((#self_member_type::wrapping_sub(0, bit as #self_member_type) ^ self.0) & Self::#const_name)))
            }
          })
        ));
      }
    };
  }

  TokenStream::from_str(&out_text).map_err(|e| panic!("{:?}", e)).unwrap()
}

/// Attribute to declare the entry point of the program.
///
/// **IMPORTANT**: This attribute must appear exactly *once* in the dependency graph.  Also, if you
/// are using Rust 1.30 the attribute must be used on a reachable item (i.e. there must be no
/// private modules between the item and the root of the crate); if the item is in the root of the
/// crate you'll be fine.  This reachability restriction doesn't apply to Rust 1.31 onwards.
///
/// The specified function will be called by the crt0 *after* RAM has been initialized.  It must
/// take no arguments, and must be divergent (in other words, its type must be either `fn() -> !`
/// or `unsafe fn() -> !`).  The program can't reference the entry point, much less invoke it.
///
/// # Example
///
/// ``` no_run
/// # #![no_main]
/// # use gba_proc_macro::entry;
/// #[entry]
/// fn main() -> ! {
///     loop {
///         /* .. */
///     }
/// }
/// ```
#[proc_macro_attribute]
pub fn entry(args: TokenStream, input: TokenStream) -> TokenStream {
  let f = parse_macro_input!(input as ItemFn);

  // check the function signature
  let valid_signature = f.constness.is_none()
    && f.vis == Visibility::Inherited
    && f.abi.is_none()
    && f.decl.inputs.is_empty()
    && f.decl.generics.params.is_empty()
    && f.decl.generics.where_clause.is_none()
    && f.decl.variadic.is_none()
    && match f.decl.output {
      ReturnType::Default => false,
      ReturnType::Type(_, ref ty) => match **ty {
        Type::Never(_) => true,
        _ => false,
      },
    };

  if !valid_signature {
    return parse::Error::new(f.span(), "`#[entry]` function must have signature `[unsafe] fn() -> !`")
      .to_compile_error()
      .into();
  }

  if !args.is_empty() {
    return parse::Error::new(Span::call_site(), "This attribute accepts no arguments")
      .to_compile_error()
      .into();
  }

  // XXX should we blacklist other attributes?
  let attrs = f.attrs;
  let block = f.block;
  let hash = random_ident();
  let unsafety = f.unsafety;

  quote!(
      #[export_name = "main"]
      #(#attrs)*
      pub #unsafety fn #hash() -> ! #block
  )
  .into()
}

// Creates a random identifier
fn random_ident() -> Ident {
  let secs = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();

  let count: u64 = CALL_COUNT.fetch_add(1, Ordering::SeqCst) as u64;
  let mut seed: [u8; 16] = [0; 16];

  for (i, v) in seed.iter_mut().take(8).enumerate() {
    *v = ((secs >> (i * 8)) & 0xFF) as u8
  }

  for (i, v) in seed.iter_mut().skip(8).enumerate() {
    *v = ((count >> (i * 8)) & 0xFF) as u8
  }

  let mut rng = rand::rngs::SmallRng::from_seed(seed);
  Ident::new(
    &(0..16)
      .map(|i| {
        if i == 0 || rng.gen() {
          ('a' as u8 + rng.gen::<u8>() % 25) as char
        } else {
          ('0' as u8 + rng.gen::<u8>() % 10) as char
        }
      })
      .collect::<String>(),
    Span::call_site(),
  )
}
