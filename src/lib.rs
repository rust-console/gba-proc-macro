#![allow(unused)]

// Note(Lokathor): this extern crate is necessary even in 2018 for whatever
// reason that I'm sure is stupid.
extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::{Group, Punct, Spacing, Span, TokenTree};
use quote::quote;
use std::collections::HashSet;
use syn::{
  parse::{Parse, ParseStream, Result},
  parse_macro_input, Expr, Ident, Token, Type,
};

struct BoolBits {
  wrapped_type: Type,
  entries: Vec<(u8, String)>,
}

impl Parse for BoolBits {
  fn parse(input: ParseStream) -> Result<Self> {
    let mut entries = vec![];
    //
    let wrapped_type: Type = input.parse()?;
    input.parse::<Token![,]>()?;
    let bit_entry_list: Group = input.parse()?;
    for tree in bit_entry_list.stream() {
      match tree {
        TokenTree::Group(bit_entry) => {
          let mut bit_entry_iter = bit_entry.stream().into_iter();
          let position: u8 = if let Some(tt) = bit_entry_iter.next() {
            match tt {
              TokenTree::Literal(l) => match format!("{}", l).parse::<u8>() {
                Ok(u) => u,
                Err(e) => {
                  return Err(syn::Error::new(l.span(), format!("Required u8 literal, got {}", l)));
                }
              },
              TokenTree::Group(g) => {
                return Err(syn::Error::new(g.span(), format!("Expected bit_position, got Group {}", g)));
              }
              TokenTree::Ident(i) => {
                return Err(syn::Error::new(i.span(), format!("Expected bit_position, got Ident {}", i)));
              }
              TokenTree::Punct(p) => {
                return Err(syn::Error::new(p.span(), format!("Expected bit_position, got Punct {}", p)));
              }
            }
          } else {
            return Err(syn::Error::new(
              bit_entry.span(),
              format!("Expected Group (bit_position, name), got an empty Group"),
            ));
          };
          let _comma: char = if let Some(tt) = bit_entry_iter.next() {
            match tt {
              TokenTree::Punct(p) => {
                if p.as_char() == ',' {
                  ','
                } else {
                  return Err(syn::Error::new(p.span(), format!("Expected Punct ',', got Punct {}", p)));
                }
              }
              TokenTree::Literal(l) => {
                return Err(syn::Error::new(l.span(), format!("Expected Punct ',', got Literal {}", l)));
              }
              TokenTree::Group(g) => {
                return Err(syn::Error::new(g.span(), format!("Expected Punct ',', got Group {}", g)));
              }
              TokenTree::Ident(i) => {
                return Err(syn::Error::new(i.span(), format!("Expected Punct ',', got Ident {}", i)));
              }
            }
          } else {
            return Err(syn::Error::new(
              bit_entry.span(),
              format!("Expected Group (bit_position, name), got a 1 item Group"),
            ));
          };
          let name: String = if let Some(tt) = bit_entry_iter.next() {
            match tt {
              TokenTree::Ident(i) => format!("{}", i),
              TokenTree::Punct(p) => {
                return Err(syn::Error::new(p.span(), format!("Expected Ident, got Punct {}", p)));
              }
              TokenTree::Literal(l) => {
                return Err(syn::Error::new(l.span(), format!("Expected Ident, got Literal {}", l)));
              }
              TokenTree::Group(g) => {
                return Err(syn::Error::new(g.span(), format!("Expected Ident, got Group {}", g)));
              }
            }
          } else {
            return Err(syn::Error::new(
              bit_entry.span(),
              format!("Expected Group (bit_position, name), got a 2 item Group"),
            ));
          };
          entries.push((position, name));
        }
        TokenTree::Punct(p) => {
          // we just eat as many commas as we see, it's probably not important
          // that they alternate the captured groups
          if p.as_char() == ',' {
            continue;
          } else {
            return Err(syn::Error::new(p.span(), format!("Expected (bit_position, name), got Punct {}", p)));
          }
        }
        TokenTree::Ident(i) => return Err(syn::Error::new(i.span(), format!("Expected (bit_position, name), got Ident {}", i))),
        TokenTree::Literal(l) => return Err(syn::Error::new(l.span(), format!("Expected (bit_position, name), got Literal {}", l))),
      }
    }
    Ok(BoolBits { wrapped_type, entries })
  }
}

/// Generates one or more virtual bool fields within a type.
///
/// You must use this within an `impl` block for a tuple struct that has an
/// integral type as the 0th field.
///
/// Give the type of `self.0`, a comma, and then a Group, which itself contains
/// comma separated Group values, each of which should be formatted as `(bit,
/// field_name)`, no more than one per bit. Something like this:
///
/// ```txt
/// impl Demo {
///   bool_bits!(
///     u16,
///     [
///       (3, cgb_mode),
///       (4, page1_enabled),
///       (5, hblank_interval_free),
///       (6, object_memory_1d),
///       (7, force_blank),
///       (8, display_bg0),
///       (9, display_bg1)
///     ]
///   );
/// }
/// ```
#[proc_macro]
pub fn bool_bits(input: TokenStream) -> TokenStream {
  let BoolBits { wrapped_type, entries } = parse_macro_input!(input as BoolBits);

  let mut bits: HashSet<u8> = HashSet::new();
  for entry in entries.iter() {
    let bit = entry.0;
    if bits.contains(&bit) {
      panic!("Can't list a bit more than once! Found repeats of {}", bit);
    } else {
      bits.insert(bit);
    }
  }

  let mut output = TokenStream::new();
  for (bit, name) in entries.into_iter() {
    let const_name = Ident::new(&name.to_uppercase(), Span::call_site());
    let read_name = Ident::new(&name.clone(), Span::call_site());
    let with_name = Ident::new(&format!("with_{}", name), Span::call_site());
    let more_tokens: TokenStream = TokenStream::from(quote! {

      #[allow(missing_docs)]
      #[allow(clippy::identity_op)]
      pub const #const_name: #wrapped_type = 1 << #bit;

      #[allow(missing_docs)]
      pub const fn #read_name(self) -> bool {
        (self.0 & Self::#const_name) != 0
      }

      // https://graphics.stanford.edu/~seander/bithacks.html#ConditionalSetOrClearBitsWithoutBranching
      #[allow(missing_docs)]
      pub const fn #with_name(self, bit: bool) -> Self {
        Self(self.0 ^ (((#wrapped_type::wrapping_sub(0, bit as #wrapped_type) ^ self.0) & Self::#const_name)))
      }

    });
    output.extend(more_tokens);
  }
  output
}

//
// Multi Bit Fields
//

struct WrappedEntry {
  base: u8,
  width: u8,
  name: String,
}

struct EnumEntry {
  base: u8,
  width: u8,
  name: String,
  enum_type: String,
  variant_list: Vec<String>,
}

enum MultiBitEntry {
  Wrapped(WrappedEntry),
  Enum(EnumEntry),
}

struct MultiBitFields {
  wrapped_type: Type,
  entries: Vec<MultiBitEntry>,
}

impl Parse for MultiBitFields {
  fn parse(input: ParseStream) -> Result<Self> {
    let mut entries = vec![];
    //
    let wrapped_type: Type = input.parse()?;
    input.parse::<Token![,]>()?;
    let bit_entry_list: Group = input.parse()?;
    for tree in bit_entry_list.stream() {
      match tree {
        TokenTree::Group(bit_entry) => {
          let mut bit_entry_iter = bit_entry.stream().into_iter();
          let base: u8 = if let Some(tt) = bit_entry_iter.next() {
            match tt {
              TokenTree::Literal(l) => match format!("{}", l).parse::<u8>() {
                Ok(u) => u,
                Err(e) => {
                  return Err(syn::Error::new(l.span(), format!("Required u8 literal, got {}", l)));
                }
              },
              TokenTree::Group(g) => {
                return Err(syn::Error::new(g.span(), format!("Expected base, got Group {}", g)));
              }
              TokenTree::Ident(i) => {
                return Err(syn::Error::new(i.span(), format!("Expected base, got Ident {}", i)));
              }
              TokenTree::Punct(p) => {
                return Err(syn::Error::new(p.span(), format!("Expected base, got Punct {}", p)));
              }
            }
          } else {
            return Err(syn::Error::new(
              bit_entry.span(),
              format!("Expected multi-bit spec (min of 3), got an empty Group"),
            ));
          };
          let _comma: char = if let Some(tt) = bit_entry_iter.next() {
            match tt {
              TokenTree::Punct(p) => {
                if p.as_char() == ',' {
                  ','
                } else {
                  return Err(syn::Error::new(p.span(), format!("Expected Punct ',', got Punct {}", p)));
                }
              }
              TokenTree::Literal(l) => {
                return Err(syn::Error::new(l.span(), format!("Expected Punct ',', got Literal {}", l)));
              }
              TokenTree::Group(g) => {
                return Err(syn::Error::new(g.span(), format!("Expected Punct ',', got Group {}", g)));
              }
              TokenTree::Ident(i) => {
                return Err(syn::Error::new(i.span(), format!("Expected Punct ',', got Ident {}", i)));
              }
            }
          } else {
            return Err(syn::Error::new(
              bit_entry.span(),
              format!("Expected multi-bit spec (min of 3), got a 1 item Group"),
            ));
          };
          let width: u8 = if let Some(tt) = bit_entry_iter.next() {
            match tt {
              TokenTree::Literal(l) => match format!("{}", l).parse::<u8>() {
                Ok(u) => u,
                Err(e) => {
                  return Err(syn::Error::new(l.span(), format!("Required u8 literal, got {}", l)));
                }
              },
              TokenTree::Group(g) => {
                return Err(syn::Error::new(g.span(), format!("Expected width, got Group {}", g)));
              }
              TokenTree::Ident(i) => {
                return Err(syn::Error::new(i.span(), format!("Expected width, got Ident {}", i)));
              }
              TokenTree::Punct(p) => {
                return Err(syn::Error::new(p.span(), format!("Expected width, got Punct {}", p)));
              }
            }
          } else {
            return Err(syn::Error::new(
              bit_entry.span(),
              format!("Expected multi-bit spec (min of 3), got a 1 item Group"),
            ));
          };
          let _comma: char = if let Some(tt) = bit_entry_iter.next() {
            match tt {
              TokenTree::Punct(p) => {
                if p.as_char() == ',' {
                  ','
                } else {
                  return Err(syn::Error::new(p.span(), format!("Expected Punct ',', got Punct {}", p)));
                }
              }
              TokenTree::Literal(l) => {
                return Err(syn::Error::new(l.span(), format!("Expected Punct ',', got Literal {}", l)));
              }
              TokenTree::Group(g) => {
                return Err(syn::Error::new(g.span(), format!("Expected Punct ',', got Group {}", g)));
              }
              TokenTree::Ident(i) => {
                return Err(syn::Error::new(i.span(), format!("Expected Punct ',', got Ident {}", i)));
              }
            }
          } else {
            return Err(syn::Error::new(
              bit_entry.span(),
              format!("Expected multi-bit spec (min of 3), got a 2 item Group"),
            ));
          };
          let name: String = if let Some(tt) = bit_entry_iter.next() {
            match tt {
              TokenTree::Ident(i) => format!("{}", i),
              TokenTree::Punct(p) => {
                return Err(syn::Error::new(p.span(), format!("Expected Ident, got Punct {}", p)));
              }
              TokenTree::Literal(l) => {
                return Err(syn::Error::new(l.span(), format!("Expected Ident, got Literal {}", l)));
              }
              TokenTree::Group(g) => {
                return Err(syn::Error::new(g.span(), format!("Expected Ident, got Group {}", g)));
              }
            }
          } else {
            return Err(syn::Error::new(
              bit_entry.span(),
              format!("Expected multi-bit spec (min of 3), got a 2 item Group"),
            ));
          };
          let enum_comma: bool = if let Some(tt) = bit_entry_iter.next() {
            match tt {
              TokenTree::Punct(p) => true,
              TokenTree::Literal(l) => {
                return Err(syn::Error::new(l.span(), format!("Expected Punct ',' or End, got Literal {}", l)));
              }
              TokenTree::Group(g) => {
                return Err(syn::Error::new(g.span(), format!("Expected Punct ',' or End, got Group {}", g)));
              }
              TokenTree::Ident(i) => {
                return Err(syn::Error::new(i.span(), format!("Expected Punct ',' or End, got Ident {}", i)));
              }
            }
          } else {
            false
          };
          if enum_comma {
            // read the enum
            let enum_type: String = if let Some(tt) = bit_entry_iter.next() {
              match tt {
                TokenTree::Ident(i) => format!("{}", i),
                TokenTree::Punct(p) => {
                  return Err(syn::Error::new(p.span(), format!("Expected Ident, got Punct {}", p)));
                }
                TokenTree::Literal(l) => {
                  return Err(syn::Error::new(l.span(), format!("Expected Ident, got Literal {}", l)));
                }
                TokenTree::Group(g) => {
                  return Err(syn::Error::new(g.span(), format!("Expected Ident, got Group {}", g)));
                }
              }
            } else {
              return Err(syn::Error::new(
                bit_entry.span(),
                format!("Expected enum type name after trailing comma, found none"),
              ));
            };
            // begin reading accepted variants, in order
            let mut variant_list = vec![];
            'tag_gather_loop: loop {
              let _comma: char = if let Some(tt) = bit_entry_iter.next() {
                match tt {
                  TokenTree::Punct(p) => {
                    if p.as_char() == ',' {
                      ','
                    } else {
                      return Err(syn::Error::new(p.span(), format!("Expected Punct ',', got Punct {}", p)));
                    }
                  }
                  TokenTree::Literal(l) => {
                    return Err(syn::Error::new(l.span(), format!("Expected Punct ',', got Literal {}", l)));
                  }
                  TokenTree::Group(g) => {
                    return Err(syn::Error::new(g.span(), format!("Expected Punct ',', got Group {}", g)));
                  }
                  TokenTree::Ident(i) => {
                    return Err(syn::Error::new(i.span(), format!("Expected Punct ',', got Ident {}", i)));
                  }
                }
              } else {
                break 'tag_gather_loop;
              };
              let enum_tag: String = if let Some(tt) = bit_entry_iter.next() {
                match tt {
                  TokenTree::Ident(i) => format!("{}", i),
                  TokenTree::Punct(p) => {
                    return Err(syn::Error::new(p.span(), format!("Expected Ident, got Punct {}", p)));
                  }
                  TokenTree::Literal(l) => {
                    return Err(syn::Error::new(l.span(), format!("Expected Ident, got Literal {}", l)));
                  }
                  TokenTree::Group(g) => {
                    return Err(syn::Error::new(g.span(), format!("Expected Ident, got Group {}", g)));
                  }
                }
              } else {
                return Err(syn::Error::new(bit_entry.span(), format!("Expected enum tag after trailing comma")));
              };
              variant_list.push(enum_tag);
            }
            if variant_list.len() > 0 {
              entries.push(MultiBitEntry::Enum(EnumEntry {
                base,
                width,
                name,
                enum_type,
                variant_list,
              }));
            } else {
              return Err(syn::Error::new(Span::call_site(), "Enum tag list was missing!"));
            }
          } else {
            entries.push(MultiBitEntry::Wrapped(WrappedEntry { base, width, name }));
          }
        }
        TokenTree::Punct(p) => {
          // we just eat as many commas as we see, it's probably not important
          // that they alternate the captured groups
          if p.as_char() == ',' {
            continue;
          } else {
            return Err(syn::Error::new(p.span(), format!("Expected multi-bit spec or comma, got Punct {}", p)));
          }
        }
        TokenTree::Ident(i) => return Err(syn::Error::new(i.span(), format!("Expected multi-bit spec or comma, got Ident {}", i))),
        TokenTree::Literal(l) => return Err(syn::Error::new(l.span(), format!("Expected multi-bit spec or comma, got Literal {}", l))),
      }
    }
    Ok(MultiBitFields { wrapped_type, entries })
  }
}

/// Generates one or more virtual multi-bit fields within a type.
///
/// You must use this within an `impl` block for a tuple struct that has an
/// integral type as the 0th field.
///
/// * Each virtual field has a base position and width.
/// * Each virtual field is either of the 0th field integral type OR a specified
///   enum type which must have a repr that matches the 0th field type.
///
/// Specify the type of the 0th tuple field, a comma, and then a Group. The
/// Group must contain a comma separated list of Group values that each specify
/// one field.
///
/// The specification is one of:
///
/// * `(base, width, name)`
/// * `(base, width, name, EnumType, EnumTag1, EnumTagN...)`
///
/// With the Enum version, you must provide the tags in the order they should be
/// used. Even a proc-macro doesn't have the reflection required
///
/// Such as the following example:
///
/// ```txt
/// impl Demo {
///   multi_bits!(
///     u16,
///     [
///       (0, 2, priority),
///       (2, 2, cbb),
///       (8, 5, sbb),
///       (14, 2, size, SizeEnum, Small, Medium, Large),
///     ]
///   );
/// }
/// ```
#[proc_macro]
pub fn multi_bits(input: TokenStream) -> TokenStream {
  let MultiBitFields { wrapped_type, entries } = parse_macro_input!(input as MultiBitFields);

  let mut bits: HashSet<u8> = HashSet::new();
  for entry in entries.iter() {
    let (base, width): (u8, u8) = match entry {
      MultiBitEntry::Wrapped(WrappedEntry { base, width, .. }) => (*base, *width),
      MultiBitEntry::Enum(EnumEntry { base, width, .. }) => (*base, *width),
    };
    assert!(width > 0);

    for bit in base..width {
      if bits.contains(&bit) {
        panic!("Bit overlap found for bit {}", bit);
      } else {
        bits.insert(bit);
      }
    }
  }

  let mut output = TokenStream::new();
  for entry in entries.into_iter() {
    match entry {
      MultiBitEntry::Wrapped(WrappedEntry { base, width, name }) => {
        let mask_name = Ident::new(&format!("{}_MASK", name.to_uppercase()), Span::call_site());
        let read_name = Ident::new(&name.clone(), Span::call_site());
        let with_name = Ident::new(&format!("with_{}", name), Span::call_site());
        let more_tokens: TokenStream = TokenStream::from(quote! {

          #[allow(missing_docs)]
          #[allow(clippy::identity_op)]
          pub const #mask_name: #wrapped_type = ((1<<(#width))-1) << #base;

          #[allow(missing_docs)]
          pub const fn #read_name(self) -> #wrapped_type {
            (self.0 & Self::#mask_name) >> #base
          }

          #[allow(missing_docs)]
          pub const fn #with_name(self, #read_name: #wrapped_type) -> Self {
            Self((self.0 & !Self::#mask_name) | ((#read_name << #base) & Self::#mask_name))
          }

        });
        output.extend(more_tokens);
      }
      MultiBitEntry::Enum(EnumEntry {
        base,
        width,
        name,
        enum_type,
        variant_list,
      }) => {
        let mask_name = Ident::new(&format!("{}_MASK", name.to_uppercase()), Span::call_site());
        let read_name = Ident::new(&name.clone(), Span::call_site());
        let with_name = Ident::new(&format!("with_{}", name), Span::call_site());
        let enum_type_ident = Ident::new(&enum_type.clone(), Span::call_site());
        // add many, but not all, of our tokens
        let more_tokens: TokenStream = TokenStream::from(quote! {

          #[allow(missing_docs)]
          #[allow(clippy::identity_op)]
          pub const #mask_name: #wrapped_type = ((1<<(#width+1))-1) << #base;

          #[allow(missing_docs)]
          pub const fn #with_name(self, #read_name: #enum_type_ident) -> Self {
            Self((self.0 & !Self::#mask_name) | (((#read_name as #wrapped_type) << #base) & Self::#mask_name))
          }

          #[allow(missing_docs)]
          pub fn #read_name(self) -> #enum_type_ident
        });
        output.extend(more_tokens);
        // curly to enter a function, start the match
        let mut temp_string = "{".to_string();
        let tokens = TokenStream::from(quote! {

          match self.0 & Self::#mask_name

        });
        temp_string.push_str(&format!("{}", tokens));
        // curly to enter the match
        temp_string.push_str(" { ");
        // dump the match arms
        for i in 0..variant_list.len() {
          temp_string.push_str(&format!("\n{} => ", i));
          let enum_tag_ident = Ident::new(&variant_list[i].clone(), Span::call_site());
          let tokens = TokenStream::from(quote! {

            #enum_type_ident::#enum_tag_ident,

          });
          temp_string.push_str(&format!("{}", tokens));
        }
        // place the catch all arm
        if variant_list.len() == (1 << (width - 1)) {
          let tokens = TokenStream::from(quote! {

            _ => core::hint::unreachable_unchecked(),

          });
          temp_string.push_str(&format!("{}", tokens));
        } else {
          let tokens = TokenStream::from(quote! {

            _ => unreachable!(),

          });
          temp_string.push_str(&format!("{}", tokens));
        }
        // close those two unbalanced curly braces
        temp_string.push_str(" } } ");
        // push all that into the output
        use core::str::FromStr;
        let more_tokens: TokenStream = TokenStream::from_str(&temp_string).map_err(|e| panic!("{:?}", e)).unwrap();
        output.extend(more_tokens);
      }
    };
  }
  output
}
