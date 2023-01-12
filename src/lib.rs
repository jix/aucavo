//! Aucavo is a computational group theory library for Rust.
//!
//! Currently an early work in progress.

#![deny(unsafe_op_in_unsafe_fn)]
#![warn(missing_docs)]
#![warn(clippy::undocumented_unsafe_blocks)]
#![allow(clippy::comparison_chain)]
#![allow(clippy::needless_range_loop)]

#[macro_use]
mod specialize;

pub mod as_slice;
pub mod bignum;
pub mod perm;
pub mod point;
pub mod rand;
