#![forbid(unsafe_code)]

//! `nb2nl` is a small crate for translating [NetsBlox](https://netsblox.org/) code into [Netlogo](https://ccl.northwestern.edu/netlogo/) source.
//! 
//! NetsBlox is a block-based programming environment based on [Snap!](https://snap.berkeley.edu/).
//! By using sprites and clones, NetsBlox can simulate complex multi-agent behavior; however, this is quite slow at scale.
//! Netlogo is a specialized tool for simulating relatively large multi-agent systems in a similar manner.
//! This crate serves as a translation bridge so that projects can be written in simple block-based NetsBlox code, but can be translated into and run by Netlogo.

#[macro_use] extern crate lalrpop_util;
#[macro_use] extern crate lazy_static;

pub mod xml2nl;
pub mod nl2xml;
mod util;
