//! A framework for interacting with Wayland compositors from the client side.
//! 
//! # The Wayland Protocol
//! 
//! This module provides foundational tools for establishing and managing a Wayland client
//! connection. It includes functionality for connecting to the Wayland compositor using
//! environment variables, sending and receiving Wayland protocol messages, and handling global
//! objects.
//! 
//! The documentation for the Wayland protocol can be found
//! [here](https://wayland.freedesktop.org/docs/html/). You most likely won't need to use it
//! directly, so this is only for framework authors and contributors.
//! 
//! # Async Usage
//! 
//! This framework is asynchronous, unlike other implementations which use `calloop`. It relies
//! heavily on [`tokio`] and it does not support other runtimes by default.
//! 
//! # Establishing a Connection
//! 
//! Before you can interact with a Wayland compositor, you need to establish a connection. This is 
//! done using the [`Connection::from_env()`](connection::Connection::from_env) function, which
//! reads the necessary environment variables and establishes the connection automatically.
//! 
//! ```
//! use way::connection::Connection;
//! 
//! let conn = Connection::from_env().await.unwrap();
//! ```

pub mod connection;
pub mod globals;
pub mod messages;
