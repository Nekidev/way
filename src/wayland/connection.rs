//! A module for managing the Wayland connection.
//!
//! # The Connection Struct
//!
//! Establishing a connection to the Wayland compositor is quite simple with the [`Connection`]
//! struct. Underneath, it just wraps a Tokio [`UnixStream`] connected to the Wayland socket
//! prettily with some utilities on top, making it easier to work with Wayland in an async context.
//!
//! The [`Connection::from_env()`] method automatically reads the necessary environment variables
//! (`XDG_RUNTIME_DIR` and `WAYLAND_DISPLAY`) to determine the correct socket path and establishes
//! the connection for you.
//!
//! ```
//! let conn = Connection::from_env().await?;
//! ```
//!
//! That's it! You now have a connected Wayland client connection ready for use.
//!
//! # Error Handling
//!
//! The module defines a [`ConnectionError`] enum to handle common errors that may occur during
//! connection establishment, such as missing environment variables or connection failures. Only
//! three error types are defined:
//! * [`ConnectionError::XdgRuntimeDirNotSet`] - Indicates that the `XDG_RUNTIME_DIR` environment
//!   variable is not set.
//! * [`ConnectionError::ConnectionFailed`] - Indicates that the connection to the Wayland socket
//!   failed, wrapping the underlying I/O error.
//! * [`ConnectionError::MessageError`] - Indicates that there was an error while sending a Wayland
//!   message.

use std::{
    env::VarError,
    sync::atomic::{AtomicU32, Ordering},
};

use tokio::net::UnixStream;

use crate::wayland::messages::{IntoMessage, MessageError};

#[derive(Debug, thiserror::Error)]
pub enum ConnectionError {
    #[error("There was no XDG_RUNTIME_DIR set in the environment")]
    XdgRuntimeDirNotSet(#[from] VarError),

    #[error("Failed to connect to the Wayland compositor")]
    ConnectionFailed(#[from] std::io::Error),

    #[error(transparent)]
    MessageError(#[from] MessageError),
}

/// Wraps a connection to a Wayland compositor.
///
/// Internally, it's just a Tokio [`UnixStream`] connected to the Wayland socket, with
/// utilities for establishing the connection from environment variables.
///
/// Initialize a new connection using [`Connection::from_env()`].
pub struct Connection {
    stream: UnixStream,
    id_counter: AtomicU32,
}

impl Connection {
    /// Establishes a new Wayland connection using environment variables.
    ///
    /// This function reads the `XDG_RUNTIME_DIR` and `WAYLAND_DISPLAY` environment variables to
    /// determine the correct socket path and establishes the connection. Read [this module's
    /// documentation](self) for more details.
    ///
    /// Returns:
    /// * `Ok(Connection)` - A successfully established Wayland connection.
    /// * `Err(ConnectionError)` - An error occurred while trying to establish the connection.
    pub async fn from_env() -> Result<Self, ConnectionError> {
        let wayland_display = std::env::var("WAYLAND_DISPLAY").unwrap_or("wayland-0".to_string());

        // If WAYLAND_DISPLAY is an absolute path, use it directly. Otherwise, construct the socket
        // path using XDG_RUNTIME_DIR.
        let socket_path = if wayland_display.starts_with("/") {
            wayland_display
        } else {
            format!(
                "{}/{}",
                std::env::var("XDG_RUNTIME_DIR")?,
                std::env::var("WAYLAND_DISPLAY").unwrap_or("wayland-0".to_string())
            )
        };

        let stream = UnixStream::connect(socket_path).await?;

        Ok(Self {
            stream,
            id_counter: AtomicU32::new(1),
        })
    }

    /// Sends a Wayland message to the compositor.
    ///
    /// Arguments:
    /// * `message` - The message to send.
    ///
    /// Returns:
    /// * `Ok(())` - The message was sent successfully.
    /// * `Err(ConnectionError)` - An error occurred while sending the message.
    pub async fn send(&mut self, message: impl IntoMessage) -> Result<(), ConnectionError> {
        let message = message.into_message(|| self.id_counter.fetch_add(1, Ordering::SeqCst));

        message.write(&mut self.stream).await?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_connection_from_env() {
        Connection::from_env().await.unwrap();
    }
}
