//! A module for parsing and encoding Wayland protocol messages.

use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::UnixStream,
};
use tokio_byteorder::{AsyncReadBytesExt, AsyncWriteBytesExt, NativeEndian};

#[derive(Debug, thiserror::Error)]
pub enum MessageError {
    #[error("Failed to read from or to write to the Wayland connection")]
    IoFailed(#[from] std::io::Error),

    #[error("The Wayland message received from the compositor is invalid: {0}")]
    InvalidMessage(String),
}

/// Represents a Wayland protocol message.
pub struct Message {
    pub object_id: u32,
    pub opcode: u16,
    pub arguments: Vec<u8>,
}

impl Message {
    /// Reads a Wayland message from the given [`UnixStream`].
    ///
    /// Arguments:
    /// * `stream` - The UnixStream to read the message from.
    ///
    /// Returns:
    /// * `Ok(Message)` - The successfully read Wayland message.
    /// * `Err(MessageError)` - An error occurred while reading the message.
    pub async fn read(stream: &mut UnixStream) -> Result<Self, MessageError> {
        let object_id = AsyncReadBytesExt::read_u32::<NativeEndian>(stream).await?;
        let opcode = AsyncReadBytesExt::read_u16::<NativeEndian>(stream).await?;
        let size = AsyncReadBytesExt::read_u16::<NativeEndian>(stream).await?;

        if size < 8 {
            return Err(MessageError::InvalidMessage(format!(
                "The message size in the message header ({size} bytes) is less than the header's own size (8 bytes), which is the minimum allowed."
            )));
        }

        let arguments_size = size as usize - 8;
        let mut arguments = vec![0u8; arguments_size];

        stream.read_exact(&mut arguments).await?;

        Ok(Message {
            object_id,
            opcode,
            arguments,
        })
    }

    /// Writes the Wayland message to the given [`UnixStream`].
    ///
    /// Arguments:
    /// * `stream` - The UnixStream to write the message to.
    ///
    /// Returns:
    /// * `Ok(())` - The message was successfully written.
    /// * `Err(MessageError)` - An error occurred while writing the message.
    pub async fn write(&self, stream: &mut UnixStream) -> Result<(), MessageError> {
        AsyncWriteBytesExt::write_u32::<NativeEndian>(stream, self.object_id).await?;
        AsyncWriteBytesExt::write_u16::<NativeEndian>(stream, self.opcode).await?;

        let size = (8 + self.arguments.len()) as u16;
        AsyncWriteBytesExt::write_u16::<NativeEndian>(stream, size).await?;

        stream.write_all(&self.arguments).await?;

        Ok(())
    }
}

/// Represents a Wayland protocol message without an associated object ID.
///
/// The message ID will be automatically assigned by the
/// [`Connection`](super::connection::Connection) when it's sent.
pub struct AnonymousMessage {
    pub opcode: u16,
    pub arguments: Vec<u8>,
}

pub trait IntoMessage {
    fn into_message(self, id_generator: impl Fn() -> u32) -> Message;
}

impl IntoMessage for AnonymousMessage {
    fn into_message(self, id_generator: impl Fn() -> u32) -> Message {
        Message {
            object_id: id_generator(),
            opcode: self.opcode,
            arguments: self.arguments,
        }
    }
}

/// A Wayland 24.8 fixed-point number.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fixed(i32);

impl Fixed {
    /// Convert the fixed-point value to f64.
    ///
    /// Returns:
    /// * `f64` - The converted floating-point value.
    pub fn to_f64(self) -> f64 {
        self.0 as f64 / 256.0
    }

    /// Convert the fixed-point value to f32.
    ///
    /// Returns:
    /// * `f32` - The converted floating-point value.
    pub fn to_f32(self) -> f32 {
        self.0 as f32 / 256.0
    }

    /// Create a Fixed from an f64.
    ///
    /// Returns:
    /// * `Fixed` - The created fixed-point value.
    pub fn from_f64(val: f64) -> Self {
        Fixed((val * 256.0).round() as i32)
    }

    /// Create a Fixed from an f32.
    ///
    /// Returns:
    /// * `Fixed` - The created fixed-point value.
    pub fn from_f32(val: f32) -> Self {
        Fixed((val * 256.0).round() as i32)
    }

    /// Access the raw underlying i32.
    ///
    /// Returns:
    /// * `i32` - The raw fixed-point value.
    pub fn raw(self) -> i32 {
        self.0
    }
}

/// A Wayland object ID.
pub struct ObjectId(u32);

/// A new Wayland object ID to be assigned before use.
///
/// This is automatically generated when sending messages that create new objects if not fixed.
pub enum NewObjectId {
    /// Automatically generate a new object ID.
    Auto,

    /// Use the specified fixed object ID.
    Fixed(u32),
}

trait ParseArgument: Sized {
    /// Parses the argument from the given byte slice and returns the parsed argument with the
    /// remaining data.
    ///
    /// Arguments:
    /// * `data` - The byte slice to parse the argument from.
    ///
    /// Returns:
    /// * `Ok((Self, &[u8]))` - The parsed argument and the remaining data.
    /// * `Err(MessageError)` - An error occurred while parsing the argument.
    fn parse(data: &[u8]) -> Result<(Self, &[u8]), MessageError>;
}

impl ParseArgument for i32 {
    fn parse(data: &[u8]) -> Result<(Self, &[u8]), MessageError> {
        if data.len() < 4 {
            return Err(MessageError::InvalidMessage(
                "Not enough data to parse i32 argument".to_string(),
            ));
        }

        let value = i32::from_ne_bytes(data[0..4].try_into().unwrap());
        let remaining = &data[4..];

        Ok((value, remaining))
    }
}

impl ParseArgument for u32 {
    fn parse(data: &[u8]) -> Result<(Self, &[u8]), MessageError> {
        if data.len() < 4 {
            return Err(MessageError::InvalidMessage(
                "Not enough data to parse u32 argument".to_string(),
            ));
        }

        let value = u32::from_ne_bytes(data[0..4].try_into().unwrap());
        let remaining = &data[4..];

        Ok((value, remaining))
    }
}

impl ParseArgument for Fixed {
    fn parse(data: &[u8]) -> Result<(Self, &[u8]), MessageError> {
        let (raw, remaining) = i32::parse(data)?;
        Ok((Fixed(raw), remaining))
    }
}

impl ParseArgument for String {
    fn parse(data: &[u8]) -> Result<(Self, &[u8]), MessageError> {
        if data.len() < 4 {
            return Err(MessageError::InvalidMessage("The size header for the string argument was smaller than 4 bytes. There's missing data.".to_string()));
        }

        let len = u32::from_ne_bytes(data[0..4].try_into().unwrap()) as usize;

        if len == 0 {
            // Null string
            let remaining = &data[4..];
            return Ok((String::new(), remaining));
        }

        if data.len() < 4 + len {
            return Err(MessageError::InvalidMessage(
                "Not enough data to parse string argument".to_string(),
            ));
        }

        // Extract string bytes excluding null terminator
        let string_bytes = &data[4..4 + len - 1];
        let s = String::from_utf8(string_bytes.to_vec()).map_err(|_| {
            MessageError::InvalidMessage("Invalid UTF-8 in string argument".to_string())
        })?;

        // Compute padded length to next 4-byte boundary
        let total_bytes = len.div_ceil(4) * 4;
        let remaining = &data[total_bytes..];

        Ok((s, remaining))
    }
}

impl ParseArgument for ObjectId {
    fn parse(data: &[u8]) -> Result<(Self, &[u8]), MessageError> {
        let (id, remaining) = u32::parse(data)?;
        Ok((ObjectId(id), remaining))
    }
}

impl ParseArgument for Vec<u8> {
    fn parse(data: &[u8]) -> Result<(Self, &[u8]), MessageError> {
        if data.len() < 4 {
            return Err(MessageError::InvalidMessage(
                "Not enough data to parse byte array length".to_string(),
            ));
        }

        let len = u32::from_ne_bytes(data[0..4].try_into().unwrap()) as usize;

        if data.len() < 4 + len {
            return Err(MessageError::InvalidMessage(
                "Not enough data to parse byte array".to_string(),
            ));
        }

        let bytes = data[4..4 + len].to_vec();

        // Compute padded length to next 4-byte boundary
        let total_bytes = len.div_ceil(4) * 4;
        let remaining = &data[total_bytes + 4..];

        Ok((bytes, remaining))
    }
}
