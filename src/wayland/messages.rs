//! A module for parsing and encoding Wayland protocol messages.
//!
//! As a user of the framework, you will most likely not interact with this module directly, but
//! you may encounter it when working with higher-level abstractions.
//!
//! # Wayland's OO Model
//!
//! The Wayland protocol uses an object-oriented model, where clients interact with objects (such
//! as windows, surfaces, etc.) through messages. You may be familiar with this model if you've
//! used OOP languages like Python, Java, or C++.
//!
//! In Wayland, everything is an object, and each object has a unique ID. Clients send messages to
//! these objects with an opcode, which identifies what method of that object to invoke. For
//! example, Wayland's root object, the display (`wl_display`), could be represented as a struct
//! with associated functions. Something like this:
//!
//! ```
//! struct Display {
//!     // Wayland's display object ID is always 1. For other objects, this would be dynamically
//!     // assigned.
//!     object_id: u32,
//! }
//!
//! impl Display {
//!     /// Corresponds to the `get_registry` method of the `wl_display` object in Wayland.
//!     ///
//!     /// The OP code for this method (associated function) is 0.
//!     fn get_registry(&self, new_id: u32) -> Registry {
//!         ...
//!     }
//! }
//! ```
//!
//! Then, to call the `get_registry` function, a client would send a message to the display object
//! with the following structure:
//!
//! ```text
//! Object ID: 1 (the display object)
//! Opcode: 0 (the get_registry method)
//! Arguments: [new_id]
//! ```
//!
//! TL;DR: Wayland uses an object-oriented model for communication between clients and the
//! compositor. You can think of objects as structs and methods as functions associated with those
//! structs.
//!
//! # Requests and Events
//!
//! In Wayland, messages can be either requests or events. Requests are sent by clients to the
//! compositor, and events are sent from the compositor to clients.
//!
//! Events may be in response to requests, or they may be unsolicited notifications from the
//! compositor.
//!
//! In HTTP terms, requests are similar to POST or GET requests, while events are similar to
//! server-sent events or WebSocket messages.
//!
//! # Message Structure
//!
//! Wayland protocol messages are quite simple, they only consist of a header and a list of
//! arguments.
//!
//! The format looks like this:
//!
//! ```text
//! Bytes:  0          3 4          5 6          7 8
//!        +------------+------------+------------+------------···
//!        | Object  ID |   Opcode   |    Size    | Arguments
//!        +------------+------------+------------+------------···
//!             u32          u16          u16
//! ```
//!
//! - Object ID: The ID of the object the message is sent to.
//! - Opcode: The opcode of the message, which identifies the specific action to be performed.
//! - Size: The total size of the message in bytes, including the header and the arguments.
//! - Arguments: The arguments of the message, which can be of [various types](#argument-types).
//!
//! *NOTE: The header itself is 8 bytes long in total because all its fields are counted as one
//! part. That means opcode and size are not padded for alignment, only the arguments are. You'll
//! read about this in [Alignment and Endianness](#alignment-and-endianness).*
//!
//! ## Alignment and Endianness
//!
//! Wayland messages are aligned to 4-byte boundaries, meaning that each argument is padded
//! to ensure it starts at a multiple of 4 bytes.
//!
//! For example, if an argument takes just 1 byte, it'll be padded with 3 extra bytes to make it
//! 4 bytes, even if those extra bytes are not used. I.e. a byte `01` would be sent as `01 00
//! 00 00`. The same way, for example, a 6-byte argument would be padded with 2 extra bytes to
//! make it 8 bytes, i.e. `01 02 03 04 05 06 00 00`. 8-byte arguments do not need any padding, as
//! they are already aligned to 4-byte boundaries.
//!
//! Note that even though `00` bytes were used in the example for padding, the actual value of
//! those bytes is not specified by the protocol and may be anything. This doesn't matter, as
//! padding bytes are simply ignored when parsing the message.
//!
//! As for endianness, Wayland uses the native endianness of the system for encoding and decoding
//! messages. This means that on little-endian systems (like x86), multi-byte values are sent in
//! little-endian format, while on big-endian systems (like some ARM architectures), they are sent
//! in big-endian format.
//!
//! This crate uses [`tokio_byteorder`] to handle reading and writing multi-byte values in the
//! native endianness of the system.
//!
//! # Argument Types
//!
//! Wayland protocol messages can contain no, one, or multiple arguments of the following types:
//!
//! - `int` - A 32-bit signed integer (represented as [`i32`]).
//! - `uint` - A 32-bit unsigned integer (represented as [`u32`]).
//! - `fixed` - A 24.8 fixed-point number (represented as [`Fixed`]).
//! - `string` - A UTF-8 encoded string with a length prefix and null terminator (represented as
//!   [`String`]).
//! - `object` - A Wayland object ID (represented as [`ObjectId`]).
//! - `new_id` - A new Wayland object ID to be assigned before use (represented as [`NewId`]).
//! - `array` - A byte array with a length prefix (represented as [`Vec<u8>`]).
//! - `fd` - A file descriptor (represented as [`u32`]).
//!
//! These value types are represented in the code as the [`Value`] and [`ValueType`] enums, each
//! arm being one type.
//!
//! You can read the reference for Wayland protocol types in the [official Wayland
//! documentation](https://wayland.freedesktop.org/docs/html/ch04.html#sect-Protocol-Wire-Format).
//!
//! ## File Descriptors
//!
//! File descriptors (fd), unlike the rest of argument types, are not sent as part of the message
//! data itself. Instead, they are sent out-of-band using Unix domain socket ancillary data
//! (`SCM_RIGHTS`).
//!
//! The protocol does not specify the exact position of the file descriptors in the stream, except
//! that the order of file descriptors is the same as the order of messages and fd arguments within
//! messages on the stream. This means that any byte of the stream, even the message header, may
//! carry the ancillary data with file descriptors.
//!
//! This means that messages must be queued until all file descriptors for the message have been
//! received, which may even be before the message is sent or after the whole message has been
//! received.
//!
//! For example, a message with with a FD argument may be received like this:
//!
//! ```text
//! 01 00 00 00 00 00 08 00   // message header
//! <SCM_RIGHTS sends fd: /dev/shm/abc123>
//! ```
//!
//! ### But, Why File Descriptors?
//!
//! In many cases, big amounts of data or resources need to be shared between the Wayland
//! compositor and clients. For example, if you want to render an image, you don't send the raw
//! pixels through the stream because:
//!
//! 1. It would be inefficient and slow. You'd need to copy all the pixel data into the message,
//!    which would take a time and bandwidth. The stream protocol is kept simple and lightweight
//!    for efficiency, which means big data and resources go out of band.
//! 2. File descriptors provide a way to share resources like memory buffers, shared memory
//!    segments, or GPU buffers between processes. These cannot be sent as raw data in the stream.

use std::sync::{
    OnceLock,
    atomic::{AtomicU32, Ordering},
};

use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::UnixStream,
};
use tokio_byteorder::{AsyncReadBytesExt, AsyncWriteBytesExt, NativeEndian};
use withfd::WithFd;

#[derive(Debug, thiserror::Error)]
pub enum MessageError {
    #[error("Failed to read from or to write to the Wayland connection")]
    IoFailed(#[from] std::io::Error),

    #[error("The Wayland message received from the compositor is invalid: {0}")]
    InvalidMessage(String),
}

/// Represents a raw Wayland protocol message.
pub struct RawMessage {
    pub object_id: u32,
    pub opcode: u16,
    pub arguments: Vec<u8>,
}

impl RawMessage {
    /// Reads a raw Wayland message from the given [`WithFd<UnixStream>`].
    ///
    /// Arguments:
    /// * `stream` - The [`WithFd<UnixStream>`] to read the message from.
    ///
    /// Returns:
    /// * `Ok(RawMessage)` - The successfully read Wayland message.
    /// * `Err(MessageError)` - An error occurred while reading the message.
    pub async fn read(stream: &mut WithFd<UnixStream>) -> Result<Self, MessageError> {
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

        Ok(RawMessage {
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

/// The global atomic counter for generating new Wayland object IDs.
static NEXT_ID: OnceLock<AtomicU32> = OnceLock::new();

/// A Wayland new object ID to be assigned before use.
pub struct NewId(u32);

impl NewId {
    /// Generates a new Wayland object ID.
    ///
    /// Returns:
    /// * `NewId` - The newly generated Wayland object ID.
    pub fn auto() -> Self {
        NewId(
            NEXT_ID
                .get_or_init(|| AtomicU32::new(1))
                .fetch_add(1, Ordering::Relaxed),
        )
    }

    /// Creates a Wayland object ID with a fixed value.
    ///
    /// Arguments:
    /// * `id` - The fixed object ID value.
    ///
    /// Returns:
    /// * `NewId` - The Wayland object ID with the specified value.
    pub fn fixed(id: u32) -> Self {
        NewId(id)
    }
}

/// A trait for parsing Wayland protocol arguments from byte slices.
trait ArgumentType: Sized {
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

    /// Encodes the argument into a byte vector.
    ///
    /// Returns:
    /// * `Vec<u8>` - The encoded byte vector.
    fn encode(&self) -> Vec<u8>;
}

impl ArgumentType for i32 {
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

    fn encode(&self) -> Vec<u8> {
        self.to_ne_bytes().to_vec()
    }
}

impl ArgumentType for u32 {
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

    fn encode(&self) -> Vec<u8> {
        self.to_ne_bytes().to_vec()
    }
}

impl ArgumentType for Fixed {
    fn parse(data: &[u8]) -> Result<(Self, &[u8]), MessageError> {
        let (raw, remaining) = i32::parse(data)?;
        Ok((Fixed(raw), remaining))
    }

    fn encode(&self) -> Vec<u8> {
        self.0.to_ne_bytes().to_vec()
    }
}

impl ArgumentType for String {
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

    fn encode(&self) -> Vec<u8> {
        let mut encoded = Vec::new();
        let len = self.len() + 1 + 4; // +1 for null terminator, +4 for length prefix

        // Write length prefix
        encoded.extend_from_slice(&(len as u32).to_ne_bytes());

        // Write string bytes
        encoded.extend_from_slice(self.as_bytes());

        // Write null terminator
        encoded.push(0);

        // Add padding to align to 4-byte boundary
        let padding = (4 - (encoded.len() % 4)) % 4;
        encoded.extend(std::iter::repeat_n(0, padding));

        encoded
    }
}

impl ArgumentType for ObjectId {
    fn parse(data: &[u8]) -> Result<(Self, &[u8]), MessageError> {
        let (id, remaining) = u32::parse(data)?;
        Ok((ObjectId(id), remaining))
    }

    fn encode(&self) -> Vec<u8> {
        self.0.to_ne_bytes().to_vec()
    }
}

impl ArgumentType for NewId {
    fn parse(data: &[u8]) -> Result<(Self, &[u8]), MessageError> {
        let (id, remaining) = u32::parse(data)?;
        Ok((NewId::fixed(id), remaining))
    }

    fn encode(&self) -> Vec<u8> {
        self.0.to_ne_bytes().to_vec()
    }
}

impl ArgumentType for Vec<u8> {
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

    fn encode(&self) -> Vec<u8> {
        let mut encoded = Vec::with_capacity(self.len() + 4);
        let len = self.len();

        // Write length prefix
        encoded.extend_from_slice(&(len as u32).to_ne_bytes());

        // Write byte array
        encoded.extend_from_slice(self);

        // Add padding to align to 4-byte boundary
        let padding = (4 - (encoded.len() % 4)) % 4;
        encoded.extend(std::iter::repeat_n(0, padding));

        encoded
    }
}

/// Represents a Wayland protocol argument value.
pub enum Value {
    I32(i32),
    U32(u32),
    Fixed(Fixed),
    String(String),
    Object(ObjectId),
    NewId(NewId),
    Array(Vec<u8>),
    Fd(u32),
}

impl Value {
    /// Returns the type of the Wayland protocol argument.
    ///
    /// Returns:
    /// * [`ValueType`] - The type of the argument.
    pub fn r#type(&self) -> ValueType {
        match self {
            Value::I32(_) => ValueType::I32,
            Value::U32(_) => ValueType::U32,
            Value::Fixed(_) => ValueType::Fixed,
            Value::String(_) => ValueType::String,
            Value::Object(_) => ValueType::Object,
            Value::NewId(_) => ValueType::NewId,
            Value::Array(_) => ValueType::Array,
            Value::Fd(_) => ValueType::Fd,
        }
    }

    pub fn encode(&self) -> Vec<u8> {
        match self {
            Value::I32(v) => v.encode(),
            Value::U32(v) => v.encode(),
            Value::Fixed(v) => v.encode(),
            Value::String(v) => v.encode(),
            Value::Object(v) => v.encode(),
            Value::NewId(v) => v.encode(),
            Value::Array(v) => v.encode(),
            Value::Fd(_) => {
                unimplemented!("File descriptor encoding is not implemented yet");
            }
        }
    }
}

impl From<i32> for Value {
    fn from(val: i32) -> Self {
        Value::I32(val)
    }
}

impl From<u32> for Value {
    fn from(val: u32) -> Self {
        Value::U32(val)
    }
}

impl From<Fixed> for Value {
    fn from(val: Fixed) -> Self {
        Value::Fixed(val)
    }
}

impl From<String> for Value {
    fn from(val: String) -> Self {
        Value::String(val)
    }
}

impl From<ObjectId> for Value {
    fn from(val: ObjectId) -> Self {
        Value::Object(val)
    }
}

impl From<NewId> for Value {
    fn from(val: NewId) -> Self {
        Value::NewId(val)
    }
}

impl From<Vec<u8>> for Value {
    fn from(val: Vec<u8>) -> Self {
        Value::Array(val)
    }
}

/// Represents the type of a Wayland protocol argument.
pub enum ValueType {
    I32,
    U32,
    Fixed,
    String,
    Object,
    NewId,
    Array,
    Fd,
}

impl ValueType {
    /// Reads a Wayland protocol argument of this type from the given byte slice.
    ///
    /// Arguments:
    /// * `data` - The byte slice to read the argument from.
    ///
    /// Returns:
    /// * `Ok((Value, &[u8]))` - The read argument and the remaining data.
    /// * `Err(MessageError)` - An error occurred while reading the argument.
    pub fn read<'a>(&self, data: &'a [u8]) -> Result<(Value, &'a [u8]), MessageError> {
        match self {
            ValueType::I32 => {
                let (val, remaining) = i32::parse(data)?;
                Ok((Value::I32(val), remaining))
            }
            ValueType::U32 => {
                let (val, remaining) = u32::parse(data)?;
                Ok((Value::U32(val), remaining))
            }
            ValueType::Fixed => {
                let (val, remaining) = Fixed::parse(data)?;
                Ok((Value::Fixed(val), remaining))
            }
            ValueType::String => {
                let (val, remaining) = String::parse(data)?;
                Ok((Value::String(val), remaining))
            }
            ValueType::Object => {
                let (val, remaining) = ObjectId::parse(data)?;
                Ok((Value::Object(val), remaining))
            }
            ValueType::NewId => {
                let (val, remaining) = u32::parse(data)?;
                Ok((Value::NewId(NewId::fixed(val)), remaining))
            }
            ValueType::Array => {
                let (val, remaining) = Vec::<u8>::parse(data)?;
                Ok((Value::Array(val), remaining))
            }
            ValueType::Fd => {
                unimplemented!("File descriptor parsing is not implemented yet");
            }
        }
    }
}

/// A trait to convert typed messages into a [`RawMessage`].
pub trait IntoRawMessage {
    fn into_raw_message(self) -> RawMessage;
}

pub trait ArgumentsDecoder {
    /// Decodes the arguments from a byte slice into a vector of [`Value`]s.
    ///
    /// Arguments:
    /// * `data` - The byte slice containing the encoded arguments.
    ///
    /// Returns:
    /// * `Ok(Vec<Value>)` - The decoded arguments.
    /// * `Err(MessageError)` - An error occurred while decoding the arguments.
    fn decode(&self, data: &[u8]) -> Result<Vec<Value>, MessageError>;
}

impl ArgumentsDecoder for Vec<ValueType> {
    fn decode(&self, mut data: &[u8]) -> Result<Vec<Value>, MessageError> {
        let mut values = Vec::with_capacity(self.len());

        for arg_type in self {
            let (value, remaining) = arg_type.read(data)?;
            values.push(value);
            data = remaining;
        }

        Ok(values)
    }
}
