use crate::wayland::messages::{IntoMessage, Message};

pub struct GetRegistryRequest;

impl IntoMessage for GetRegistryRequest {
    fn into_message(self, id_generator: impl Fn() -> u32) -> Message {
        Message {
            object_id: 1,
            opcode: 0,
            arguments: id_generator().to_le_bytes().to_vec(),
        }
    }
}
