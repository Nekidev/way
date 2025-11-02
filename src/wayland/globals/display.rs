use std::sync::Arc;

use crate::wayland::{
    connection::Connection,
    messages::{ArgumentEncoder, IntoRawMessage, NewId, RawMessage},
};

pub struct Display {
    conn: Arc<Connection>,
}

impl Display {
    pub async fn sync(&self) {}
}

struct DisplaySyncRequest;

impl IntoRawMessage for DisplaySyncRequest {
    fn into_raw_message(self) -> RawMessage {
        RawMessage {
            object_id: 1,
            opcode: 0,
            arguments: vec![NewId::auto().into()].encode(),
        }
    }
}
