use std::sync::Arc;

use crate::wayland::connection::Connection;

pub struct Display {
    conn: Arc<Connection>,
}

impl Display {
    pub async fn sync(&self) {
        self.conn.recv_raw();
    }
}

struct DisplaySyncRequest;