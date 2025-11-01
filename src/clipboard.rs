use crate::wayland::connection::Connection;

pub async fn daemon() {
    let conn = Connection::from_env().await.unwrap();
}
