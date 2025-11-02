use crate::wayland::globals::display::Display;

pub mod display;

pub enum InterfaceType {
    Display,
    Registry,
    Callback,
    Compositor,
    ShmPool,
    Shm,
    Buffer,
    DataOffer,
    DataSource,
    DataDevice,
    DataDeviceManager,
    Shell,
    ShellSurface,
    Surface,
    Seat,
    Pointer,
    Keyboard,
    Touch,
    Output,
    Region,
    Subcompositor,
    Subsurface,
    Fixes,
}

pub enum Interface {
    Display(Display),
}
