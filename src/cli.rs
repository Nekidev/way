use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(
    name = "way",
    about = "A general-purpose Wayland utility CLI tool.",
    author,
    version,
    arg_required_else_help = true
)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Subcommand)]
pub enum Command {
    Clipboard {
        #[command(subcommand)]
        command: ClipboardCommand,
    },
}

#[derive(Subcommand)]
pub enum ClipboardCommand {
    /// Starts the clipboard daemon.
    Daemon,
}
