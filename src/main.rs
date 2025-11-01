use clap::Parser;

use crate::cli::{Cli, ClipboardCommand, Command};

mod cli;
mod clipboard;
mod wayland;

#[tokio::main]
async fn main() {
    pretty_logging::init(log::LevelFilter::Trace, ["way"]);

    let args = Cli::parse();

    match args.command {
        Command::Clipboard { command } => handle_clipboard_command(command).await,
    }
}

async fn handle_clipboard_command(command: ClipboardCommand) {
    match command {
        ClipboardCommand::Daemon => {
            clipboard::daemon().await;
        }
    }
}
