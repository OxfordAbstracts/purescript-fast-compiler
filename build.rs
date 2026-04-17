fn main() {
    lalrpop::process_root().unwrap();

    // Embed git commit hash at compile time
    let output = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output();
    if let Ok(output) = output {
        let hash = String::from_utf8_lossy(&output.stdout).trim().to_string();
        println!("cargo:rustc-env=PFC_GIT_COMMIT={hash}");
    }
}
