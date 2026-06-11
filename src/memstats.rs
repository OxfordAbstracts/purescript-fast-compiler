//! Process memory introspection + opt-in checkpoint log.
//!
//! Enabled with `PFC_MEM_LOG=<path>` env var. When set, callers invoke
//! [`checkpoint`] with a short label (e.g. a module name) and the
//! current RSS in bytes is appended to the file along with the label,
//! a monotonic sequence number, and time-since-process-start (ms).
//! No-ops when the env var is unset — zero overhead in the default
//! release build.
//!
//! Reads RSS via the OS-specific syscall: `task_info` on macOS,
//! `/proc/self/status` on Linux. Other targets fall back to 0.

use std::io::Write;
use std::sync::{Mutex, OnceLock};

/// Current resident set size in bytes. Returns 0 on failure or on
/// unsupported platforms.
pub fn rss_bytes() -> u64 {
    rss_impl()
}

#[cfg(target_os = "macos")]
fn rss_impl() -> u64 {
    // `mach_task_basic_info` via the `task_info` syscall. Layout
    // mirrors `<mach/task_info.h>` — keep the struct opaque-as-
    // bytes since libc doesn't expose this type cleanly on macOS.
    #[repr(C)]
    struct MachTaskBasicInfo {
        virtual_size: u64,
        resident_size: u64,
        resident_size_max: u64,
        user_time: [u32; 2],
        system_time: [u32; 2],
        policy: i32,
        suspend_count: i32,
    }
    const MACH_TASK_BASIC_INFO: i32 = 20;
    // `MACH_TASK_BASIC_INFO_COUNT = sizeof / sizeof(u32)`.
    const COUNT: u32 = (std::mem::size_of::<MachTaskBasicInfo>() / 4) as u32;

    extern "C" {
        fn mach_task_self() -> u32;
        fn task_info(
            target: u32,
            flavor: i32,
            info: *mut MachTaskBasicInfo,
            count: *mut u32,
        ) -> i32;
    }

    let mut info: MachTaskBasicInfo = unsafe { std::mem::zeroed() };
    let mut count: u32 = COUNT;
    let kr = unsafe {
        task_info(
            mach_task_self(),
            MACH_TASK_BASIC_INFO,
            &mut info,
            &mut count,
        )
    };
    if kr == 0 {
        info.resident_size
    } else {
        0
    }
}

#[cfg(target_os = "linux")]
fn rss_impl() -> u64 {
    let s = match std::fs::read_to_string("/proc/self/status") {
        Ok(s) => s,
        Err(_) => return 0,
    };
    for line in s.lines() {
        if let Some(rest) = line.strip_prefix("VmRSS:") {
            // `VmRSS:    12345 kB`
            let kb: u64 = rest
                .trim()
                .split_whitespace()
                .next()
                .and_then(|n| n.parse().ok())
                .unwrap_or(0);
            return kb * 1024;
        }
    }
    0
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn rss_impl() -> u64 {
    0
}

struct LogState {
    file: std::fs::File,
    start: std::time::Instant,
    seq: u64,
}

fn log_state() -> Option<&'static Mutex<LogState>> {
    static STATE: OnceLock<Option<Mutex<LogState>>> = OnceLock::new();
    STATE
        .get_or_init(|| {
            let path = std::env::var("PFC_MEM_LOG").ok()?;
            let file = std::fs::OpenOptions::new()
                .create(true)
                .truncate(true)
                .write(true)
                .open(&path)
                .ok()?;
            Some(Mutex::new(LogState {
                file,
                start: std::time::Instant::now(),
                seq: 0,
            }))
        })
        .as_ref()
}

/// Write a `<seq>\t<elapsed_ms>\t<rss_mb>\t<label>` line to the log
/// file configured via `PFC_MEM_LOG`. No-op when unset.
///
/// `label` should be short (one module name, one phase name) — gets
/// written verbatim, newlines stripped to keep lines intact.
pub fn checkpoint(label: &str) {
    let Some(state_lock) = log_state() else { return };
    let rss = rss_bytes();
    let mut state = match state_lock.lock() {
        Ok(g) => g,
        Err(_) => return,
    };
    let elapsed_ms = state.start.elapsed().as_millis() as u64;
    state.seq += 1;
    let seq = state.seq;
    let mb = rss as f64 / (1024.0 * 1024.0);
    let safe_label: String = label
        .chars()
        .filter(|c| *c != '\n' && *c != '\t')
        .collect();
    let _ = writeln!(
        state.file,
        "{seq}\t{elapsed_ms}\t{mb:.1}\t{safe_label}",
    );
    // Best-effort flush; if it fails we drop the line — preferable
    // to taking a panic in instrumentation.
    let _ = state.file.flush();
}
