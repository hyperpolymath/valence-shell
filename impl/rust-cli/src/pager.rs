// SPDX-License-Identifier: PLMP-1.0-or-later
//! Smart Pager (fish-style)
//!
//! Automatically pages long output to prevent terminal flooding.
//! Features:
//! - Auto-detect terminal height
//! - Only page if output exceeds screen
//! - Use system pager (less) or built-in pager
//! - Preserve colors (ANSI codes)
//! - Keyboard navigation (space/enter/q)

use anyhow::{Context, Result};
use std::io::{self, Write};
use std::process::{Command, Stdio};

/// Smart pager configuration
pub struct Pager {
    /// Terminal height in lines (auto-detected)
    terminal_height: usize,

    /// Threshold: page if output > (height * threshold)
    /// Default: 0.9 (page if >90% of screen)
    threshold: f32,

    /// Use system pager (less) vs built-in
    use_system_pager: bool,
}

impl Default for Pager {
    fn default() -> Self {
        Self::new()
    }
}

impl Pager {
    /// Create new smart pager with auto-detected terminal height
    pub fn new() -> Self {
        let terminal_height = Self::detect_terminal_height();

        Self {
            terminal_height,
            threshold: 0.9,
            use_system_pager: true,
        }
    }

    /// Detect terminal height using termios
    fn detect_terminal_height() -> usize {
        // Try to get terminal size using crossterm
        if let Ok((_, rows)) = crossterm::terminal::size() {
            return rows as usize;
        }

        // Fallback to LINES env var
        if let Ok(lines_str) = std::env::var("LINES") {
            if let Ok(lines) = lines_str.parse::<usize>() {
                return lines;
            }
        }

        // Default fallback
        24
    }

    /// Check if output should be paged
    fn should_page(&self, line_count: usize) -> bool {
        line_count > (self.terminal_height as f32 * self.threshold) as usize
    }

    /// Page output using system pager (less)
    fn page_with_less(&self, content: &str) -> Result<()> {
        // Check if less is available
        let less_path = which::which("less").or_else(|_| which::which("more"))?;

        let mut child = Command::new(less_path)
            .arg("-R") // Preserve ANSI colors
            .arg("-F") // Exit if content fits on one screen
            .arg("-X") // Don't clear screen on exit
            .stdin(Stdio::piped())
            .spawn()
            .context("Failed to spawn pager")?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(content.as_bytes())
                .context("Failed to write to pager")?;
        }

        child.wait().context("Failed to wait for pager")?;
        Ok(())
    }

    /// Page output using built-in pager
    fn page_builtin(&self, content: &str) -> Result<()> {
        let lines: Vec<&str> = content.lines().collect();
        let total_lines = lines.len();

        if total_lines == 0 {
            return Ok(());
        }

        let page_size = self.terminal_height.saturating_sub(1); // Reserve 1 line for prompt
        let mut current_line = 0;

        while current_line < total_lines {
            // Display one page
            let end_line = std::cmp::min(current_line + page_size, total_lines);

            for line in &lines[current_line..end_line] {
                println!("{}", line);
            }

            current_line = end_line;

            // Check if more content remains
            if current_line < total_lines {
                // Show prompt
                let remaining = total_lines - current_line;
                print!(
                    "\r{}",
                    format!(
                        "-- MORE -- ({}/{} lines) [space=next page, enter=next line, q=quit] ",
                        current_line, total_lines
                    )
                );
                io::stdout().flush()?;

                // Read single character
                match Self::read_key()? {
                    Key::Space => {
                        // Next page
                        print!("\r{}\r", " ".repeat(80)); // Clear prompt line
                        continue;
                    }
                    Key::Enter => {
                        // Next line
                        print!("\r{}\r", " ".repeat(80));
                        current_line = end_line.saturating_sub(page_size - 1);
                        continue;
                    }
                    Key::Q | Key::Escape => {
                        // Quit
                        println!("\r{}\r", " ".repeat(80));
                        break;
                    }
                    _ => {
                        // Treat other keys as space
                        print!("\r{}\r", " ".repeat(80));
                        continue;
                    }
                }
            } else {
                // No more content - reached end
                break;
            }
        }

        Ok(())
    }

    /// Read a single key press (non-blocking)
    fn read_key() -> Result<Key> {
        use crossterm::event::{read, Event, KeyCode, KeyEvent};

        match read()? {
            Event::Key(KeyEvent { code, .. }) => match code {
                KeyCode::Char(' ') => Ok(Key::Space),
                KeyCode::Char('q') | KeyCode::Char('Q') => Ok(Key::Q),
                KeyCode::Enter => Ok(Key::Enter),
                KeyCode::Esc => Ok(Key::Escape),
                _ => Ok(Key::Other),
            },
            _ => Ok(Key::Other),
        }
    }

    /// Page output (smart: auto-detect if paging needed)
    ///
    /// If output is short, prints directly.
    /// If output is long, pages using system pager or built-in.
    ///
    /// # Arguments
    /// * `content` - Text to display/page
    ///
    /// # Examples
    /// ```no_run
    /// use vsh::pager::Pager;
    ///
    /// let pager = Pager::new();
    /// let long_output = "line 1\nline 2\n...".to_string();
    /// pager.page(&long_output)?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn page(&self, content: &str) -> Result<()> {
        let line_count = content.lines().count();

        if !self.should_page(line_count) {
            // Output is short - just print directly
            print!("{}", content);
            io::stdout().flush()?;
            return Ok(());
        }

        // Output is long - page it
        if self.use_system_pager {
            // Try system pager first
            if let Err(e) = self.page_with_less(content) {
                eprintln!("Warning: System pager failed ({}), using built-in", e);
                self.page_builtin(content)?;
            }
        } else {
            // Use built-in pager
            self.page_builtin(content)?;
        }

        Ok(())
    }

    /// Force paging (even if output is short)
    pub fn page_force(&self, content: &str) -> Result<()> {
        if self.use_system_pager {
            self.page_with_less(content)
                .or_else(|_| self.page_builtin(content))
        } else {
            self.page_builtin(content)
        }
    }

    /// Set threshold for auto-paging
    ///
    /// # Arguments
    /// * `threshold` - Page if output > (height * threshold). Range: 0.0 to 1.0
    pub fn with_threshold(mut self, threshold: f32) -> Self {
        self.threshold = threshold.clamp(0.0, 1.0);
        self
    }

    /// Set pager preference
    ///
    /// # Arguments
    /// * `use_system` - If true, use less/more. If false, use built-in pager.
    pub fn with_system_pager(mut self, use_system: bool) -> Self {
        self.use_system_pager = use_system;
        self
    }
}

/// Key press for pager navigation
enum Key {
    Space,
    Enter,
    Q,
    Escape,
    Other,
}

/// Global pager instance (convenience)
static PAGER: std::sync::OnceLock<Pager> = std::sync::OnceLock::new();

/// Get global pager instance
pub fn get_pager() -> &'static Pager {
    PAGER.get_or_init(Pager::new)
}

/// Convenience function: page output using global pager
///
/// # Examples
/// ```no_run
/// use vsh::pager::page;
///
/// let output = "line 1\nline 2\n...".to_string();
/// page(&output)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn page(content: &str) -> Result<()> {
    get_pager().page(content)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_terminal_height() {
        let height = Pager::detect_terminal_height();
        assert!(height > 0);
        assert!(height < 1000); // Sanity check
    }

    #[test]
    fn test_should_page() {
        let pager = Pager {
            terminal_height: 24,
            threshold: 0.9,
            use_system_pager: false,
        };

        assert!(!pager.should_page(10)); // 10 lines < 24 * 0.9 = 21.6
        assert!(!pager.should_page(21));
        assert!(pager.should_page(22)); // 22 > 21.6
        assert!(pager.should_page(100));
    }

    #[test]
    fn test_short_output_no_paging() {
        let pager = Pager::new();
        let short_content = "line 1\nline 2\nline 3\n";

        // Should not error
        pager.page(short_content).unwrap();
    }

    #[test]
    fn test_threshold_clamping() {
        let pager = Pager::new().with_threshold(1.5);
        assert_eq!(pager.threshold, 1.0); // Clamped to 1.0

        let pager = Pager::new().with_threshold(-0.5);
        assert_eq!(pager.threshold, 0.0); // Clamped to 0.0
    }
}
