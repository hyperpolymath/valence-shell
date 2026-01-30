// SPDX-License-Identifier: PLMP-1.0-or-later
//! Integration test for daemon client

use vsh::daemon_client::DaemonClient;

#[test]
#[ignore] // Run with: cargo test --test daemon_integration_test -- --ignored
fn test_daemon_connection() {
    if !DaemonClient::is_daemon_running() {
        println!("⚠️  Daemon not running - start it with: cd ../elixir && mix run --no-halt");
        return;
    }

    let mut client = DaemonClient::connect().expect("Failed to connect to daemon");

    // Test status
    let status = client.status().expect("Failed to get status");
    println!("✓ Daemon status: {:?}", status);

    // Test mkdir
    let result = client.mkdir("/tmp/vsh-test-dir").expect("Failed to mkdir");
    println!("✓ mkdir result: {:?}", result);
    assert!(result.success);

    // Test undo
    let undo_result = client.undo(None).expect("Failed to undo");
    println!("✓ undo result: {:?}", undo_result);

    println!("\n🎉 All daemon integration tests passed!");
}
