#!/usr/bin/env bash
exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f .lake/native-browser-serial.toml "$@"
