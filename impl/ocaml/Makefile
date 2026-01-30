# SPDX-License-Identifier: PMPL-1.0-or-later
# Makefile for Lean 4 → C → OCaml extraction pipeline

LEAN_PREFIX := $(shell lean --print-prefix)
LEAN_INCLUDE := $(LEAN_PREFIX)/include
LEAN_LIB := $(LEAN_PREFIX)/lib/lean

# Directories
LEAN_SRC := ../../proofs/lean4
LEAN_BUILD := $(LEAN_SRC)/.lake/build
LEAN_IR_DIR := $(LEAN_BUILD)/ir

# Output library
TARGET := liblean_vsh.so

# Source files
C_WRAPPER := lean_wrapper.c
LEAN_EXTRACTION := Extraction

.PHONY: all clean build-lean build-c test

all: build-lean build-c

# Step 1: Build Lean 4 code and extract to C
build-lean:
	@echo "Building Lean 4 extraction..."
	cd $(LEAN_SRC) && lake build $(LEAN_EXTRACTION)
	@echo "Lean compilation complete: $(LEAN_IR_DIR)/$(LEAN_EXTRACTION).c"

# Step 2: Compile C wrapper + extracted Lean code to shared library
build-c: build-lean
	@echo "Compiling C wrapper to shared library..."
	gcc -shared -fPIC -o $(TARGET) \
		$(C_WRAPPER) \
		$(LEAN_IR_DIR)/$(LEAN_EXTRACTION).c \
		-I$(LEAN_INCLUDE) \
		-L$(LEAN_LIB) \
		-lleanshared \
		-Wl,-rpath,$(LEAN_LIB)
	@echo "Shared library created: $(TARGET)"

# Test that the library loads
test: all
	@echo "Testing library loading..."
	@if [ -f $(TARGET) ]; then \
		echo "✓ $(TARGET) exists"; \
		ldd $(TARGET) | grep lean || echo "Warning: Lean library not linked"; \
	else \
		echo "✗ $(TARGET) not found"; \
		exit 1; \
	fi

# Clean build artifacts
clean:
	rm -f $(TARGET)
	cd $(LEAN_SRC) && lake clean

# Install library to system location (optional)
install: all
	@echo "Installing $(TARGET) to /usr/local/lib..."
	sudo cp $(TARGET) /usr/local/lib/
	sudo ldconfig
