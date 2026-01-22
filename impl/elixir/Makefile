# SPDX-License-Identifier: PLMP-1.0-or-later
# Valence Shell - Elixir NIF Makefile

# Erlang paths
ERLANG_PATH = $(shell erl -eval 'io:format("~s", [lists:concat([code:root_dir(), "/erts-", erlang:system_info(version), "/include"])])' -s init stop -noshell)
ERL_INTERFACE_INCLUDE = $(shell erl -eval 'io:format("~s", [code:lib_dir(erl_interface, include)])' -s init stop -noshell)
ERL_INTERFACE_LIB = $(shell erl -eval 'io:format("~s", [code:lib_dir(erl_interface, lib)])' -s init stop -noshell)

# Zig library path
ZIG_LIB_DIR = ../zig/zig-out/lib
ZIG_INCLUDE_DIR = ../zig/src

# Platform detection
UNAME_S := $(shell uname -s)

ifeq ($(UNAME_S),Darwin)
    LDFLAGS = -dynamiclib -undefined dynamic_lookup
    SO_EXT = .so
else
    LDFLAGS = -shared -fPIC
    SO_EXT = .so
endif

# Compiler flags
CC = gcc
CFLAGS = -fPIC -O2 -Wall -Wextra \
         -I$(ERLANG_PATH) \
         -I$(ERL_INTERFACE_INCLUDE) \
         -I$(ZIG_INCLUDE_DIR)

# Output paths
PRIV_DIR = priv
NIF_SO = $(PRIV_DIR)/valence_ffi$(SO_EXT)

# Source files
C_SRC = c_src/valence_nif.c

# Zig static library
ZIG_LIB = $(ZIG_LIB_DIR)/libvalence_ffi.a

.PHONY: all clean zig_lib

all: $(PRIV_DIR) zig_lib $(NIF_SO)

$(PRIV_DIR):
	mkdir -p $(PRIV_DIR)

# Build Zig library first
zig_lib:
	cd ../zig && zig build -Doptimize=ReleaseFast

$(NIF_SO): $(C_SRC) $(ZIG_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) \
		-o $@ \
		$(C_SRC) \
		$(ZIG_LIB) \
		-L$(ERL_INTERFACE_LIB) \
		-lei -lpthread

clean:
	rm -rf $(PRIV_DIR)
	rm -f c_src/*.o
