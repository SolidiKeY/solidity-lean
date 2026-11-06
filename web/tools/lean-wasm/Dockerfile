# syntax=docker/dockerfile:1
FROM emscripten/emsdk:4.0.15@sha256:27bc6267cb285223b8aebb7627bfebae7cb3ad2aaa0d5923b8aa5321793033e8
RUN --mount=type=secret,id=system_ca \
    if test -f /run/secrets/system_ca; then cp /run/secrets/system_ca /usr/local/share/ca-certificates/session.crt; update-ca-certificates; fi; \
    apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends pkg-config cmake make git && \
    rm -rf /var/lib/apt/lists/*
