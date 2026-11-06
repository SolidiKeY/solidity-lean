# syntax=docker/dockerfile:1
FROM emscripten/emsdk:4.0.15@sha256:27bc6267cb285223b8aebb7627bfebae7cb3ad2aaa0d5923b8aa5321793033e8
RUN --mount=type=secret,id=system_ca,required=true \
    apt-get -o Acquire::https::CaInfo=/run/secrets/system_ca update && \
    DEBIAN_FRONTEND=noninteractive apt-get -o Acquire::https::CaInfo=/run/secrets/system_ca install -y --no-install-recommends pkg-config cmake make git && \
    rm -rf /var/lib/apt/lists/*
