"""HTTP layer for the Games/ portal (see Games/DESIGN.md).

This package is pure I/O plumbing: routing, static file serving, request
validation, background jobs, and JSONL persistence. All game-theoretic
computation lives in Games/engine/, reached lazily through
server.engine_adapter so this package can be developed and tested
independently of it.
"""
