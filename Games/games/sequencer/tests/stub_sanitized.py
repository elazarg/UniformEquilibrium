import http.server, functools, json, sys
root = sys.argv[1]
SEED = [[0,0,0,0]] * 16
def table(v):
    rows = [[0.0,0.0,0.0,0.0]]
    for m in range(1, 16):
        rows.append([float(v), 1.0, 0.0, 0.0])
    return rows
class H(http.server.SimpleHTTPRequestHandler):
    def _json(self, payload, code=200):
        body = json.dumps(payload).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)
    def do_GET(self):
        if self.path.startswith("/api/tables/curated"):
            return self._json({"tables": [
                {"id": "c1", "name": "unattacked table", "table": table(1),
                 "known_score": 1e9, "note": "score sanitized from inf"},
                {"id": "c2", "name": "scored table", "table": table(2),
                 "known_score": 0.004, "note": "ordinary"},
            ]})
        if self.path.startswith("/api/candidates"):
            return self._json({"candidates": [
                {"id": "k-null", "table": table(3), "game": "stub",
                 "evaluation": {"score": None}, "tier": "unattacked", "status": "proposed"},
                {"id": "k-inf", "table": table(1), "game": "stub",
                 "evaluation": {"score": 1e9}, "tier": "unattacked", "status": "proposed"},
                {"id": "k-real", "table": table(2), "game": "stub",
                 "evaluation": {"score": 0.017}, "tier": "survivor-quick", "status": "proposed"},
            ]})
        return super().do_GET()
    def do_POST(self):
        length = int(self.headers.get("Content-Length", 0))
        self.rfile.read(length)
        if self.path.startswith("/api/evaluate"):
            # nan sanitized to null: must never be read as a kill
            return self._json({"exploitability": None, "per_player": [None]*4,
                               "on_path": [0,0,0,0], "best_deviations": []})
        return self._json({"error": "not stubbed"}, 404)
    def log_message(self, *a): pass
http.server.ThreadingHTTPServer(("127.0.0.1", 8795),
    functools.partial(H, directory=root)).serve_forever()
