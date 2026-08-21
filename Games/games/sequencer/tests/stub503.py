import http.server, functools, sys
root = sys.argv[1]
class H(http.server.SimpleHTTPRequestHandler):
    def _busy(self):
        body = b'{"error": "engine warming up"}'
        self.send_response(503)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)
    def do_GET(self):
        if self.path.startswith("/api/"):
            return self._busy()
        return super().do_GET()
    def do_POST(self):
        return self._busy()
    def log_message(self, *a): pass
http.server.ThreadingHTTPServer(("127.0.0.1", 8794),
    functools.partial(H, directory=root)).serve_forever()
