import tempfile
import unittest
from pathlib import Path

from server.static import resolve_static


class StaticResolutionTests(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        (self.root / "portal").mkdir()
        (self.root / "portal" / "index.html").write_text("<html>portal</html>")
        (self.root / "portal" / "app.js").write_text("console.log(1)")
        (self.root / "games" / "standoff").mkdir(parents=True)
        (self.root / "games" / "standoff" / "index.html").write_text("<html>standoff</html>")
        (self.root / "games" / "standoff" / "sub").mkdir()
        (self.root / "games" / "standoff" / "sub" / "index.html").write_text("<html>sub</html>")

    def tearDown(self):
        self._tmp.cleanup()

    def test_root_serves_portal_index(self):
        file_path, content_type = resolve_static(self.root, "/")
        self.assertEqual(file_path, self.root / "portal" / "index.html")
        self.assertEqual(content_type, "text/html")

    def test_root_file_served_with_mime_type(self):
        file_path, content_type = resolve_static(self.root, "/app.js")
        self.assertEqual(file_path, self.root / "portal" / "app.js")
        self.assertIn("javascript", content_type)

    def test_game_mount_prefix(self):
        file_path, _ = resolve_static(self.root, "/standoff/")
        self.assertEqual(file_path, self.root / "games" / "standoff" / "index.html")

    def test_game_mount_directory_without_trailing_slash_serves_index(self):
        file_path, _ = resolve_static(self.root, "/standoff/sub")
        self.assertEqual(file_path, self.root / "games" / "standoff" / "sub" / "index.html")

    def test_missing_file_is_none(self):
        self.assertIsNone(resolve_static(self.root, "/standoff/nope.js"))

    def test_unmounted_prefix_falls_through_to_root_mount(self):
        # "/" is the last, catch-all mount: an unknown top-level path still
        # resolves inside portal/ (and 404s there if the file is absent).
        self.assertIsNone(resolve_static(self.root, "/totally-unknown/thing.js"))

    def test_path_traversal_is_rejected(self):
        self.assertIsNone(resolve_static(self.root, "/standoff/../../../etc/passwd"))
        # Escapes the "/" mount's root (games_root/portal) to a sibling
        # directory outside it -- must not leak files from elsewhere in
        # games_root, even though the path stays inside games_root overall.
        (self.root / "secret.txt").write_text("do not serve me")
        self.assertIsNone(resolve_static(self.root, "/../secret.txt"))

    def test_path_traversal_via_encoded_dots(self):
        self.assertIsNone(resolve_static(self.root, "/standoff/%2e%2e/%2e%2e/secret"))


if __name__ == "__main__":
    unittest.main()
