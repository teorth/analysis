import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('preview', Path(__file__).parents[1] / 'serve.py')
preview = importlib.util.module_from_spec(spec)
spec.loader.exec_module(preview)

class ContainmentTests(unittest.TestCase):
    def test_symlink_to_outside_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root = base / 'site'
            root.mkdir()
            outside = base / 'private.txt'
            outside.write_text('outside the published site')
            (root / 'linked.txt').symlink_to(outside)
            translated = preview.CustomHTTPRequestHandler._join_under(str(root), 'linked.txt')
            self.assertNotEqual(Path(translated).resolve(), outside.resolve())
            self.assertFalse(Path(translated).exists())

    def test_internal_symlink_and_symlinked_root_are_allowed(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root = base / 'site'
            root.mkdir()
            published = root / 'page.html'
            published.write_text('published')
            (root / 'linked.html').symlink_to(published)
            alias = base / 'site-alias'
            alias.symlink_to(root, target_is_directory=True)
            translated = preview.CustomHTTPRequestHandler._join_under(str(alias), 'linked.html')
            self.assertEqual(Path(translated).read_text(), 'published')

if __name__ == '__main__':
    unittest.main()
