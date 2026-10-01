import json
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile
import unittest


class TestScriptRoots(unittest.TestCase):
    def test_builds_and_preview_resolve_paths_from_repository(self):
        source = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory).resolve()
            repo = base / 'checkout with spaces'
            repo.mkdir()
            for name in ('build.sh', 'build-web.sh', 'serve.py'):
                shutil.copyfile(source / name, repo / name)
            tools = base / 'bin'
            tools.mkdir()
            lake = tools / 'lake'
            lake.write_text('#!/bin/sh\npwd >> "$LAKE_CWD_LOG"\n')
            lake.chmod(0o755)
            log = base / 'lake.log'
            env = dict(os.environ, PATH=str(tools) + os.pathsep + os.environ['PATH'],
                       LAKE_CWD_LOG=str(log))
            for name in ('build.sh', 'build-web.sh'):
                subprocess.run(['bash', str(repo / name)], cwd=base, env=env, check=True)
            self.assertEqual(log.read_text().splitlines(), [str(repo)] * 6)
            code = ('import json, runpy; m=runpy.run_path(' + repr(str(repo / 'serve.py')) + '); '
                    'print(json.dumps([m["BOOK_SITE"], m["DOCS_SITE"]]))')
            result = subprocess.run([sys.executable, '-c', code], cwd=base,
                                    text=True, capture_output=True, check=True)
            self.assertEqual(json.loads(result.stdout),
                             [str(repo / '.lake/build/literate-html'), str(repo / '.lake/build/doc')])
