import http.client
from http.server import HTTPServer
from pathlib import Path
import sys
import threading
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from serve import CustomHTTPRequestHandler


class TestRedirects(unittest.TestCase):
    def test_get_and_head_preserve_queries_on_canonical_redirects(self):
        server = HTTPServer(('127.0.0.1', 0), CustomHTTPRequestHandler)
        worker = threading.Thread(target=server.serve_forever, daemon=True)
        worker.start()
        try:
            for method in ('GET', 'HEAD'):
                for path in ('/', '/analysis'):
                    with self.subTest(method=method, path=path):
                        conn = http.client.HTTPConnection(*server.server_address, timeout=2)
                        try:
                            conn.request(method, path + '?q=compact%20sets')
                            response = conn.getresponse()
                            self.assertEqual(response.status, 301)
                            self.assertEqual(response.getheader('Location'),
                                             '/analysis/?q=compact%20sets')
                            response.read()
                        finally:
                            conn.close()
        finally:
            server.shutdown()
            worker.join()
            server.server_close()
