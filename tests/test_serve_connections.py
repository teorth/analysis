import http.client
from pathlib import Path
import socket
import sys
import threading
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import serve


class TestPreviewConnections(unittest.TestCase):
    def test_idle_preconnection_does_not_block_another_request(self):
        server = serve.ThreadingHTTPServer(('127.0.0.1', 0), serve.CustomHTTPRequestHandler)
        idle = socket.create_connection(server.server_address, timeout=2)
        # Accept the idle connection before the active one is created.
        accepted = threading.Event()
        original = server.get_request

        def get_request():
            result = original()
            accepted.set()
            return result

        server.get_request = get_request
        worker = threading.Thread(target=server.serve_forever, daemon=True)
        worker.start()
        conn = http.client.HTTPConnection(*server.server_address, timeout=2)
        try:
            self.assertTrue(accepted.wait(2))
            conn.request('GET', '/favicon.ico')
            response = conn.getresponse()
            self.assertEqual(response.status, 204)
            response.read()
        finally:
            conn.close()
            idle.close()
            server.shutdown()
            worker.join()
            server.server_close()
