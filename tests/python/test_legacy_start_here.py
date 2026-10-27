import unittest,tempfile,zipfile
from pathlib import Path
from tests.support.legacy_start_here import unpack
class OuterTests(unittest.TestCase):
 def test_safe_extract_preserves_bytes(self):
  with tempfile.TemporaryDirectory() as t:
   p=Path(t);z=p/'a.zip'
   with zipfile.ZipFile(z,'w') as f:f.writestr('dir/x.txt',b'abc\n')
   unpack(z,p/'out');self.assertEqual((p/'out/dir/x.txt').read_bytes(),b'abc\n')
 def test_parent_escape_rejected(self):
  with tempfile.TemporaryDirectory() as t:
   p=Path(t);z=p/'a.zip'
   with zipfile.ZipFile(z,'w') as f:f.writestr('../escape',b'x')
   with self.assertRaises(ValueError):unpack(z,p/'out')
   self.assertFalse((p/'escape').exists())
 def test_absolute_rejected(self):
  with tempfile.TemporaryDirectory() as t:
   p=Path(t);z=p/'a.zip'
   with zipfile.ZipFile(z,'w') as f:f.writestr('/tmp/escape',b'x')
   with self.assertRaises(ValueError):unpack(z,p/'out')
 def test_symlink_rejected(self):
  with tempfile.TemporaryDirectory() as t:
   p=Path(t);z=p/'a.zip';i=zipfile.ZipInfo('link');i.external_attr=(0o120777<<16)
   with zipfile.ZipFile(z,'w') as f:f.writestr(i,'/tmp')
   with self.assertRaises(ValueError):unpack(z,p/'out')
if __name__=='__main__':unittest.main()
