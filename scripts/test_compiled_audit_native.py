"""Real Lean regressions for isolated compiled policy audits (build-tier only)."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import audit_compiled_modules as audit

ROOT = Path(__file__).resolve().parent.parent
PAIR = ['MathlibExtTest.AlgebraicGeometry.ProjHomExtBasicOpen',
        'MathlibExtTest.AlgebraicGeometry.SeparatedOpenCover']


class CompiledAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if shutil.which('lake') is None:
            raise RuntimeError('native compiled-audit regressions require Lake')
        cls.checker = (ROOT / 'scripts/check_axioms.lean').read_text()
        result = subprocess.run(['lake', 'build', *['+' + name for name in PAIR]], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if result.returncode:
            raise RuntimeError(result.stdout[-5000:])
        cls.storage = tempfile.TemporaryDirectory(prefix='atlas-audit-regression-')
        cls.fixture = Path(cls.storage.name)
        for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
            shutil.copyfile(ROOT / name, cls.fixture / name)
        (cls.fixture / '.lake').mkdir()
        (cls.fixture / '.lake/packages').symlink_to((ROOT / '.lake/packages').resolve(), target_is_directory=True)
        sources = {
            'Forbidden': 'module\n@[expose] public section\naxiom alien : False\ntheorem poisoned : False := alien\n',
            'Implemented': 'module\n@[expose] public section\ndef fast (n : Nat) : Nat := n + 1\n@[implemented_by fast] def substituted (n : Nat) : Nat := n\n',
            'PrivateUnsafe': 'module\nprivate unsafe def unchecked : Nat := 0\n',
        }
        for name, text in sources.items():
            path = cls.fixture / f'MathlibExtTest/AuditFixture/{name}.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        result = subprocess.run(['lake', 'build', *['+MathlibExtTest.AuditFixture.' + name for name in sources]],
                                cwd=cls.fixture, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if result.returncode:
            raise RuntimeError(result.stdout[-5000:])

    @classmethod
    def tearDownClass(cls):
        cls.storage.cleanup()

    def test_actual_import_collision_splits_without_dropping_coverage(self):
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean') as driver:
            driver.write(''.join(f'import {name}\n' for name in PAIR) + self.checker)
            driver.flush()
            result = subprocess.run(['lake', 'env', 'lean', driver.name], cwd=ROOT,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("environment already contains 'exactSource'", result.stdout)
        repaired = audit.audit(ROOT, PAIR, self.checker)
        self.assertEqual(repaired['checkedModules'], PAIR)
        self.assertEqual(repaired['successfulGroups'], 2)
        self.assertEqual(repaired['importCollisionSplits'], 1)

    def test_domain_import_boundary(self):
        sources = {
            'Domains.AuditFixture.Model': 'module\npublic def domainFixture : Nat := 1\n',
            'DomainsTest.AuditFixture.Model': 'module\npublic import Domains.AuditFixture.Model\n',
            'WantedExt.AuditFixture.Model': 'module\npublic import Domains.AuditFixture.Model\n',
            'MathlibExt.AuditFixture.Reverse': 'module\npublic import Domains.AuditFixture.Model\n',
        }
        for module, source in sources.items():
            path = self.fixture.joinpath(*module.split('.')).with_suffix('.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
        subprocess.run(['lake', 'build', *('+' + name for name in sources)], cwd=self.fixture, check=True)
        allowed = ['Domains.AuditFixture.Model', 'DomainsTest.AuditFixture.Model', 'WantedExt.AuditFixture.Model']
        self.assertEqual(audit.audit(self.fixture, allowed, self.checker)['checkedModules'], allowed)
        with self.assertRaisesRegex(audit.AuditFailure,
                                    r'MathlibExt\.AuditFixture\.Reverse must not import Domains\.AuditFixture\.Model'):
            audit.audit(self.fixture, ['MathlibExt.AuditFixture.Reverse'], self.checker)

    def test_forbidden_axiom_still_fails(self):
        with self.assertRaisesRegex(audit.AuditFailure, 'depends on forbidden axioms'):
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.Forbidden'], self.checker)

    def test_implemented_by_still_fails(self):
        with self.assertRaisesRegex(audit.AuditFailure, 'uses implemented_by'):
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.Implemented'], self.checker)

    def test_private_unsafe_still_fails(self):
        with self.assertRaisesRegex(audit.AuditFailure, 'unsafe declaration'):
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.PrivateUnsafe'], self.checker)

    def test_other_import_failure_still_fails(self):
        with self.assertRaisesRegex(audit.AuditFailure, 'does not exist'):
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.Missing'], self.checker)


if __name__ == '__main__':
    unittest.main()
