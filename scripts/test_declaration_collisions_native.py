"""Real Lean regressions for the v2 declaration-collision check (build-tier only)."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
SOURCES = {
    # Two modules that never import each other declare the same name.
    'MathlibExt.CollisionFixture.Original':
        'module\n@[expose] public section\npublic theorem collisionFixture : True := trivial\n',
    'Domains.CollisionFixture.Copy': 'theorem collisionFixture : 1 = 1 := rfl\n',
    # Private names are qualified by their module, so they never collide.
    'CSLibExt.CollisionFixture.PrivateA': 'module\nprivate def helperFixture : Nat := 1\n',
    'WantedExt.CollisionFixture.PrivateB': 'module\nprivate def helperFixture : Nat := 2\n',
    # A non-ASCII file name is read literally.
    'MathlibExt.CollisionFixture.Étale': 'module\npublic def etaleFixture : Nat := 1\n',
    # Test libraries are not imported by the wiki, so the check leaves them out.
    'MathlibExtTest.CollisionFixture.Test': 'theorem collisionFixture : 2 = 2 := rfl\n',
}

DOTTED_SOURCE = 'MathlibExt/CollisionFixture/Finite.Product.lean'


def source_path(module: str) -> str:
    return module.replace('.', '/') + '.lean'


class DeclarationCollisionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if shutil.which('lake') is None:
            raise RuntimeError('native declaration-collision regressions require Lake')
        cls.storage = tempfile.TemporaryDirectory(prefix='atlas-collision-regression-')
        cls.fixture = Path(cls.storage.name)
        for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
            shutil.copyfile(ROOT / name, cls.fixture / name)
        (cls.fixture / 'scripts').mkdir()
        for name in ('check_declaration_collisions.sh', 'check_declaration_collisions.lean',
                     'list_v2_modules.sh'):
            shutil.copy2(ROOT / 'scripts' / name, cls.fixture / 'scripts' / name)
        (cls.fixture / '.lake').mkdir()
        (cls.fixture / '.lake/packages').symlink_to((ROOT / '.lake/packages').resolve(),
                                                    target_is_directory=True)
        for module, text in SOURCES.items():
            path = cls.fixture / source_path(module)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        # Lake builds a file whose name contains a dot as one module component.
        dotted = cls.fixture / DOTTED_SOURCE
        dotted.write_text('module\npublic def dottedFixture : Nat := 1\n')
        result = subprocess.run(['lake', 'build', *('+' + module for module in SOURCES),
                                 '+MathlibExt.CollisionFixture.«Finite.Product»'],
                                cwd=cls.fixture, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        if result.returncode:
            raise RuntimeError(result.stdout[-5000:])
        subprocess.run(['git', 'init', '-q'], cwd=cls.fixture, check=True)

    @classmethod
    def tearDownClass(cls):
        cls.storage.cleanup()

    def check(self, *modules: str, paths: tuple[str, ...] = ()) -> subprocess.CompletedProcess:
        subprocess.run(['git', 'rm', '-q', '--cached', '-r', '--ignore-unmatch', '.'],
                       cwd=self.fixture, check=True)
        subprocess.run(['git', 'add', *map(source_path, modules), *paths], cwd=self.fixture,
                       check=True)
        return subprocess.run(['scripts/check_declaration_collisions.sh'], cwd=self.fixture,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

    def test_collision_between_unrelated_modules_names_both(self):
        result = self.check('MathlibExt.CollisionFixture.Original',
                            'Domains.CollisionFixture.Copy')
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertRegex(result.stderr, r'FAIL \[declaration collisions\]: collisionFixture is '
                                        r'declared in both (MathlibExt\.CollisionFixture\.Original '
                                        r'and Domains\.CollisionFixture\.Copy|Domains\.Collision'
                                        r'Fixture\.Copy and MathlibExt\.CollisionFixture\.Original)\.')

    def test_distinct_and_private_names_pass(self):
        result = self.check('MathlibExt.CollisionFixture.Original',
                            'CSLibExt.CollisionFixture.PrivateA',
                            'WantedExt.CollisionFixture.PrivateB')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('ok [declaration collisions]: 3 modules import together.', result.stdout)

    def test_non_ascii_module_names_are_found(self):
        result = self.check('MathlibExt.CollisionFixture.Original',
                            'MathlibExt.CollisionFixture.Étale')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('ok [declaration collisions]: 2 modules import together.', result.stdout)

    def test_module_paths_that_are_not_identifiers_are_rejected(self):
        # Lake names these modules after their files, but Lean reads `Bad-name` as no
        # module and `«Quoted»` as `Quoted`, so neither could be imported by name.
        listing = self.fixture / 'misnamed-modules.txt'
        listing.write_text('MathlibExt.CollisionFixture.Original\n'
                           'MathlibExt.CollisionFixture.Bad-name\n'
                           'MathlibExt.CollisionFixture.«Quoted»\n', encoding='utf-8')
        result = subprocess.run(['lake', 'env', 'lean', '--run',
                                 'scripts/check_declaration_collisions.lean', str(listing)],
                                cwd=self.fixture, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        for path in ('MathlibExt/CollisionFixture/Bad-name.lean',
                     'MathlibExt/CollisionFixture/«Quoted».lean'):
            self.assertIn(f'FAIL [declaration collisions]: {path}: every directory and file '
                          'name of a module must be a Lean identifier; rename it.',
                          result.stderr)
        self.assertNotIn('Original', result.stderr)

    def test_a_dotted_file_name_is_rejected_by_path(self):
        self.assertTrue((self.fixture / '.lake/build/lib/lean/MathlibExt/CollisionFixture/'
                         'Finite.Product.olean').is_file())
        result = self.check('MathlibExt.CollisionFixture.Original', paths=(DOTTED_SOURCE,))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('Module path is not a Lean module name (a directory or file name contains '
                      f'a dot or a line break): {DOTTED_SOURCE}', result.stderr)
        self.assertIn('FAIL [declaration collisions]: could not list the compiled v2 modules',
                      result.stderr)

    def test_test_libraries_are_not_imported(self):
        result = self.check('MathlibExt.CollisionFixture.Original',
                            'MathlibExtTest.CollisionFixture.Test')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('ok [declaration collisions]: 1 module imports together.', result.stdout)


if __name__ == '__main__':
    unittest.main()
