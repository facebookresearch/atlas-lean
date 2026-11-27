"""Real Lean regressions for the declaration-collision check (build-tier only)."""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

import audit_compiled_modules as audit

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
    # The compiled audit imports the test libraries with the others, so the check does too.
    'MathlibExtTest.CollisionFixture.Test': 'theorem collisionFixture : 2 = 2 := rfl\n',
    # A test's own private helper is qualified by its module.
    'CSLibExtTest.CollisionFixture.PrivateTest':
        'module\nprivate theorem collisionFixture : 3 = 3 := rfl\n',
    # Two modules that sort first and last declare one name, so that only an import of every
    # module at once, not one in smaller groups, meets both.
    'CSLibExt.CollisionFixture.AFirst': 'theorem farCollisionFixture : True := trivial\n',
    'WantedExt.CollisionFixture.ZLast': 'theorem farCollisionFixture : 1 = 1 := rfl\n',
    # Two modules whose declarations differ but whose initializers register the same option:
    # they load together only if their initializers are not run. They also sort first and last.
    'CSLibExt.CollisionFixture.AOption':
        'import Lean\ninitialize optionFixtureA : Lean.Option Bool ←\n'
        '  Lean.Option.register `collisionFixture.option { defValue := false, descr := "A" }\n',
    'WantedExt.CollisionFixture.ZOption':
        'import Lean\ninitialize optionFixtureZ : Lean.Option Bool ←\n'
        '  Lean.Option.register `collisionFixture.option { defValue := true, descr := "Z" }\n',
    # An initializer whose error reads like Lean's collision error, without being one.
    'DomainsTest.CollisionFixture.FailingInit':
        'import Lean\ninitialize do\n  throw <| IO.userError "schema import validation failed, '
        'environment already contains \'sample\' from defaults"\n',
}

DOTTED_SOURCE = 'MathlibExt/CollisionFixture/Finite.Product.lean'
# `CSLibExtTest/CollisionFixture/PrivateTest.lean` renamed so that it keeps its flattened module
# name, now declaring a public `collisionFixture`.
RENAMED_SOURCE = 'CSLibExtTest/CollisionFixture.PrivateTest.lean'


def source_path(module: str) -> str:
    return module.replace('.', '/') + '.lean'


TEXTS = {**{source_path(module): text for module, text in SOURCES.items()},
         DOTTED_SOURCE: 'module\npublic def dottedFixture : Nat := 1\n',
         RENAMED_SOURCE: 'theorem collisionFixture : 4 = 4 := rfl\n'}


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
                     'list_v2_modules.sh', 'audit_compiled_modules.py'):
            shutil.copy2(ROOT / 'scripts' / name, cls.fixture / 'scripts' / name)
        (cls.fixture / '.lake').mkdir()
        (cls.fixture / '.lake/packages').symlink_to((ROOT / '.lake/packages').resolve(),
                                                    target_is_directory=True)
        # The compiled audit's inventory needs every library it audits.
        for library in audit.ROOTS:
            (cls.fixture / library).mkdir()
        # Lake builds a file whose name contains a dot as one module component.
        for path, text in TEXTS.items():
            (cls.fixture / path).parent.mkdir(parents=True, exist_ok=True)
            (cls.fixture / path).write_text(text)
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

    def check(self, *modules: str, paths: tuple[str, ...] = (), untracked: tuple[str, ...] = (),
              deleted: tuple[str, ...] = (),
              directories: tuple[str, ...] = ()) -> subprocess.CompletedProcess:
        # The compiled audit imports every source file of its libraries, tracked or not, so
        # the working tree holds only this case's sources; every .olean stays built. After
        # they are tracked, `deleted` sources are removed and `directories` replace sources.
        tracked = [*map(source_path, modules), *paths]
        for path, text in TEXTS.items():
            target = self.fixture / path
            if target.is_dir():
                target.rmdir()
            if path in tracked or path in untracked:
                target.write_text(text)
            else:
                target.unlink(missing_ok=True)
        subprocess.run(['git', 'rm', '-q', '--cached', '-r', '--ignore-unmatch', '.'],
                       cwd=self.fixture, check=True)
        subprocess.run(['git', 'add', *tracked], cwd=self.fixture, check=True)
        for path in (*deleted, *directories):
            (self.fixture / path).unlink()
        for path in directories:
            (self.fixture / path).mkdir()
        return subprocess.run(['scripts/check_declaration_collisions.sh'], cwd=self.fixture,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

    def assertCollision(self, result: subprocess.CompletedProcess, declaration: str,
                        *modules: str):
        # Lean reports the module it was importing and a module it says already holds the name.
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        report = re.search(r'^FAIL \[declaration collisions\]: could not import the modules '
                           r'together: import (\S+) failed, environment already contains '
                           rf"'{re.escape(declaration)}' from (\S+)$", result.stderr, re.MULTILINE)
        self.assertIsNotNone(report, result.stderr)
        self.assertEqual(sorted(report.groups()), sorted(modules))
        self.assertIn('If two modules declare one name, keep one declaration', result.stderr)

    def test_collision_between_unrelated_modules_names_both(self):
        result = self.check('MathlibExt.CollisionFixture.Original',
                            'Domains.CollisionFixture.Copy')
        self.assertCollision(result, 'collisionFixture', 'MathlibExt.CollisionFixture.Original',
                             'Domains.CollisionFixture.Copy')

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
        self.assertIn('FAIL [declaration collisions]: could not list the compiled modules',
                      result.stderr)

    def test_collision_with_a_test_library_names_both(self):
        result = self.check('MathlibExt.CollisionFixture.Original',
                            'MathlibExtTest.CollisionFixture.Test')
        self.assertCollision(result, 'collisionFixture', 'MathlibExt.CollisionFixture.Original',
                             'MathlibExtTest.CollisionFixture.Test')

    def test_untracked_audited_source_fails(self):
        # The compiled audit reads the untracked copy too.
        result = self.check('MathlibExt.CollisionFixture.Original',
                            untracked=(source_path('Domains.CollisionFixture.Copy'),))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('FAIL [declaration collisions]: Domains/CollisionFixture/Copy.lean is not '
                      'tracked by Git, but the compiled audit reads it; add it, or remove it.',
                      result.stderr)
        self.assertNotIn('import together', result.stdout)

    # Modules that sort between the first and last fixtures and collide with neither.
    BETWEEN = ('CSLibExt.CollisionFixture.PrivateA', 'CSLibExtTest.CollisionFixture.PrivateTest',
               'Domains.CollisionFixture.Copy', 'MathlibExt.CollisionFixture.Étale',
               'WantedExt.CollisionFixture.PrivateB')

    def test_collision_between_the_first_and_last_modules_fails(self):
        result = self.check('CSLibExt.CollisionFixture.AFirst', *self.BETWEEN,
                            'WantedExt.CollisionFixture.ZLast')
        self.assertCollision(result, 'farCollisionFixture', 'CSLibExt.CollisionFixture.AFirst',
                             'WantedExt.CollisionFixture.ZLast')

    def test_initializers_that_conflict_fail(self):
        # The compiled audit imports as `lean` does, running every initializer.
        result = self.check('CSLibExt.CollisionFixture.AOption', *self.BETWEEN,
                            'WantedExt.CollisionFixture.ZOption')
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('FAIL [declaration collisions]: could not import the modules together:',
                      result.stderr)
        self.assertIn('collisionFixture.option', result.stderr)
        self.assertNotIn('If two modules declare one name', result.stderr)

    def test_other_import_errors_are_reported_as_they_are(self):
        result = self.check('MathlibExt.CollisionFixture.Original',
                            'DomainsTest.CollisionFixture.FailingInit')
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("FAIL [declaration collisions]: could not import the modules together: "
                      "schema import validation failed, environment already contains 'sample' "
                      "from defaults\n", result.stderr)

    def test_collision_a_group_boundary_apart_names_both(self):
        # The pair is 1,024 places apart, as two of the audit's groups would hold them, with
        # 1,023 distinct compiled modules of Lean itself between them.
        prefix = subprocess.run(['lean', '--print-prefix'], cwd=self.fixture, check=True,
                                stdout=subprocess.PIPE, text=True).stdout.strip()
        library = Path(prefix) / 'lib/lean'
        between = sorted(path.relative_to(library).with_suffix('').as_posix().replace('/', '.')
                         for path in (library / 'Lean').rglob('*.olean'))[:1023]
        self.assertEqual(len(between), 1023)
        listing = self.fixture / 'far-apart-modules.txt'
        listing.write_text('\n'.join(['CSLibExt.CollisionFixture.AFirst', *between,
                                      'WantedExt.CollisionFixture.ZLast']) + '\n',
                           encoding='utf-8')
        result = subprocess.run(['lake', 'env', 'lean', '--run',
                                 'scripts/check_declaration_collisions.lean', str(listing)],
                                cwd=self.fixture, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True)
        self.assertCollision(result, 'farCollisionFixture', 'CSLibExt.CollisionFixture.AFirst',
                             'WantedExt.CollisionFixture.ZLast')

    def test_initializers_run(self):
        result = self.check('MathlibExt.CollisionFixture.Original',
                            'WantedExt.CollisionFixture.ZOption')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('ok [declaration collisions]: 2 modules import together.', result.stdout)

    def test_source_renamed_to_the_same_module_name_fails(self):
        # The untracked `CollisionFixture.PrivateTest.lean` flattens to the module name of the
        # tracked, deleted `CollisionFixture/PrivateTest.lean`, whose .olean is still built.
        old = source_path('CSLibExtTest.CollisionFixture.PrivateTest')
        result = self.check('MathlibExt.CollisionFixture.Original',
                            'CSLibExtTest.CollisionFixture.PrivateTest',
                            deleted=(old,), untracked=(RENAMED_SOURCE,))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(f'FAIL [declaration collisions]: {RENAMED_SOURCE} is not tracked by Git, '
                      'but the compiled audit reads it; add it, or remove it.', result.stderr)
        self.assertIn(f"FAIL [declaration collisions]: {old} is tracked by Git, but the compiled "
                      "audit's walk of its libraries does not find it.", result.stderr)
        self.assertNotIn('import together', result.stdout)

    def test_directory_in_place_of_a_source_fails(self):
        old = source_path('CSLibExtTest.CollisionFixture.PrivateTest')
        result = self.check('MathlibExt.CollisionFixture.Original',
                            'CSLibExtTest.CollisionFixture.PrivateTest', directories=(old,))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(f'FAIL [declaration collisions]: {old} is not a regular file.',
                      result.stderr)
        self.assertNotIn('import together', result.stdout)

    def test_private_test_helpers_pass(self):
        result = self.check('MathlibExt.CollisionFixture.Original',
                            'CSLibExtTest.CollisionFixture.PrivateTest')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('ok [declaration collisions]: 2 modules import together.', result.stdout)


if __name__ == '__main__':
    unittest.main()
