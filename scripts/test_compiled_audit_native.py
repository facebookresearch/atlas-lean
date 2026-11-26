"""Real Lean regressions for isolated compiled policy audits (build-tier only)."""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

import audit_compiled_modules as audit

ROOT = Path(__file__).resolve().parent.parent
# Two fixture modules that never import each other declare one name with different statements.
PAIR = ['MathlibExtTest.AuditFixture.CollisionA', 'MathlibExtTest.AuditFixture.CollisionB']


class CompiledAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if shutil.which('lake') is None:
            raise RuntimeError('native compiled-audit regressions require Lake')
        cls.checker = (ROOT / 'scripts/check_axioms.lean').read_text()
        cls.storage = tempfile.TemporaryDirectory(prefix='atlas-audit-regression-')
        cls.fixture = Path(cls.storage.name)
        for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
            shutil.copyfile(ROOT / name, cls.fixture / name)
        (cls.fixture / '.lake').mkdir()
        (cls.fixture / '.lake/packages').symlink_to((ROOT / '.lake/packages').resolve(), target_is_directory=True)
        sources = {
            'CollisionA': 'module\n@[expose] public section\ntheorem auditCollision : True := trivial\n',
            'CollisionB': 'module\n@[expose] public section\ntheorem auditCollision : 1 = 1 := rfl\n',
            'Forbidden': 'module\n@[expose] public section\naxiom alien : False\ntheorem poisoned : False := alien\n',
            'Implemented': 'module\n@[expose] public section\ndef fast (n : Nat) : Nat := n + 1\n@[implemented_by fast] def substituted (n : Nat) : Nat := n\n',
            'PrivateUnsafe': 'module\nprivate unsafe def unchecked : Nat := 0\n',
            # Lean generates `T.ctorIdx`, and for `T.ctorIdx` the unsafe `T.ctorIdx._impl`, for each of
            # these: several constructors, parameters and indices, a universe, no constructor at all.
            'GeneratedCtorIdx': (
                'module\n@[expose] public section\nuniverse u\n'
                'inductive AuditColour where\n  | red\n  | green\n  | blue\n'
                'inductive AuditTagged (α : Type u) : Nat → Type u where\n'
                '  | zero (a : α) : AuditTagged α 0\n'
                '  | succ (a : α) (n : Nat) (t : AuditTagged α n) : AuditTagged α (n + 1)\n'
                'inductive AuditEmpty : Type\n'
                'structure AuditBox where\n  x : Nat\n'),
            # A hand-written unsafe `_impl` for a type whose generated `ctorIdx` uses none.
            'HandWrittenCtorIdxImpl': (
                'module\n@[expose] public section\n'
                'inductive AuditOne where\n  | only\n'
                'unsafe def AuditOne.ctorIdx._impl (_ : AuditOne) : Nat := 7\n'),
            # A hand-written pair in place of the generated one.
            'HandWrittenCtorIdx': (
                'module\n@[expose] public section\n'
                'set_option genCtorIdx false in\ninductive AuditTwo where\n  | first\n  | second\n'
                'unsafe def AuditTwo.ctorIdx._impl (_ : AuditTwo) : Nat := 7\n'
                '@[implemented_by AuditTwo.ctorIdx._impl] def AuditTwo.ctorIdx (_ : AuditTwo) : Nat := 0\n'),
            # The generated `_impl`, but a `ctorIdx` whose value is not the generated one.
            'ForgedCtorIdxValue': (
                'module\n@[expose] public section\n'
                'set_option genCtorIdx false in\ninductive AuditThree where\n  | first\n  | second\n'
                'unsafe def AuditThree.ctorIdx._impl (x : AuditThree) : Nat := getObjTagNat x\n'
                '@[implemented_by AuditThree.ctorIdx._impl] def AuditThree.ctorIdx (_ : AuditThree) : Nat := 5\n'),
            # A hand-written pair of exactly the generated form: only its declaration ranges tell it apart.
            'ExactHandWrittenCtorIdx': (
                'module\n@[expose] public section\n'
                'set_option genCtorIdx false in\ninductive AuditFour where\n  | first\n  | second\n'
                'unsafe def AuditFour.ctorIdx._impl : AuditFour → Nat := fun x => getObjTagNat x\n'
                '@[implemented_by AuditFour.ctorIdx._impl] def AuditFour.ctorIdx : AuditFour → Nat :=\n'
                '  fun x => AuditFour.casesOn (motive := fun _ => Nat) x (nat_lit 0) (nat_lit 1)\n'),
            # Pairs a metaprogram adds, so without declaration ranges, that differ from the generated pair in
            # one part only: each shape check must reject its part on its own.
            'RangeFreeForgedImpl': (
                'import Lean\n'
                'set_option genCtorIdx false in\ninductive AuditFive where\n  | first\n  | second\n'
                'open Lean Meta in\nrun_meta do\n'
                '  let T := `AuditFive\n'
                '  let ty ← mkArrow (mkConst T) (mkConst ``Nat)\n'
                '  let impl := Expr.lam `x (mkConst T) (mkRawNatLit 7) .default\n'
                '  addDecl (.defnDecl { name := `AuditFive.ctorIdx._impl, levelParams := [], type := ty, '
                'value := impl, hints := ReducibilityHints.opaque, safety := DefinitionSafety.unsafe })\n'
                '  let motive := Expr.lam `x (mkConst T) (mkConst ``Nat) .default\n'
                '  let value := Expr.lam `x (mkConst T) (mkAppN (mkConst `AuditFive.casesOn [Level.one]) '
                '#[motive, .bvar 0, mkRawNatLit 0, mkRawNatLit 1]) .default\n'
                '  addDecl (.defnDecl { name := `AuditFive.ctorIdx, levelParams := [], type := ty, '
                'value := value, hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe })\n'
                '  setImplementedBy `AuditFive.ctorIdx `AuditFive.ctorIdx._impl\n'),
            'RangeFreeForgedValue': (
                'import Lean\n'
                'set_option genCtorIdx false in\ninductive AuditSix where\n  | first\n  | second\n'
                'open Lean Meta in\nrun_meta do\n'
                '  let T := `AuditSix\n'
                '  let ty ← mkArrow (mkConst T) (mkConst ``Nat)\n'
                '  let impl := Expr.lam `x (mkConst T) (mkAppN (mkConst ``getObjTagNat [Level.one]) '
                '#[mkConst T, .bvar 0]) .default\n'
                '  addDecl (.defnDecl { name := `AuditSix.ctorIdx._impl, levelParams := [], type := ty, '
                'value := impl, hints := ReducibilityHints.opaque, safety := DefinitionSafety.unsafe })\n'
                '  let value := Expr.lam `x (mkConst T) (mkRawNatLit 5) .default\n'
                '  addDecl (.defnDecl { name := `AuditSix.ctorIdx, levelParams := [], type := ty, '
                'value := value, hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe })\n'
                '  setImplementedBy `AuditSix.ctorIdx `AuditSix.ctorIdx._impl\n'),
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
            result = subprocess.run(['lake', 'env', 'lean', driver.name], cwd=self.fixture,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("environment already contains 'auditCollision'", result.stdout)
        repaired = audit.audit(self.fixture, PAIR, self.checker)
        self.assertEqual(repaired['checkedModules'], PAIR)
        self.assertEqual(repaired['successfulGroups'], 2)
        self.assertEqual(repaired['importCollisionSplits'], 1)

    def test_domain_import_boundary(self):
        sources = {
            'PhyslibExt.AuditFixture.Model': 'module\npublic def physicsFixture : Nat := 1\n',
            'Domains.AuditFixture.Model': (
                'module\npublic import PhyslibExt.AuditFixture.Model\n'
                'public def domainFixture : Nat := physicsFixture\n'),
            'DomainsTest.AuditFixture.Model': 'module\npublic import Domains.AuditFixture.Model\n',
            'WantedExt.AuditFixture.Model': (
                'module\npublic import Batteries.Util.ProofWanted\n'
                'public import Domains.AuditFixture.Model\n'
                'public theorem_wanted domainFixtureWanted : domainFixture = 1\n'),
            'WantedExt.AuditFixture.Physics': (
                'module\npublic import Batteries.Util.ProofWanted\n'
                'public import PhyslibExt.AuditFixture.Model\n'
                'public theorem_wanted physicsFixtureWanted : physicsFixture = 1\n'),
        }
        allowed = list(sources)
        forbidden = {}
        for library in ('MathlibExt', 'CSLibExt', 'PhyslibExt'):
            forbidden[f'{library}.AuditFixture.DomainImport'] = 'Domains.AuditFixture.Model'
        for library in audit.ROOTS:
            if library != 'WantedExt':
                forbidden[f'{library}.AuditFixture.WantedImport'] = 'WantedExt.AuditFixture.Model'
        for library in ('MathlibExt', 'CSLibExt', 'PhyslibExt', 'Domains', 'WantedExt'):
            forbidden[f'{library}.AuditFixture.TestImport'] = 'DomainsTest.AuditFixture.Model'
        forbidden['WantedExt.AuditFixture.FoundationTestImport'] = PAIR[0]
        for module, target in forbidden.items():
            sources[module] = f'module\npublic import {target}\n'
        for module, source in sources.items():
            path = self.fixture.joinpath(*module.split('.')).with_suffix('.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
        subprocess.run(['lake', 'build', *('+' + name for name in sources)], cwd=self.fixture, check=True)
        self.assertEqual(audit.audit(self.fixture, allowed, self.checker)['checkedModules'], allowed)
        for module, target in forbidden.items():
            with self.subTest(module=module), self.assertRaisesRegex(
                    audit.AuditFailure, re.escape(f'{module} must not import {target}')):
                audit.audit(self.fixture, [module], self.checker)

    def test_domain_wanted_declaration_still_fails(self):
        module = 'Domains.AuditFixture.WantedDeclaration'
        path = self.fixture.joinpath(*module.split('.')).with_suffix('.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            'module\npublic import Batteries.Util.ProofWanted\n'
            'public theorem_wanted misplacedDomainWanted : True\n')
        subprocess.run(['lake', 'build', '+' + module], cwd=self.fixture, check=True)
        with self.assertRaisesRegex(audit.AuditFailure,
                                    re.escape(f'{module} contains a wanted declaration outside WantedExt')):
            audit.audit(self.fixture, [module], self.checker)

    def test_forbidden_axiom_still_fails(self):
        with self.assertRaisesRegex(audit.AuditFailure, 'depends on forbidden axioms'):
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.Forbidden'], self.checker)

    def test_implemented_by_still_fails(self):
        with self.assertRaisesRegex(audit.AuditFailure, 'uses implemented_by'):
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.Implemented'], self.checker)

    def test_private_unsafe_still_fails(self):
        with self.assertRaisesRegex(audit.AuditFailure, 'unsafe declaration'):
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.PrivateUnsafe'], self.checker)

    def test_generated_ctor_idx_passes(self):
        module = 'MathlibExtTest.AuditFixture.GeneratedCtorIdx'
        self.assertEqual(audit.audit(self.fixture, [module], self.checker)['checkedModules'], [module])

    def test_hand_written_ctor_idx_impl_fails(self):
        with self.assertRaisesRegex(audit.AuditFailure, r'AuditOne\.ctorIdx\._impl is an unsafe declaration'):
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.HandWrittenCtorIdxImpl'], self.checker)

    def test_hand_written_ctor_idx_pair_fails(self):
        with self.assertRaises(audit.AuditFailure) as failure:
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.HandWrittenCtorIdx'], self.checker)
        self.assertIn('AuditTwo.ctorIdx._impl is an unsafe declaration', str(failure.exception))
        self.assertIn('AuditTwo.ctorIdx uses implemented_by', str(failure.exception))

    def test_forged_ctor_idx_value_fails(self):
        with self.assertRaises(audit.AuditFailure) as failure:
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.ForgedCtorIdxValue'], self.checker)
        self.assertIn('AuditThree.ctorIdx._impl is an unsafe declaration', str(failure.exception))
        self.assertIn('AuditThree.ctorIdx uses implemented_by', str(failure.exception))

    def test_exact_hand_written_ctor_idx_pair_fails(self):
        with self.assertRaises(audit.AuditFailure) as failure:
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.ExactHandWrittenCtorIdx'], self.checker)
        self.assertIn('AuditFour.ctorIdx._impl is an unsafe declaration', str(failure.exception))
        self.assertIn('AuditFour.ctorIdx uses implemented_by', str(failure.exception))

    def test_range_free_forged_impl_fails(self):
        with self.assertRaises(audit.AuditFailure) as failure:
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.RangeFreeForgedImpl'], self.checker)
        self.assertIn('AuditFive.ctorIdx._impl is an unsafe declaration', str(failure.exception))
        self.assertIn('AuditFive.ctorIdx uses implemented_by', str(failure.exception))

    def test_range_free_forged_value_fails(self):
        with self.assertRaises(audit.AuditFailure) as failure:
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.RangeFreeForgedValue'], self.checker)
        self.assertIn('AuditSix.ctorIdx._impl is an unsafe declaration', str(failure.exception))
        self.assertIn('AuditSix.ctorIdx uses implemented_by', str(failure.exception))

    def test_other_import_failure_still_fails(self):
        with self.assertRaisesRegex(audit.AuditFailure, 'does not exist'):
            audit.audit(self.fixture, ['MathlibExtTest.AuditFixture.Missing'], self.checker)


if __name__ == '__main__':
    unittest.main()
