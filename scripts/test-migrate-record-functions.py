#!/usr/bin/env python3
"""Structural migration checks; no compiler compatibility mode is involved."""

import importlib.util
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location(
    "migrate_record_functions", Path(__file__).with_name("migrate-record-functions.py")
)
migration = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = migration
spec.loader.exec_module(migration)


class MigrationTests(unittest.TestCase):
    def migrate(self, source):
        result = migration.migrate_source(source)
        self.assertEqual(migration.migrate_source(result), result, "migration must be idempotent")
        comments = lambda text: [match.group() for match in migration.TOKEN.finditer(text)
                                 if match.group().startswith("//")]
        self.assertEqual(comments(result), comments(source), "comments must survive in order")
        return result

    def test_body_contracts_mutability_and_literals_stay_exact(self):
        body = '\n  // body comment\n  (#requires (#u64::lt value 100u64))\n  (#let text (#array #char 6) "// (){}")\n  (#return value)'
        source = '// λ\n#fn keep ((#mut value #u64)) #u64' + body + '\n'
        result = self.migrate(source)
        self.assertIn('#params = ((#mut value #u64));', result)
        self.assertIn('#returns = #u64;', result)
        self.assertIn('#body = (' + body, result)

    def test_cfg_declarations_convert_but_generator_function_data_does_not(self):
        data = '#gn emit () `((#fn generated () #u64 (#return 42u64)))\n#generate #async-fn ((function (#fn work () #u64 (#return 42u64))))\n'
        source = data + '#cfg-if (#cfg-is #feature enabled)\n  (#fn yes () #u64 (#return 1u64))\n  (#cfg-else (#cfg-if (#cfg-is #mode slow) (#unsafe-fn no () () (#return ()))) )\n'
        result = self.migrate(source)
        self.assertTrue(result.startswith(data))
        self.assertIn('(#fn yes {', result)
        self.assertIn('(#unsafe-fn no {', result)
        self.assertEqual(result.count('#body ='), 2)

    def test_extern_abi_parameters_and_comments_are_preserved(self):
        source = '#extern-fn // convention\n  #abi-c // binding\n  print ((value #u64)) ()\n'
        result = self.migrate(source)
        self.assertIn('#abi = #abi-c;', result)
        self.assertIn('#params = ((value #u64));', result)
        self.assertIn('#returns = ();', result)
        self.assertNotIn('#body', result)

    def test_named_sections_become_record_fields(self):
        source = '#fn keep (#params { value = #u64; }) (#returns #u64) (#requires (#u64::lt value 100u64)) (#body (#return value))\n'
        result = self.migrate(source)
        self.assertIn('#params = { value = #u64; };', result)
        self.assertIn('#requires = ( (#u64::lt value 100u64));', result)
        self.assertIn('#body = ( (#return value));', result)

    def test_adjacent_comments_and_inline_root_separators(self):
        source = '#fn first () #u64// return type\n  (#return 1u64)\n; #fn second () #u64 (#return 2u64)\n'
        result = self.migrate(source)
        self.assertIn('}\n; #fn second {', result)
        self.assertIn('#returns = #u64;', result)
        self.assertIn('// return type', result)

    def test_existing_records_and_quoted_root_data_are_unchanged(self):
        for source in [
            '#fn answer { #params = {}; #returns = #u64; #body: #return 42; }\n',
            '#extern-fn print { #abi = #abi-c; #params = { value = #u64; }; #returns = (); }\n',
            '#generate #array:\n  element #u64;\n  length 4;\n  name Array4;\n',
            "'(#fn literal () #u64 (#return 42u64))\n",
        ]:
            self.assertEqual(self.migrate(source), source)

    def test_malformed_and_unclassified_fixtures_are_reported(self):
        for source in [
            '#fn incomplete (',
            '#fn header-only () #u64',
            '#fn main () #u64 (#return "unterminated)',
            '#fn main () #u64 (#return 42u64)]',
            '(#fn literal () #u64 (#return 42u64))',
            '#extern-fn #abi-c foreign () () (#return ())',
        ]:
            with self.assertRaises(migration.MigrationError, msg=source):
                migration.migrate_source(source)


if __name__ == '__main__':
    unittest.main()
