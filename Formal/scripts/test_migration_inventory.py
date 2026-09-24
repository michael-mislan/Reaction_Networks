"""Regression checks against false migration completion or historical passes."""
import json,tempfile,unittest
from pathlib import Path
from paper_inventory import EXPECTED_IDS,validate
from historical_evidence import validate as validate_history
from historical_evidence import digest
from lean_source import theorem_header
from historical_evidence import parse_receipt
from check_integrity import reading_copy_matches

class ReadingCopyTests(unittest.TestCase):
    def test_changed_reading_copy_cannot_pass(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);source=root/'paper.pdf';reading=root/'P001-paper.pdf'
            source.write_bytes(b'original');reading.write_bytes(b'original')
            entry={'source':source.name,'pdf':reading.name,'sha256':digest(source)}
            self.assertTrue(reading_copy_matches(root,entry))
            reading.write_bytes(b'changed')
            self.assertFalse(reading_copy_matches(root,entry))

    def test_missing_source_cannot_pass(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);reading=root/'P001-paper.pdf';reading.write_bytes(b'original')
            self.assertFalse(reading_copy_matches(root,{'source':'missing.pdf','pdf':reading.name,'sha256':digest(reading)}))

class ConsoleReceiptTests(unittest.TestCase):
    def test_exact_success_trailer(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'receipt.txt'
            for trailer in ['EXIT 0','exit=0']:
                p.write_text('progress\n{"verified":true,"exit_code":0}\n'+trailer+'\n')
                self.assertTrue(parse_receipt(p)['verified'])

    def test_rejects_other_or_inconsistent_trailers(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'receipt.txt'
            for body in ['{"verified":true,"exit_code":0}\nEXIT 1',
                         '{"verified":false,"exit_code":0}\nEXIT 0',
                         '{"verified":true,"exit_code":1}\nEXIT 0',
                         '{"verified":true,"exit_code":0}\nEXIT 0\nextra']:
                p.write_text(body)
                with self.assertRaises(ValueError):parse_receipt(p)

class SourceHeaderTests(unittest.TestCase):
    def test_retains_let_bound_quantities_in_the_statement(self):
        header='theorem design (n : Nat) :\n let V := n + 1\n let R := V * 10\n R > V'
        self.assertEqual(theorem_header(header+' := by omega','design'),header)

    def test_skips_proof_assignments_in_binders_and_comments(self):
        header='theorem source (n : Nat := 1) /- := ignored /- nested -/ -/ :\n (let x := n; x) = n'
        self.assertEqual(theorem_header(header+' := by rfl','source'),header)

    def test_dotted_declaration_name(self):
        self.assertEqual(theorem_header('theorem Foo.bound : True := trivial','Foo.bound'),'theorem Foo.bound : True')

class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.rows=[{'id':p,'mapping_status':'VERIFIED','copy_status':'COPIED','hash_status':'PASS','dependency_status':'COMPLETE'} for p in EXPECTED_IDS[:60]]
        self.manifest={'expected_ids':EXPECTED_IDS,'papers':[{'id':p,'status':'ACCEPTED' if i<60 else 'PENDING_SOURCE_REVIEW'} for i,p in enumerate(EXPECTED_IDS)]}

    def test_partial_collection_keeps_twenty_two_pending(self):
        self.assertEqual(len(validate(self.manifest,self.rows)),22)

    def test_missing_expected_paper_is_error(self):
        self.manifest['papers'].pop()
        with self.assertRaises(ValueError):validate(self.manifest,self.rows)

    def test_duplicate_dossier_is_error(self):
        with self.assertRaises(ValueError):validate(self.manifest,self.rows+[self.rows[0]])

    def test_removing_accepted_dossier_is_error(self):
        with self.assertRaises(ValueError):validate(self.manifest,self.rows[1:])

    def test_unfinished_gate_cannot_be_accepted(self):
        self.rows[0]['dependency_status']='INCOMPLETE'
        with self.assertRaises(ValueError):validate(self.manifest,self.rows)

    def test_reduced_denominator_is_error(self):
        self.manifest['expected_ids']=EXPECTED_IDS[:60]
        with self.assertRaises(ValueError):validate(self.manifest,self.rows)

    def test_missing_historical_record_is_error(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(FileNotFoundError):
                validate_history(Path(directory),{'id':'P061','historical_verification':'missing.json'})

class HistoricalClosureTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.write('mathlib4_project/lean-toolchain','leanprover/lean4:v4.30.0')
        self.write('mathlib4_project/lake-manifest.json','{}')
        self.manifest=digest(self.root/'mathlib4_project/lake-manifest.json')
        self.write('proofs/Base.lean','import Mathlib\n')
        self.write('proofs/Root.lean','import proofs.Base\n')
        self.dump('migration/modules.json',[{'module':'proofs.Base','imports':['Mathlib']},{'module':'proofs.Root','imports':['proofs.Base']}])
        self.history=[]
        for name in ['Base','Root']:
            deps=[] if name=='Base' else [{'module':'proofs.Base','source_sha256':digest(self.root/'proofs/Base.lean'),'cache_key':'base-key'}]
            receipt={'verified':True,'exit_code':0,'stdout':'','stderr':'','proof_sha256':digest(self.root/f'proofs/{name}.lean'),
                     'lean_toolchain':'leanprover/lean4:v4.30.0','lake_manifest_sha256':self.manifest,
                     'target_compilation':{'warning_as_error':True},'verified_module_artifact':{'cache_key':name.lower()+'-key'},
                     'dependency_materialization':{'status':'complete','dependencies':deps},'declaration_interfaces':[]}
            self.dump(name+'.json',receipt)
            self.history.append({'module':'proofs.'+name,'source':f'proofs/{name}.lean','source_sha256':receipt['proof_sha256'],
                                 'receipt':name+'.json','receipt_sha256':digest(self.root/(name+'.json')),
                                 'local_dependencies':deps,'probed_declarations':[]})
        self.row={'id':'P062','closure':['proofs/Base.lean','proofs/Root.lean'],'historical_verification':'history.json'}
        self.record={'paper_id':'P062','fresh_destination_run':False,'status':'SOURCE_AND_ENVIRONMENT_MATCHED',
                     'lean_toolchain':'leanprover/lean4:v4.30.0','lake_manifest_sha256':self.manifest,'modules':self.history}
        self.dump('history.json',self.record)

    def write(self,path,text):
        p=self.root/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text,encoding='utf8')

    def dump(self,path,value):self.write(path,json.dumps(value))

    def test_matching_transitive_receipts_pass(self):validate_history(self.root,self.row)

    def test_changed_dependency_source_fails(self):
        self.write('proofs/Base.lean','import Mathlib\n-- changed source\n')
        with self.assertRaises(AssertionError):validate_history(self.root,self.row)

    def test_omitted_dependency_receipt_fails(self):
        self.record['modules']=self.history[1:];self.dump('history.json',self.record)
        with self.assertRaises((AssertionError,KeyError)):validate_history(self.root,self.row)

    def test_root_receipt_cannot_omit_imported_dependency(self):
        r=json.loads((self.root/'Root.json').read_text());r['dependency_materialization']['dependencies']=[]
        self.dump('Root.json',r);self.history[1]['receipt_sha256']=digest(self.root/'Root.json')
        self.history[1]['local_dependencies']=[];self.dump('history.json',self.record)
        with self.assertRaises(AssertionError):validate_history(self.root,self.row)

    def use_root_closure_record(self):
        self.record.pop('modules')
        self.record['receipt_closures']=[{'root_module':'proofs.Root','receipt':'Root.json',
          'receipt_sha256':digest(self.root/'Root.json'),
          'source_hashes':{m['module']:m['source_sha256'] for m in self.history},'probed_declarations':[]}]
        self.dump('history.json',self.record)

    def test_root_closure_receipt_passes(self):
        self.use_root_closure_record();validate_history(self.root,self.row)

    def test_root_closure_rejects_changed_dependency(self):
        self.use_root_closure_record();self.write('proofs/Base.lean','changed')
        with self.assertRaises(AssertionError):validate_history(self.root,self.row)

    def test_root_closure_rejects_uncovered_import(self):
        self.use_root_closure_record();self.write('proofs/Extra.lean','import Mathlib\n')
        self.dump('migration/modules.json',[{'module':'proofs.Base','imports':['Mathlib']},
          {'module':'proofs.Extra','imports':['Mathlib']},{'module':'proofs.Root','imports':['proofs.Base','proofs.Extra']}])
        self.row['closure'].append('proofs/Extra.lean')
        with self.assertRaises(AssertionError):validate_history(self.root,self.row)

    def test_root_closure_rejects_import_cycle(self):
        self.use_root_closure_record()
        self.dump('migration/modules.json',[{'module':'proofs.Base','imports':['proofs.Root']},
          {'module':'proofs.Root','imports':['proofs.Base']}])
        with self.assertRaises(AssertionError):validate_history(self.root,self.row)

    def use_source_only_record(self):
        self.use_root_closure_record()
        self.write('proofs/Legacy.lean','import Mathlib\nnamespace PhenotypeIdentification\ntheorem sample : True := trivial\nend PhenotypeIdentification\n')
        self.write('legacy_verifier.py',"command = ['lean', '-DwarningAsError=true']\n")
        receipt={'toolchain':'leanprover/lean4:v4.30.0','modules':{'Legacy':{'exit_code':0,
          'sha256':digest(self.root/'proofs/Legacy.lean'),'stdout':'','stderr':''}},
          'axiom_probe':{'exit_code':0,'stderr':'','declarations':['sample'],
                         'stdout':"'PhenotypeIdentification.sample' depends on axioms: [propext]"}}
        self.dump('legacy.json',receipt)
        self.record['source_only_receipts']=[{'schema':'phenotype-identification-standalone-v1',
          'module':'proofs.Legacy','receipt_module':'Legacy','source_sha256':receipt['modules']['Legacy']['sha256'],
          'receipt':'legacy.json','receipt_sha256':digest(self.root/'legacy.json'),
          'verifier':'legacy_verifier.py','verifier_sha256':digest(self.root/'legacy_verifier.py'),
          'mathlib_manifest_recorded':False,'probed_axioms':{'PhenotypeIdentification.sample':['propext']}}]
        self.record['status']='SOURCE_MATCHED_WITH_PARTIAL_ENVIRONMENT_EVIDENCE'
        self.row['closure'].append('proofs/Legacy.lean')
        self.dump('migration/modules.json',[{'module':'proofs.Base','imports':['Mathlib']},
          {'module':'proofs.Root','imports':['proofs.Base']},{'module':'proofs.Legacy','imports':['Mathlib']}])
        self.dump('history.json',self.record)

    def test_source_only_history_requires_explicit_partial_status(self):
        self.use_source_only_record();validate_history(self.root,self.row)
        self.record['status']='SOURCE_AND_ENVIRONMENT_MATCHED';self.dump('history.json',self.record)
        with self.assertRaises(AssertionError):validate_history(self.root,self.row)

    def test_source_only_history_rejects_changed_source(self):
        self.use_source_only_record();self.write('proofs/Legacy.lean','changed')
        with self.assertRaises(AssertionError):validate_history(self.root,self.row)

    def test_source_only_history_cannot_cover_local_dependencies(self):
        self.use_source_only_record()
        graph=json.loads((self.root/'migration/modules.json').read_text())
        graph[-1]['imports'].append('proofs.Base');self.dump('migration/modules.json',graph)
        with self.assertRaises(AssertionError):validate_history(self.root,self.row)

    def test_source_only_history_rejects_incomplete_axiom_report(self):
        self.use_source_only_record();r=json.loads((self.root/'legacy.json').read_text())
        r['axiom_probe']['stdout']='';self.dump('legacy.json',r)
        self.record['source_only_receipts'][0]['receipt_sha256']=digest(self.root/'legacy.json')
        self.dump('history.json',self.record)
        with self.assertRaises(AssertionError):validate_history(self.root,self.row)

    def test_source_only_history_rejects_nonstandard_axiom(self):
        self.use_source_only_record();r=json.loads((self.root/'legacy.json').read_text())
        r['axiom_probe']['stdout']="'PhenotypeIdentification.sample' depends on axioms: [sorryAx]"
        self.dump('legacy.json',r);g=self.record['source_only_receipts'][0]
        g['receipt_sha256']=digest(self.root/'legacy.json');g['probed_axioms']={'PhenotypeIdentification.sample':['sorryAx']}
        self.dump('history.json',self.record)
        with self.assertRaises(AssertionError):validate_history(self.root,self.row)

if __name__=='__main__':unittest.main()
