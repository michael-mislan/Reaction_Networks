import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch00
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch01
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch02
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch03
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch04
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch05
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch06
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch07
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch08
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch09
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch10
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch11
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch12
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch13
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch14
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch15
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch16
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch17
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch18
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch19
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch20
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch21
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch22
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch23
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch24
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch25
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch26
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch27
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch28
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch29
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch30
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch31
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch32
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch33
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch34
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch35
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch36
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch37
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch38
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch39
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch40
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch41
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch42
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch43
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch44
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch45
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch46
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch47
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch48
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch49
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch50
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch51
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch52
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch53
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch54
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch55
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch56
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch57
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch58
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch59
import proofs.SmallCusp.Classification.SourceRecordKeyPairsBatch60
import proofs.SmallCusp.Classification.SourceCoverageSources

namespace SmallCusp

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem source_record_key_pairs_all :
    sourceCoverageRecords.map sourceRecordKeyPair = sourceRecordKeyPairs := by
  unfold sourceCoverageRecords sourceCoverageValidation00Records sourceRecordKeyPairs
  simp only [List.map_append,
    source_record_key_pairs_batch00,
    source_record_key_pairs_batch01,
    source_record_key_pairs_batch02,
    source_record_key_pairs_batch03,
    source_record_key_pairs_batch04,
    source_record_key_pairs_batch05,
    source_record_key_pairs_batch06,
    source_record_key_pairs_batch07,
    source_record_key_pairs_batch08,
    source_record_key_pairs_batch09,
    source_record_key_pairs_batch10,
    source_record_key_pairs_batch11,
    source_record_key_pairs_batch12,
    source_record_key_pairs_batch13,
    source_record_key_pairs_batch14,
    source_record_key_pairs_batch15,
    source_record_key_pairs_batch16,
    source_record_key_pairs_batch17,
    source_record_key_pairs_batch18,
    source_record_key_pairs_batch19,
    source_record_key_pairs_batch20,
    source_record_key_pairs_batch21,
    source_record_key_pairs_batch22,
    source_record_key_pairs_batch23,
    source_record_key_pairs_batch24,
    source_record_key_pairs_batch25,
    source_record_key_pairs_batch26,
    source_record_key_pairs_batch27,
    source_record_key_pairs_batch28,
    source_record_key_pairs_batch29,
    source_record_key_pairs_batch30,
    source_record_key_pairs_batch31,
    source_record_key_pairs_batch32,
    source_record_key_pairs_batch33,
    source_record_key_pairs_batch34,
    source_record_key_pairs_batch35,
    source_record_key_pairs_batch36,
    source_record_key_pairs_batch37,
    source_record_key_pairs_batch38,
    source_record_key_pairs_batch39,
    source_record_key_pairs_batch40,
    source_record_key_pairs_batch41,
    source_record_key_pairs_batch42,
    source_record_key_pairs_batch43,
    source_record_key_pairs_batch44,
    source_record_key_pairs_batch45,
    source_record_key_pairs_batch46,
    source_record_key_pairs_batch47,
    source_record_key_pairs_batch48,
    source_record_key_pairs_batch49,
    source_record_key_pairs_batch50,
    source_record_key_pairs_batch51,
    source_record_key_pairs_batch52,
    source_record_key_pairs_batch53,
    source_record_key_pairs_batch54,
    source_record_key_pairs_batch55,
    source_record_key_pairs_batch56,
    source_record_key_pairs_batch57,
    source_record_key_pairs_batch58,
    source_record_key_pairs_batch59,
    source_record_key_pairs_batch60]

end SmallCusp
