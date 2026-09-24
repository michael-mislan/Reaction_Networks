# Source and declaration audit

The supplied guide is preserved as GUIDE.md and has been read in full.
Energy PDF SHA256 matches the guide:
740c3833395479e312c266ff743bd6a555947308172e2e76805c6a4cb3a63fea.
The local joint manuscript publication/paper.pdf has SHA256
bd5ba3c9163451a3023dcc5beea5c63c285716ef89091bae75aa907dfc80dfc4,
different from the reviewed guide version. It is the 13-page 16 September paper
with full eight-coordinate Appendix A and source publication/paper.tex. Do not
claim hash identity with Medical_Shared_NADPH_Regeneration_Joint_Service.pdf.
Energy text and full local joint manuscript text were reviewed; energy equations
are rasterized, so their exact forms were checked against the textual supplement.

## Newly recovered Shimo source

Primary DOI: https://doi.org/10.1155/2011/398945
Full XML: https://www.ebi.ac.uk/europepmc/webservices/rest/PMC3184397/fullTextXML
Archive: https://www.ebi.ac.uk/europepmc/webservices/rest/PMC3184397/supplementaryFiles
Saved as sources/shimo.xml and sources/shimo_supplements.zip.
Browser PMC returned CAPTCHA; publisher returned 403. Public Europe PMC API
returned HTTP 200 for both full text and archive. No challenge bypass attempted.

The archive contains article images and four single-page figure PDFs only.
The caption promises kinetic equations and initial concentration tables, but
these are not present in the retrieved archive. Figure 1 was rendered and viewed.
This is a specific source-delivery gap, not evidence that the equations never existed.
Article Eq (1), preserved as MathML, does give the G6PD reaction law:

v = V (N/Kn)(S/Kg) /
    [1 + (N/Kn)(1+S/Kg) + H/Kh + A/Ka + B/Kb].

N=NADP, S=G6P, H=NADPH, A=ATP, B=2,3BPG. The six positive kinetic
parameters are V, Kn, Kg, Kh, Ka, Kb. No factor of two applies to this reaction:
the second oxidative PPP dehydrogenase is a separate source obligation.
The paper's parameter tables label V in M/s; that surprising scale is retained
as an unresolved unit issue, not silently converted. Reported recovery times are
simulation results. Correlations between patient kinetic constants are explicitly
acknowledged; their independent box of virtual patients can include unrealizable
combinations. We will not treat that box as a measured population distribution.

## Existing declarations to reuse

- StoredRedCells.S7Certificate.source_joint_inventory_bound: full matrix bound.
- StoredRedCells.PairedRecovery.paired_integrated_identity: common-input signal.
- CommonEnvironmentProtection.jointProtection_iff_minimumRegeneration: maintained
  steady state, not transient or erythrocyte result.
- CommonEnvironmentProtection.Allocation.allocation_attained: designed enzyme
  reallocation, not an intracellular control to assume in the current problem.

Their existence and stated scopes are inspected; this campaign has not rebuilt
the unchanged full source modules. No inherited compilation is represented as new.

## Newly recovered alternative source
Nishino2013 model .s007 and supplements .s008/.s009 recovered from PLOS. See NISHINO_SOURCE_AUDIT.md for hashes, source-format caveats, exact pool checks and absence of a peroxide state. This is not Shimo2011 reconstruction.
