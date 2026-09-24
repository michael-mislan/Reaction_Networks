# Blank author fields

The catalogue's reading links use PDFs with blank author and affiliation fields.
Eight preserved manuscripts contained literal author placeholders, including
running headers in three papers. Twelve others had `Anonymous manuscript` in
their author slots; two of those also used that label in PDF author metadata.
Their reading copies are named `presentation.pdf`. The other forty reading
copies already had blank author slots and author metadata.

For the twenty affected papers, `paper.pdf` remains the exact original selected PDF.
The derived reading copy removes only the author/affiliation placeholder text
from title pages or running headers and clears the PDF author metadata. Dates,
titles, mathematical content, citations, page counts and page geometry are
preserved. Bibliography entries are source attributions, not author fields;
their text is unchanged. Manuscript source files also retain their original bytes.

[The presentation manifest](presentation-pdfs.json) records both file hashes,
the exact page rectangles changed, and validation results. All 413 pages in the
twenty derived PDFs were compared: extracted text outside the author slots was
identical, and rendered pixels outside those slots were identical at 72 dpi.
The edited title pages were also visually inspected. PyMuPDF 1.26.4 performed
text redactions and rendered the comparisons; pypdf 6.10.0 removed exact author
text operators where that preserved surrounding rendering more precisely.
Removed placeholders are absent from the reading copies'
searchable text rather than merely covered by white rectangles.

`scripts/check_integrity.py` verifies both source and presentation hashes.
`scripts/catalog.py` refuses to link a presentation copy if its hashes or
validation status no longer match. None of these edits changes any proof source,
declaration, build dependency or verification result.
