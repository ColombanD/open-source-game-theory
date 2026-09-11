---
name: latex-blocks-compact
description: "When handing Colomban LaTeX snippets, keep them compact — no unnecessary blank lines, very brief code examples"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: ff357ffe-cc0f-4a7a-bfc5-6078caad5838
  modified: 2026-09-04T08:26:56.507Z
---

When giving LaTeX blocks for the paper (2026-09-04): no blank lines inside the snippet unless a paragraph break is intended (blank lines are semantic in LaTeX), and keep embedded code examples very brief — one-line rule signatures with binder ceremony stripped, not verbatim multi-line constructors.

**Why:** they paste these blocks directly into the JMLR draft; stray blank lines create paragraph breaks, and long listings bloat the paper.

**How to apply:** compress Lean signatures to `| name : premise → side-condition → conclusion` on one or two lines; glosses as trailing clauses, not separate paragraphs. Related: [[jmlr-paper-decisions]].
