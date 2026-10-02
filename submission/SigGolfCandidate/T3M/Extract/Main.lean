import SigGolfCandidate.T3M.Extract.Full
import SigGolfCandidate.T3M.Extract.Header

/-! # Padded structural extraction (streams PEX-L / PEX-F): umbrella module

* `Basic`: `Pos`, `honestInput`, `HitIn`, honest objects, `ftsRoots` split.
* `Leaf`: tag-2 / tag-11 list parsing. `Layer`: `layerP_extract`, `layerP_shaped_core`.
* `Layers`: `layersP_walk`. `VerifyP`: `verifyP_extract_normal` (normal-form route, `FtsExtractSpecN`),
  `verifyP_extract` (stream-loop route, `FtsExtractSpec`), `keygen_pk`, `shaped_of_verifyP`.
* `Fts` (PEX-F): `FtsExtract.ftsExtractSpecN_holds`. `Full`: `verifyP_extract_full` (unconditional).
* `Header`: `Pos.hdr_injective`, `posOf`, `hitIn_posOf` (the hit position is a parse of the actual input). -/
