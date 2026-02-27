# USLLN Proof Dependency Graph

## Mermaid (for GitHub / Markdown rendering)

```mermaid
graph TD
    classDef proved fill:#4CAF50,stroke:#333,color:white
    classDef sorry fill:#F44336,stroke:#333,color:white
    classDef mathlib fill:#2196F3,stroke:#333,color:white
    classDef defn fill:#9E9E9E,stroke:#333,color:white

    SLLN_ML["strong_law_ae_real<br/>(Mathlib)"]:::mathlib
    CDT["continuous_of_dominated<br/>(Mathlib)"]:::mathlib
    ABI["ae_ball_iff<br/>(Mathlib)"]:::mathlib

    SA["sampleAvg<br/>(definition)"]:::defn
    PM["popMean<br/>(definition)"]:::defn

    IUC["integrable_U_comp_X<br/>✅ proved"]:::proved
    SAC["sampleAvg_continuous<br/>✅ proved"]:::proved
    SP["slln_pointwise<br/>✅ proved"]:::proved
    SFA["slln_finset_ae<br/>✅ proved"]:::proved
    PMC["popMean_continuous<br/>✅ proved"]:::proved
    US["uniform_slln<br/>❌ sorry"]:::sorry

    SLLN_ML --> IUC
    IUC --> SP
    SP --> SFA
    ABI --> SFA
    CDT --> PMC

    SA --> SP
    PM --> SP
    SA --> SAC

    SP --> US
    SFA --> US
    SAC --> US
    PMC --> US
```

## ASCII (for terminal / comments)

```
Layer 0 (Mathlib):
  [strong_law_ae_real]  [continuous_of_dominated]  [ae_ball_iff]
         |                       |                      |
Layer 1 (Definitions):
  [sampleAvg]  [popMean]
         |          |
Layer 2 (Integrability):
  [integrable_U_comp_X] ✅
         |
Layer 3 (Pointwise SLLN):
  [slln_pointwise] ✅
         |
Layer 4 (Helpers):
  [slln_finset_ae] ✅    [sampleAvg_continuous] ✅    [popMean_continuous] ✅
         \                       |                      /
          \                      |                     /
Layer 5 (Main Theorem):
                      [uniform_slln] ❌
```

## DOT (for graphviz rendering)

```dot
digraph USLLN {
  rankdir=TB;
  node [shape=box, style=filled, fontname="Helvetica"];

  // Mathlib
  strong_law_ae_real [label="strong_law_ae_real\n(Mathlib)", fillcolor="#2196F3", fontcolor=white];
  continuous_of_dominated [label="continuous_of_dominated\n(Mathlib)", fillcolor="#2196F3", fontcolor=white];
  ae_ball_iff [label="ae_ball_iff\n(Mathlib)", fillcolor="#2196F3", fontcolor=white];

  // Definitions
  sampleAvg [label="sampleAvg\n(def)", fillcolor="#9E9E9E"];
  popMean [label="popMean\n(def)", fillcolor="#9E9E9E"];

  // Proved
  integrable_U_comp_X [label="integrable_U_comp_X\n✅ proved", fillcolor="#4CAF50", fontcolor=white];
  sampleAvg_continuous [label="sampleAvg_continuous\n✅ proved", fillcolor="#4CAF50", fontcolor=white];
  slln_pointwise [label="slln_pointwise\n✅ proved", fillcolor="#4CAF50", fontcolor=white];
  slln_finset_ae [label="slln_finset_ae\n✅ proved", fillcolor="#4CAF50", fontcolor=white];
  popMean_continuous [label="popMean_continuous\n✅ proved", fillcolor="#4CAF50", fontcolor=white];

  // Sorry
  uniform_slln [label="uniform_slln\n❌ sorry", fillcolor="#F44336", fontcolor=white];

  // Edges
  strong_law_ae_real -> integrable_U_comp_X;
  integrable_U_comp_X -> slln_pointwise;
  sampleAvg -> slln_pointwise;
  popMean -> slln_pointwise;
  slln_pointwise -> slln_finset_ae;
  ae_ball_iff -> slln_finset_ae;
  continuous_of_dominated -> popMean_continuous;
  sampleAvg -> sampleAvg_continuous;

  slln_pointwise -> uniform_slln;
  slln_finset_ae -> uniform_slln;
  sampleAvg_continuous -> uniform_slln;
  popMean_continuous -> uniform_slln;
}
```

## Statlib Eligibility

| Declaration | Sorry | Dependencies with sorry | Eligible for Verified? |
|-------------|-------|------------------------|----------------------|
| `sampleAvg` (def) | 0 | none | ✅ |
| `popMean` (def) | 0 | none | ✅ |
| `integrable_U_comp_X` | 0 | none | ✅ |
| `sampleAvg_continuous` | 0 | none | ✅ |
| `slln_pointwise` | 0 | none | ✅ |
| `slln_finset_ae` | 0 | `slln_pointwise` (clean) | ✅ |
| `popMean_continuous` | 0 | none | ✅ |
| `uniform_slln` | 1 | self | ❌ |

**Result: 7/8 declarations eligible for Verified library (all helpers proved).**
